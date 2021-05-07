mod parser;

use std::{
    collections::HashMap,
    iter::{once, repeat},
    path::PathBuf,
};

use anyhow::Context;
use itertools::{iproduct, Either};
use sat_encoder::{Model, constraints::{And, AtMostK, AtleastK, ExactlyK, Expr, If, Not, Or}, prelude::*};
use structopt::StructOpt;
use strum::IntoEnumIterator;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, strum::EnumIter, PartialOrd, Ord)]
enum Color {
    Green,
    Red,
    Blue,
    Yellow,
}

impl Color {
    fn ascii_color_code(&self) -> &'static str {
        match self {
            Color::Red => "\u{1b}[31m",
            Color::Green => "\u{1b}[32m",
            Color::Yellow => "\u{1b}[33m",
            Color::Blue => "\u{1b}[34m",
        }
    }
}

fn valid_num(i: impl Into<Option<usize>>) -> bool {
    matches!(i.into(), Some(i) if i >= 1 && i <= 13)
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
struct NumberBlock {
    // Block with sequentially growing numbers.
    color: Color,
    instance: u32,
    is_joker: bool,

    index: usize, // 1..=13
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
struct ColorBlock {
    // Block with number and different colors.
    number: usize, // 1..=13
    instance: u32,
    is_joker: bool,

    color: Color,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
enum Card {
    Normal {
        color: Color,
        number: usize, // 1..=13
    },
    Joker,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, derive_more::From, PartialOrd, Ord)]
enum Var {
    Num(NumberBlock),
    Color(ColorBlock),
}

fn encode_number_block_rules(encoder: &mut DefaultEncoder<Var>, color: Color, instance: u32) {
    // Stores reprs of if a certain space is occupied (either by number card or joker)
    let mut reprs = Vec::new();

    // The same space cannot be occupied by its number card *and* joker
    for index in 1..=13 {
        let lits = [true, false].iter().map(|&joker| Pos(Var::Num(NumberBlock {
            color,
            instance,
            is_joker: joker,
            index,
        })));

        encoder.add_constraint(Not(And(lits.clone())));

        reprs.push(encoder.add_constraint_equals_repr(Or(lits)));
    }

    // Using the reprs we now ensure that cards form atleast 3 large blocks of cards.
    for i in 1usize..=13 {
        let i_pre1 = i.checked_sub(1);
        let i_pre2 = i.checked_sub(2);

        let i_post1 = i.checked_add(1);
        let i_post2 = i.checked_add(2);

        let mut e = None;

        match (i_pre1, i_pre2) {
            (Some(i1), Some(i2)) if valid_num(i1) && valid_num(i2) => {
                let i1 = reprs[i1 - 1];
                let i2 = reprs[i2 - 1];
                let x = Expr::from(i1) & i2;
                e = Some(x);
            }
            _ => {}
        }

        match (i_pre1, i_post1) {
            (Some(i1), Some(i2)) if valid_num(i1) && valid_num(i2) => {
                let i1 = reprs[i1 - 1];
                let i2 = reprs[i2 - 1];
                let x = Expr::from(i1) & i2;
                e = Some(e.map_or(x.clone(), |e| e | x));
            }
            _ => {}
        }

        match (i_post1, i_post2) {
            (Some(i1), Some(i2)) if valid_num(i1) && valid_num(i2) => {
                let i1 = reprs[i1 - 1];
                let i2 = reprs[i2 - 1];
                let x = Expr::from(i1) & i2;
                e = Some(e.map_or(x.clone(), |e| e | x));
            }
            _ => {}
        }

        let e = e.unwrap();
        let cond = If {
            cond: reprs[i - 1],
            then: e,
        };
        encoder.add_constraint(cond);
    }
}

fn encode_color_block_rules(encoder: &mut DefaultEncoder<Var>, number: usize, instance: u32) {
    let mut reprs = Vec::new();

    for color in Color::iter() {
        let lits = [false, true].iter().map(|&joker| {
            Pos(Var::Color(ColorBlock {
                number,
                instance,
                is_joker: joker,
                color,
            }))
        });

        encoder.add_constraint(Not(And(lits.clone())));

        let constraint = Or(lits);

        reprs.push(encoder.add_constraint_equals_repr(constraint));
    }

    let empty_cond = AtMostK {
        k: 0,
        lits: reprs.clone().into_iter(),
    };
    let filled_cond = AtleastK {
        k: 3,
        lits: reprs.clone().into_iter(),
    };
    encoder.add_constraint(Expr::from_constraint(empty_cond) | Expr::from_constraint(filled_cond));
}

fn encode_general_rules(solver: &mut DefaultEncoder<Var>) {
    for (color, instance) in iproduct!(Color::iter(), 0..=1) {
        encode_number_block_rules(solver, color, instance);
    }

    for (number, instance) in iproduct!(1..=13, 0..=1) {
        encode_color_block_rules(solver, number, instance);
    }
}

fn encode_config(encoder: &mut DefaultEncoder<Var>, config: Config) {
    for (card, count) in config.cards.into_iter() {
        let lits = match card {
            Card::Normal { color, number } => {
                let left = (0..=1)
                    .map(move |inst| {
                        Var::Num(NumberBlock {
                            color,
                            instance: inst,
                            is_joker: false,
                            index: number,
                        })
                    })
                    .chain((0..=1).map(move |inst| {
                        Var::Color(ColorBlock {
                            number,
                            instance: inst,
                            is_joker: false,
                            color,
                        })
                    }))
                    .map(|v| Pos(v));
                Either::Left(left)
            }
            Card::Joker => {
                let right = iproduct!(0..=1, Color::iter(), 1..=13)
                    .map(|(instance, color, number)| {
                        Var::Color(ColorBlock {
                            number,
                            instance,
                            is_joker: true,
                            color,
                        })
                    })
                    .chain(iproduct!(0..=1, Color::iter(), 1..=13).map(
                        |(instance, color, index)| {
                            Var::Num(NumberBlock {
                                index,
                                instance,
                                is_joker: true,
                                color,
                            })
                        },
                    ))
                    .map(|v| Pos(v));
                Either::Right(right)
            }
        };

        encoder.add_constraint(ExactlyK { k: count, lits });
    }
}

#[derive(Debug)]
pub struct Config {
    cards: HashMap<Card, u32>,
}

impl Default for Config {
    fn default() -> Self {
        let config = iproduct!(1..=13, Color::iter())
            .map(|(number, color)| Card::Normal { color, number })
            .chain(once(Card::Joker))
            .zip(repeat(0))
            .collect();
        Self { cards: config }
    }
}

fn pretty_print_solution(model: &Model<Var>) {
    const END_COLOR: &str = "\u{1b}[0m";

    // number blocks
    for (color, instance) in iproduct!(Color::iter(), 0..=1) {
        let iter = (1..=13)
            .flat_map(|index| {
                [false, true].iter().map(move |&joker| {
                    Pos(Var::Num(NumberBlock {
                        color,
                        instance,
                        is_joker: joker,
                        index,
                    }))
                })
            })
            .map(|lit| (lit, model.lit(lit).unwrap_or(false)));

        if iter.clone().all(|(_, b)| !b) {
            continue;
        }

        for (card, b) in iter {
            let card: Var = card.unwrap();
            let card = match card {
                Var::Num(num) => num,
                Var::Color(_) => {
                    unreachable!()
                }
            };

            if b {
                if card.is_joker {
                    print!("{} X{}", card.color.ascii_color_code(), END_COLOR);
                } else {
                    print!(
                        "{}{:>2}{}",
                        card.color.ascii_color_code(),
                        card.index,
                        END_COLOR
                    );
                }
            } else {
                print!("  ");
            }
        }
        println!()
    }

    // color blocks
    for (number, instance) in iproduct!(1..=13, 0..=1) {
        let iter = Color::iter()
            .flat_map(|color| {
                [false, true].iter().map(move |&joker| {
                    Pos(Var::Color(ColorBlock {
                        color,
                        instance,
                        is_joker: joker,
                        number,
                    }))
                })
            })
            .map(|lit| (lit, model.lit(lit).unwrap()));

        if iter.clone().all(|(_, b)| !b) {
            continue;
        }

        for (card, b) in iter {
            let card: Var = card.unwrap();

            let card = match card {
                Var::Num(_) => {
                    unreachable!()
                }
                Var::Color(color) => color,
            };

            if b {
                if card.is_joker {
                    print!("{} X{}", card.color.ascii_color_code(), END_COLOR);
                } else {
                    print!(
                        "{}{:>2}{}",
                        card.color.ascii_color_code(),
                        card.number,
                        END_COLOR
                    );
                }
            } else {
                print!("  ");
            }
        }
        println!()
    }
}

#[derive(structopt::StructOpt)]
struct Options {
    path: PathBuf,
}

#[rustfmt::skip]
fn main() -> anyhow::Result<()> {
    let options = Options::from_args();

    let mut encoder = DefaultEncoder::with_debug();

    encode_general_rules(&mut encoder);

    let config = std::fs::read_to_string(options.path)
        .context("Reading input file failed.")?;
    let config = parser::parse_config(&config)
        .context("Parsing input failed.")?;

    encode_config(&mut encoder, config);
    
    dbg!(&encoder.varmap);

    encoder
        .solver
        .write_dimacs(&std::path::PathBuf::from("clauses.dimacs"))
        .unwrap();

    if let Some(model) = encoder.solve() {
        //println!("{:?}", model.all_vars().collect::<Vec<_>>());
        pretty_print_solution(&model);
    } else {
        println!("No solution found!");
    }

    Ok(())
}
