mod parser;

use std::{
    collections::HashMap,
    iter::{once, repeat},
    path::PathBuf,
};

use anyhow::Context;
use itertools::{iproduct, Itertools};
use sat_encoder::{
    constraints::{
        And, AtMostK, AtleastK, ExactlyK, Expr, If, Not, Or, SameCardinality,
    },
    prelude::*,
    Model,
};
use structopt::StructOpt;
use strum::IntoEnumIterator;

#[derive(
    Debug, PartialEq, Eq, Hash, Clone, Copy, strum::EnumIter, PartialOrd, Ord,
)]
enum Color {
    Green,
    Red,
    Blue,
    Yellow,
}

impl Color {
    const END_COLOR: &'static str = "\u{1b}[0m";

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

#[derive(
    Debug, PartialEq, Eq, Hash, Clone, Copy, derive_more::From, PartialOrd, Ord,
)]
enum Var {
    Chosen(Card, u32),
    Num(NumberBlock),
    Color(ColorBlock),
}

fn encode_number_block_rules(
    encoder: &mut DefaultEncoder<Var>,
    color: Color,
    instance: u32,
) {
    // Stores reprs of if a certain space is occupied (either by number card or joker)
    let mut reprs = Vec::new();

    // The same space cannot be occupied by its number card *and* joker
    for index in 1..=13 {
        let lits = [true, false].iter().map(|&joker| {
            Pos(Var::Num(NumberBlock {
                color,
                instance,
                is_joker: joker,
                index,
            }))
        });

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

fn encode_color_block_rules(
    encoder: &mut DefaultEncoder<Var>,
    number: usize,
    instance: u32,
) {
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
    encoder.add_constraint(
        Expr::from_constraint(empty_cond) | Expr::from_constraint(filled_cond),
    );
}

fn encode_general_rules(solver: &mut DefaultEncoder<Var>) {
    for (color, instance) in iproduct!(Color::iter(), 0..=1) {
        encode_number_block_rules(solver, color, instance);
    }

    for (number, instance) in iproduct!(1..=13, 0..=1) {
        encode_color_block_rules(solver, number, instance);
    }
}

fn encode_config(encoder: &mut DefaultEncoder<Var>, config: &Config, atleast: u32) {
    let mut all_choosable = Vec::new();

    for (color, number) in iproduct!(Color::iter(), 1..=13) {
        let lits = (0..=1)
            .map(|instance| {
                Pos(Var::Color(ColorBlock {
                    number,
                    instance,
                    is_joker: false,
                    color,
                }))
            })
            .chain((0..=1).map(|instance| {
                Pos(Var::Num(NumberBlock {
                    color,
                    instance,
                    is_joker: false,
                    index: number,
                }))
            }));

        match config.cards.get(&Card::Normal { color, number }) {
            Some(&count) if count > 0 => {
                let choosable = (0..count)
                    .map(|i| Pos(Var::Chosen(Card::Normal { color, number }, i)));

                all_choosable.extend(choosable.clone());

                encoder.add_constraint({
                    let mut same_cardinality_constraint = SameCardinality::new();
                    same_cardinality_constraint
                        .add_lits(choosable)
                        .add_lits(lits);
                    same_cardinality_constraint
                });
            }
            _ => {
                // If card doesn't appear in config it cannot be chosen and
                // therefore not used.
                encoder.add_constraint(ExactlyK { k: 0, lits });
            }
        }
    }

    let joker_lits = iproduct!(Color::iter(), 1..=13, 0..=1)
        .map(|(color, number, instance)| {
            Pos(Var::Color(ColorBlock {
                number,
                instance,
                is_joker: true,
                color,
            }))
        })
        .chain(iproduct!(Color::iter(), 1..=13, 0..=1).map(
            |(color, index, instance)| {
                Pos(Var::Num(NumberBlock {
                    index,
                    instance,
                    is_joker: true,
                    color,
                }))
            },
        ));

    match config.cards.get(&Card::Joker) {
        Some(&count) if count > 0 => {
            let choosable = (0..count).map(|i| Pos(Var::Chosen(Card::Joker, i)));

            all_choosable.extend(choosable.clone());

            encoder.add_constraint({
                let mut same_cardinality_constraint = SameCardinality::new();
                same_cardinality_constraint
                    .add_lits(choosable)
                    .add_lits(joker_lits);
                same_cardinality_constraint
            });
        }
        _ => {
            // If card doesn't appear in config it cannot be chosen and
            // therefore not used.
            encoder.add_constraint(ExactlyK {
                k: 0,
                lits: joker_lits,
            });
        }
    }

    for c in &all_choosable {
        match c.var() {
            Var::Chosen(card, i) if *i > 0 => encoder.add_constraint(If {
                cond: *c,
                then: Pos(Var::Chosen(*card, i - 1)),
            }),
            _ => {}
        }
    }

    encoder.add_constraint(AtleastK {
        k: atleast,
        lits: all_choosable.into_iter(),
    });
}

#[derive(Debug)]
pub struct Config {
    cards: HashMap<Card, u32>,
}

impl Config {
    fn total(&self) -> u32 {
        self.cards.values().sum()
    }
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

fn pretty_print_config(config: &Config) {
    for color in Color::iter() {
        let mut nums = config
            .cards
            .iter()
            .filter_map(|(card, count)| match card {
                Card::Normal { color: c, number } if color == *c => {
                    Some(vec![number; *count as usize])
                }
                _ => None,
            })
            .flatten()
            .collect::<Vec<_>>();
        nums.sort();

        let s = nums.into_iter().map(|i| i.to_string()).join(" ");

        println!("{}{}{}", color.ascii_color_code(), s, Color::END_COLOR);
    }

    if let Some(joker_count) = config.cards.get(&Card::Joker) {
        println!("{}", "X".repeat(*joker_count as usize));
    }
}

fn pretty_print_solution(model: &Model<Var>) {
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
                Var::Chosen(..) => continue,
            };

            if b {
                if card.is_joker {
                    print!(
                        "{} X{}",
                        card.color.ascii_color_code(),
                        Color::END_COLOR
                    );
                } else {
                    print!(
                        "{}{:>2}{}",
                        card.color.ascii_color_code(),
                        card.index,
                        Color::END_COLOR
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
                Var::Chosen(..) => continue,
            };

            if b {
                if card.is_joker {
                    print!(
                        "{} X{}",
                        card.color.ascii_color_code(),
                        Color::END_COLOR
                    );
                } else {
                    print!(
                        "{}{:>2}{}",
                        card.color.ascii_color_code(),
                        card.number,
                        Color::END_COLOR
                    );
                }
            } else {
                print!("  ");
            }
        }
        println!()
    }
}

fn count_cards_in_solution(model: &Model<Var>) -> usize {
    model
        .vars()
        .filter(|v| matches!(v, Pos(Var::Chosen(..))))
        .count()
}

fn try_solve(
    config: &Config,
    atleast: u32,
) -> Option<(Model<Var>, DefaultEncoder<Var>)> {
    let mut encoder = DefaultEncoder::new();

    encode_general_rules(&mut encoder);
    encode_config(&mut encoder, config, atleast);

    let model = encoder.solve();
    model.map(|m| (m, encoder))
}

#[derive(structopt::StructOpt)]
struct Options {
    path: PathBuf,
}

#[rustfmt::skip]
fn main() -> anyhow::Result<()> {
    let options = Options::from_args();

    let config = std::fs::read_to_string(options.path)
        .context("Reading input file failed.")?;
    let config = parser::parse_config(&config)
        .context("Parsing input failed.")?;

    pretty_print_config(&config);

    let total = config.total();

    let mut min_encoded = 0;
    let mut min = 0;
    let mut max = total + 1;

    let mut best_model = None;
    let mut best = 0;

    loop {
        let val = (min + max) / 2;

        if val == min || val == max {
            break;
        }

        println!("Try atleast {}", val);
        if let Some(model) = try_solve(&config, val) {
            let cards = count_cards_in_solution(&model.0) as u32;

            println!("Possible solution! ({})", cards);

            min_encoded = val;
            min = cards;
            if val > best {
                best = cards;
                best_model = Some(model);
            }
        } else {
            println!("Impossible!");
            max = val;
        }
    }

    if let Some((mut model, mut encoder)) = best_model {
        pretty_print_solution(&model);

        // Required so that the search for alternative solutions has the same number 
        // of cards.
        if min_encoded < min {
            let lits = model.vars().filter(|v| matches!(v.var(), Var::Chosen(..)))
                .map(|v| Pos(*v.var()));
            encoder.add_constraint(AtleastK { k: min, lits: lits.into_iter()});
        }

        loop {
            encoder.add_constraint(Or(model.vars().filter(|v| matches!(v.var(), Var::Chosen(..))).map(|v| !v)));
            if let Some(new_model) = encoder.solve() {
                println!("Alternative Model:");
                pretty_print_solution(&new_model);
                model = new_model;
            } else {
                break;
            }
        }
    } else {
       println!("No solution found!");
    }

    Ok(())
}
