mod sat;
mod parser;

use std::{collections::{HashMap, HashSet}, iter::{once, repeat}, path::PathBuf};

use itertools::iproduct;
use sat::{prelude::*, AtMostK, AtleastK, Expr, If};
use strum::IntoEnumIterator;
use structopt::StructOpt;
use anyhow::Context;

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
    let i = i.into();
    match i {
        Some(i) if i >= 1 && i <= 13 => true,
        _ => false,
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
struct NumberBlock {
    // Block with sequentially growing numbers.
    color: Color,
    instance: u32,

    index: usize, // 1..=13
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
struct ColorBlock {
    // Block with number and different colors.
    number: usize, // 1..=13
    instance: u32,

    color: Color,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
struct Card {
    color: Color,
    number: usize, // 1..=13
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, derive_more::From, PartialOrd, Ord)]
enum Var {
    Num(NumberBlock),
    Color(ColorBlock),
}

fn encode_number_block_rules(solver: &mut impl Encoder<Var>, color: Color, instance: u32) {
    let num_block = |index| {
        Var::Num(NumberBlock {
            color,
            instance,
            index,
        })
    };

    for i in 1usize..=13 {
        let i_pre1 = i.checked_sub(1);
        let i_pre2 = i.checked_sub(2);

        let i_post1 = i.checked_add(1);
        let i_post2 = i.checked_add(2);

        let mut e = None;

        match (i_pre1, i_pre2) {
            (Some(i1), Some(i2)) if valid_num(i1) && valid_num(i2) => {
                let i1 = Pos(num_block(i1));
                let i2 = Pos(num_block(i2));
                let x = Expr::from(i1) & i2;
                e = Some(x);
            }
            _ => {}
        }

        match (i_pre1, i_post1) {
            (Some(i1), Some(i2)) if valid_num(i1) && valid_num(i2) => {
                let i1 = Pos(num_block(i1));
                let i2 = Pos(num_block(i2));
                let x = Expr::from(i1) & i2;
                e = Some(e.map_or(x.clone(), |e| e | x));
            }
            _ => {}
        }

        match (i_post1, i_post2) {
            (Some(i1), Some(i2)) if valid_num(i1) && valid_num(i2) => {
                let i1 = Pos(num_block(i1));
                let i2 = Pos(num_block(i2));
                let x = Expr::from(i1) & i2;
                e = Some(e.map_or(x.clone(), |e| e | x));
            }
            _ => {}
        }

        let e = e.unwrap();
        let cond = If {
            cond: once(Pos(num_block(i))),
            then: e,
        };
        solver.add_constraint(cond);
    }
}

fn encode_color_block_rules(solver: &mut impl Encoder<Var>, number: usize, instance: u32) {
    let lits = Color::iter().map(move |color| {
        Pos(Var::Color(ColorBlock {
            number,
            instance,
            color,
        }))
    });

    let mut it = lits.clone().map(|l| -l);

    let mut empty_cond = Expr::from(it.next().unwrap());

    for lit in it {
        empty_cond = empty_cond & lit;
    }

    let filled_cond = AtleastK { k: 3, lits };
    solver.add_constraint(Expr::from_constraint(empty_cond) | Expr::from_constraint(filled_cond));
}

fn encode_general_rules(solver: &mut impl Encoder<Var>) {
    for (color, instance) in iproduct!(Color::iter(), 0..=1) {
        encode_number_block_rules(solver, color, instance);
    }

    for (number, instance) in iproduct!(1..=13, 0..=1) {
        encode_color_block_rules(solver, number, instance);
    }
}

fn encode_config(solver: &mut impl Encoder<Var>, config: Config) {
    for (card, count) in config.cards.into_iter() {
        let lits = (0..=1)
            .map(|inst| {
                Var::Num(NumberBlock {
                    color: card.color,
                    instance: inst,
                    index: card.number,
                })
            })
            .chain((0..=1).map(|inst| {
                Var::Color(ColorBlock {
                    number: card.number,
                    instance: inst,
                    color: card.color,
                })
            }))
            .map(|v| Pos(v));

        if count > 0 {
            solver.add_constraint(AtleastK {
                k: count,
                lits: lits.clone(),
            });
        }
        solver.add_constraint(AtMostK { k: count, lits });
    }
}

#[derive(Debug)]
pub struct Config {
    cards: HashMap<Card, u32>,
}

impl Default for Config {
    fn default() -> Self {
        let config = iproduct!(1..=13, Color::iter())
            .map(|(number, color)| Card { color, number })
            .zip(repeat(0))
            .collect();
        Self { cards: config }
    }
}

fn pretty_print_solution(model: &HashSet<Lit<Var>>) {
    const END_COLOR: &str = "\u{1b}[0m";

    // number blocks
    for (color, instance) in iproduct!(Color::iter(), 0..=1) {
        let iter = (1..=13)
            .map(|index| {
                Pos(Var::Num(NumberBlock {
                    color,
                    instance,
                    index,
                }))
            })
            .map(|lit| model.contains(&lit));

        if iter.clone().all(|b| !b) {
            continue;
        }

        for (b, i) in iter.zip(1..) {
            if b {
                print!("{}{:>2}{}", color.ascii_color_code(), i, END_COLOR);
            } else {
                print!("  ");
            }
        }
        println!()
    }

    // color blocks
    for (number, instance) in iproduct!(1..=13, 0..=1) {
        let iter = Color::iter()
            .map(|color| {
                (Pos(Var::Color(ColorBlock {
                    color,
                    instance,
                    number,
                })), color)
            })
            .map(|(lit, color)| (model.contains(&lit), color));

        if iter.clone().all(|(b, _)| !b) {
            continue;
        }

        for (b, color) in iter {
            if b {
                print!("{}{:>2}{}", color.ascii_color_code(), number, END_COLOR);
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

    let mut solver = Solver::new();
    //let mut solver = sat::DebugSolver::new();

    encode_general_rules(&mut solver);

    let config = std::fs::read_to_string(options.path)
        .context("Reading input file failed.")?;
    let config = parser::parse_config(&config)
        .context("Parsing input failed.")?;

    encode_config(&mut solver, config);

    solver
        .internal
        .write_dimacs(&std::path::PathBuf::from("clauses.dimacs"))
        .unwrap();

    if let Some(model) = solver.solve() {
        pretty_print_solution(&model);
    } else {
        println!("No solution found!");
    }

    Ok(())
}
