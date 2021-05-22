mod parser;

use std::{collections::HashMap, iter, path::PathBuf};

use anyhow::Context;
use colored::Colorize;
use itertools::{Either, Itertools, iproduct};
use sat_encoder::{CadicalEncoder, Encoder, Lit, Model, Solver, constraints::{
        And, AtMostK, AtLeastK, ExactlyK, Expr, If, Not, Or, SameCardinality,
    }};
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
    fn to_color(&self) -> colored::Color {
        match self {
            Color::Red => colored::Color::Red,
            Color::Green => colored::Color::Green,
            Color::Yellow => colored::Color::Yellow,
            Color::Blue => colored::Color::Blue,
        }
    }

    fn to_bright_color(&self) -> colored::Color {
        match self {
            Color::Red => colored::Color::TrueColor {
                r: 255,
                g: 150,
                b: 150,
            },
            Color::Green => colored::Color::TrueColor {
                r: 150,
                g: 255,
                b: 150,
            },
            Color::Yellow => colored::Color::TrueColor {
                r: 255,
                g: 255,
                b: 150,
            },
            Color::Blue => colored::Color::TrueColor {
                r: 150,
                g: 150,
                b: 255,
            },
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
    #[from(ignore)]
    Required(Card, u32),

    #[from(ignore)]
    Optional(Card, u32),

    Num(NumberBlock),

    Color(ColorBlock),
}

fn encode_number_block_rules(
    encoder: &mut Encoder<Var, impl Solver>,
    color: Color,
    instance: u32,
) {
    // Stores reprs of if a certain space is occupied (either by number card or joker)
    let mut reprs = Vec::new();

    // The same space cannot be occupied by its number card *and* joker
    for index in 1..=13 {
        let lits = [true, false].iter().map(|&joker| {
            Var::Num(NumberBlock {
                color,
                instance,
                is_joker: joker,
                index,
            })
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
    encoder: &mut Encoder<Var, impl Solver>,
    number: usize,
    instance: u32,
) {
    let mut reprs = Vec::new();

    for color in Color::iter() {
        let lits = [false, true].iter().map(|&joker| {
            Var::Color(ColorBlock {
                number,
                instance,
                is_joker: joker,
                color,
            })
        });

        encoder.add_constraint(Not(And(lits.clone())));

        let constraint = Or(lits);

        reprs.push(encoder.add_constraint_equals_repr(constraint));
    }

    let empty_cond = AtMostK {
        k: 0,
        lits: reprs.clone().into_iter(),
    };
    let filled_cond = AtLeastK {
        k: 3,
        lits: reprs.clone().into_iter(),
    };
    encoder.add_constraint(
        Expr::from_constraint(empty_cond) | Expr::from_constraint(filled_cond),
    );
}

fn encode_general_rules(solver: &mut Encoder<Var, impl Solver>) {
    for (color, instance) in iproduct!(Color::iter(), 0..=1) {
        encode_number_block_rules(solver, color, instance);
    }

    for (number, instance) in iproduct!(1..=13, 0..=1) {
        encode_color_block_rules(solver, number, instance);
    }
}

fn encode_config(
    encoder: &mut Encoder<Var, impl Solver>,
    config: &Config,
    atleast: u32, // how many optional cards should be used atleast.
    with_joker: bool,
) {
    for (color, number) in iproduct!(Color::iter(), 1..=13) {
        let lits = (0..=1)
            .map(|instance| {
                Var::Color(ColorBlock {
                    number,
                    instance,
                    is_joker: false,
                    color,
                })
            })
            .chain((0..=1).map(|instance| {
                Var::Num(NumberBlock {
                    color,
                    instance,
                    is_joker: false,
                    index: number,
                })
            }));

        match config.cards.get(&Card::Normal { color, number }) {
            Some(&count) if count.total() > 0 => {
                let choosable = (0..count.required)
                    .map(|i| Var::Required(Card::Normal { color, number }, i))
                    .chain((0..count.optional).map(|i| {
                        Var::Optional(Card::Normal { color, number }, i)
                    }));

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
            Var::Color(ColorBlock {
                number,
                instance,
                is_joker: true,
                color,
            })
        })
        .chain(iproduct!(Color::iter(), 1..=13, 0..=1).map(
            |(color, index, instance)| {
                Var::Num(NumberBlock {
                    index,
                    instance,
                    is_joker: true,
                    color,
                })
            },
        ));

    match config.cards.get(&Card::Joker) {
        Some(&count) if count.required > 0 => {
            let choosable_required =
                (0..count.required).map(|i| Var::Required(Card::Joker, i));

            let choosable_optional =
                (0..count.optional).map(|i| Var::Optional(Card::Joker, i));

            let choosable = if with_joker && count.optional > 0 {
                Either::Left(choosable_required.chain(choosable_optional))
            } else {
                Either::Right(choosable_required)
            };

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

    // Ensure that smaller cards are chosen first so that returned solutions are unique.
    for (&card, amount) in config.cards.iter() {
        if amount.required > 0 {
            for i in 1..amount.required {
                encoder.add_constraint(If {
                    cond: Var::Required(card, i),
                    then: Var::Required(card, i - 1),
                });
            }
        }

        if amount.optional > 0 {
            for i in 1..amount.optional {
                encoder.add_constraint(If {
                    cond: Var::Optional(card, i),
                    then: Var::Optional(card, i - 1),
                });
            }
        }
    }

    // Ensure that all required cards are used.
    for (&card, amount) in config
        .cards
        .iter()
        .filter(|(_, amount)| amount.required > 0)
        .map(|(c, amount)| (c, amount.required))
    {
        for i in 0..amount {
            encoder.add_constraint(Var::Required(card, i));
        }
    }

    // Ensure that the minimum number of optional cards are used
    let lits = config.cards.iter().flat_map(|(&c, amount)| {
        (0..amount.optional).map(move |i| Var::Optional(c, i))
    });
    encoder.add_constraint(AtLeastK { k: atleast, lits });
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, Default)]
struct Amount {
    required: u32,
    optional: u32,
}

impl Amount {
    fn total(&self) -> u32 {
        self.required + self.optional
    }
}

#[derive(Debug, Default)]
pub struct Config {
    cards: HashMap<Card, Amount>,
}

impl Config {
    fn total_optional_cards(&self) -> u32 {
        self.cards.values().map(|amount| amount.optional).sum()
    }
}

fn pretty_print_config(config: &Config) {
    for color in Color::iter() {
        let mut nums = config
            .cards
            .iter()
            .filter_map(|(card, count)| match card {
                Card::Normal { color: c, number } if color == *c => {
                    let required = vec![(number, true); count.required as usize];
                    let optional = vec![(number, false); count.optional as usize];

                    let mut cards = required;
                    cards.extend(optional);

                    Some(cards)
                }
                _ => None,
            })
            .flatten()
            .collect::<Vec<_>>();
        nums.sort();

        let s = nums
            .into_iter()
            .map(|(i, required)| {
                let s = i.to_string();

                let s = if !required {
                    s.color(color.to_bright_color()).bold()
                } else {
                    s.color(color.to_color())
                };

                format!("{}", s)
            })
            .join(" ");

        if !s.is_empty() {
            println!("{}", s);
        }
    }

    if let Some(joker_count) = config.cards.get(&Card::Joker) {
        let s = iter::repeat("X".white().bold())
            .take(joker_count.optional as usize)
            .chain(iter::repeat("X".into()).take(joker_count.required as usize))
            .join(" ");

        println!("{}", s);
    }
}

fn pretty_print_solution(model: &Model<Var>) {
    let mut required_cards = HashMap::<_, u32>::new();
    for v in model.vars() {
        if let Var::Required(c, _) = v.var() {
            *required_cards.entry(*c).or_default() += 1;
        }
    }

    let mut required_cards_left = |card: Card| {
        if let Some(i) = required_cards.get_mut(&card) {
            if *i > 0 {
                *i -= 1;
                return true;
            }
        }
        false
    };

    let mut num_blocks = Vec::new();

    for color in Color::iter() {
        for instance in 0..=1 {
            let block: Vec<_> = iproduct!(1..=13, vec![true, false].into_iter())
                .filter(|&(index, is_joker)| {
                    model
                        .var(Var::Num(NumberBlock {
                            index,
                            color,
                            is_joker,
                            instance,
                        }))
                        .unwrap()
                })
                .collect();

            if !block.is_empty() {
                num_blocks.push((color, block));
            }
        }
    }

    for (color, block) in num_blocks {
        let s = block
            .into_iter()
            .map(|(idx, joker)| {
                if joker {
                    return if required_cards_left(Card::Joker) {
                        "X".color(color.to_color())
                    } else {
                        "X".bold().color(color.to_bright_color())
                    };
                }

                if required_cards_left(Card::Normal { color, number: idx }) {
                    return idx.to_string().color(color.to_color());
                }

                idx.to_string().color(color.to_bright_color()).bold()
            })
            .join(" ");
        println!("{}", s);
    }

    let mut color_blocks = Vec::new();

    for number in 1..=13 {
        for instance in 0..=1 {
            let block: Vec<_> =
                iproduct!(Color::iter(), vec![true, false].into_iter())
                    .filter(|&(color, is_joker)| {
                        model
                            .var(Var::Color(ColorBlock {
                                number,
                                color,
                                is_joker,
                                instance,
                            }))
                            .unwrap()
                    })
                    .collect();
            if !block.is_empty() {
                color_blocks.push((number, block));
            }
        }
    }

    for (num, block) in color_blocks {
        let s = block
            .into_iter()
            .map(|(color, joker)| {
                if joker {
                    return if required_cards_left(Card::Joker) {
                        "X".color(color.to_color())
                    } else {
                        "X".bold().color(color.to_bright_color())
                    };
                }

                if required_cards_left(Card::Normal { color, number: num }) {
                    return num.to_string().color(color.to_color());
                }

                num.to_string().color(color.to_bright_color()).bold()
            })
            .join(" ");
        println!("{}", s);
    }
}

fn count_optional_cards_in_solution(model: &Model<Var>) -> usize {
    model
        .vars()
        .filter(|v| matches!(v, Lit::Pos(Var::Optional(..))))
        .count()
}

fn try_solve(
    config: &Config,
    atleast: u32, // How many optional cards should be used.
    with_joker: bool,
) -> Option<(Model<Var>, CadicalEncoder<Var>)> {
    let mut encoder = CadicalEncoder::new();

    encode_general_rules(&mut encoder);

    encode_config(&mut encoder, config, atleast, with_joker);

    let model = encoder.solve();
    model.map(|model| (model, encoder))
}

fn collect_solutions(config: &Config, with_joker: bool) -> Vec<Model<Var>> {
    let mut min_encoded = 0;
    let mut min = 0;
    let mut max = config.total_optional_cards() + 1;

    let mut best_model = None;
    let mut best = 0;

    loop {
        let val = (min + max) / 2;

        //println!("Try atleast {}", val);
        if let Some(model) = try_solve(&config, val, with_joker) {
            let cards = count_optional_cards_in_solution(&model.0) as u32;

            //println!("Possible solution! ({})", cards);

            min_encoded = val;
            min = cards;
            if val >= best {
                best = cards;
                best_model = Some(model);
            }
        } else {
            //println!("Impossible!");
            max = val;
        }

        if val == min {
            break;
        }
    }

    let mut models = Vec::new();

    if let Some((mut model, mut encoder)) = best_model {
        models.push(model.clone());

        // Required so that the search for alternative solutions has the same number
        // of cards.
        if min_encoded < min {
            let lits = model
                .vars()
                .filter(|v| matches!(v.var(), Var::Optional(..)))
                .map(|v| *v.var());
            encoder.add_constraint(AtLeastK {
                k: min,
                lits: lits.into_iter(),
            });
        }

        loop {
            encoder.add_constraint(Or(model
                .vars()
                .filter(|v| matches!(v.var(), Var::Optional(..)))
                .map(|v| !v)));
            if let Some(new_model) = encoder.solve() {
                models.push(new_model.clone());
                model = new_model;
            } else {
                break;
            }
        }
    }

    models
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

    println!("Available:");
    pretty_print_config(&config);

    let print_models = |models: Vec<Model<Var>>| {
        for (i, sol) in models.into_iter().enumerate() {
            println!("{}.", i);
            pretty_print_solution(&sol);
        }
    };

    match config.cards.get(&Card::Joker) {
        Some(&count) if count.optional > 0  => {

            let models = collect_solutions(&config, false);
            if !models.is_empty() {
                println!("Solution without joker:");
                print_models(models);
            } else {
                println!("Impossible to solve without joker")
            }

            let models = collect_solutions(&config, true);
            if !models.is_empty() {
                println!("Solution with joker:");
                print_models(models);
            } else {
                println!("Impossible to solve with joker")
            }
        },
        _ => {
            let models = collect_solutions(&config, false);
            if !models.is_empty() {
                println!("Solution");
                print_models(models);
            } else {
                println!("No Solution exists!")
            }
        }
    }

    Ok(())
}
