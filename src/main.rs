mod sat;

use itertools::iproduct;
use sat::prelude::*;
use strum::IntoEnumIterator;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, strum::EnumIter)]
enum Color {
    Green,
    Red,
    Blue,
    Yellow,
}

fn valid_num(i: impl Into<Option<u32>>) -> bool {
    let i = i.into();
    match i {
        Some(i) if i >= 1 && i <= 13 => true,
        None => false,
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
struct NumberBlock {
    // Block with sequentially growing numbers.
    color: Color,
    instance: u32,

    index: usize, // 1..=13
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
struct ColorBlock {
    // Block with number and different colors.
    number: u32, // 1..=13
    instance: u32,

    color: Color,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
struct Card {
    color: Color,
    number: u32, // 1..=13
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, derive_more::From)]
enum Var {
    Num(NumberBlock),
    Color(ColorBlock),
    Config(Card),
}

fn encode_number_block_rules(solver: &mut Solver<Var>, color: Color, instance: u32) {
    let num_block = |index| NumberBlock { color, instance, index };

    for i in 1u32..=13 {

        let i_pre1 = i.checked_sub(1);
        let i_pre2 = i.checked_sub(2);

        let i_post1 = i.checked_add(1);
        let i_post2 = i.checked_add(2);

        todo!()

    }

}

fn encode_general_rules(solver: &mut Solver<Var>) {
    for (color, instance) in iproduct!(Color::iter(), 0..=1) {
        encode_number_block_rules(solver, color, instance);
    }
}

fn main() {
    let mut solver = Solver::new();
    encode_general_rules(&mut solver);
}
