use nom::{
    branch::alt,
    character::complete::{digit1, multispace0, multispace1, space1},
    combinator::opt,
    multi::separated_list1,
    Parser,
};
use nom_supreme::{
    error::ErrorTree,
    final_parser::{final_parser, Location},
    parse_from_str,
    parser_ext::ParserExt,
    tag::complete::tag,
};

use crate::{Card, Color, Config};

type IResult<'a, T> = nom::IResult<&'a str, T, ErrorTree<&'a str>>;

pub fn parse_config(input: &str) -> Result<Config, ErrorTree<Location>> {
    final_parser(parse_all)(input)
}

fn parse_color(input: &str) -> IResult<Color> {
    alt((
        tag("green").value(Color::Green),
        tag("red").value(Color::Red),
        tag("yellow").value(Color::Yellow),
        tag("blue").value(Color::Blue),
    ))
    .context("parse color")
    .parse(input)
}

fn parse_number(input: &str) -> IResult<usize> {
    parse_from_str(digit1).parse(input)
}

fn parse_card(input: &str) -> IResult<Card> {
    parse_color
        .terminated(space1)
        .and(parse_number)
        .map(|(color, number)| Card { color, number })
        .context("parse card")
        .parse(input)
}

fn parse_multiplier(input: &str) -> IResult<usize> {
    parse_number
        .terminated(tag("x"))
        .context("parse multiplier")
        .parse(input)
}

fn parse_entry(input: &str) -> IResult<(Card, u32)> {
    opt(parse_multiplier.terminated(space1))
        .and(parse_card)
        .context("parse entry")
        .map(|(mult, card)| (card, mult.unwrap_or(1) as u32))
        .parse(input)
}

fn parse_all(input: &str) -> IResult<Config> {
    separated_list1(multispace1, parse_entry)
        .map(|l| {
            let mut config = Config::default();

            for (card, count) in l {
                *config.cards.entry(card).or_insert(0) += count;
            }

            config
        })
        .terminated(multispace0)
        .context("parse all")
        .parse(input)
}
