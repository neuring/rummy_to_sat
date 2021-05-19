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

use crate::{Amount, Card, Color, Config};

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Category {
    Optional,
    Required,
}

fn parse_category_tag(input: &str) -> IResult<Category> {
    alt((
        tag("REQUIRED:").value(Category::Required),
        tag("OPTIONAL:").value(Category::Optional),
    ))
    .context("parse category tag")
    .parse(input)
}

fn parse_number(input: &str) -> IResult<usize> {
    parse_from_str(digit1).parse(input)
}

fn parse_card(input: &str) -> IResult<Card> {
    alt((
        tag("joker").value(Card::Joker),
        parse_color
            .terminated(space1)
            .and(parse_number)
            .map(|(color, number)| Card::Normal { color, number }),
    ))
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

struct CategoryBlock {
    category: Category,
    entries: Vec<(Card, u32)>,
}

fn parse_category_block(input: &str) -> IResult<CategoryBlock> {
    parse_category_tag
        .terminated(multispace1)
        .and(separated_list1(multispace1, parse_entry))
        .map(|(category, entries)| CategoryBlock { category, entries })
        .context("parse category block")
        .parse(input)
}

fn parse_all(input: &str) -> IResult<Config> {
    separated_list1(multispace1, parse_category_block)
        .map(|category_blocks| {
            let mut config = Config::default();

            for category_block in category_blocks {
                let category = category_block.category;

                for (card, amount) in category_block.entries {
                    match category {
                        Category::Optional => {
                            config
                                .cards
                                .entry(card)
                                .or_insert(Amount::default())
                                .optional += amount
                        }
                        Category::Required => {
                            config
                                .cards
                                .entry(card)
                                .or_insert(Amount::default())
                                .required += amount
                        }
                    }
                }
            }

            config
        })
        .terminated(multispace0)
        .context("parse all")
        .parse(input)
}
