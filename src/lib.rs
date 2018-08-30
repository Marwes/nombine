#![cfg_attr(not(feature = "std"), no_std)]
extern crate core;

pub extern crate combine;
#[cfg_attr(test, macro_use)]
pub extern crate nom;

use combine::error::{Consumed, ParseError, StreamError};
use combine::stream::{FullRangeStream, Range, StreamErrorFor};
use combine::{Parser, Stream};

fn from_nom_context<I, E>(
    input: &I,
    context: nom::Context<I, E>,
    mut convert_error: impl FnMut(nom::ErrorKind<E>) -> StreamErrorFor<I>,
) -> I::Error
where
    I: Stream,
{
    let _ = input;
    match context {
        nom::Context::Code(error_input, err) => {
            I::Error::from_error(error_input.position(), convert_error(err))
        }

        #[cfg(feature = "verbose-errors")]
        nom::Context::List(nom_errors) => {
            let mut nom_errors = nom_errors.into_iter();
            let (error_input, error_kind) = match nom_errors.next() {
                None => return I::Error::empty(input.position()),
                Some(nom_error) => nom_error,
            };

            let mut furthest_error_position = error_input.position();
            let mut err =
                I::Error::from_error(furthest_error_position.clone(), convert_error(error_kind));

            for (error_input, error_kind) in nom_errors {
                use std::cmp::Ordering;

                match error_input.position().cmp(&furthest_error_position) {
                    Ordering::Less => (),
                    Ordering::Equal => err.add(convert_error(error_kind)),
                    Ordering::Greater => {
                        err =
                            I::Error::from_error(error_input.position(), convert_error(error_kind));
                    }
                }
            }
            err
        }
    }
}

pub type NomParser<I, O, E> = fn(I) -> Result<(I, O), nom::Err<I, E>>;

/// Converts a nom parser into a combine parser
///
/// ```
/// #[macro_use]
/// extern crate nom;
/// extern crate combine;
/// extern crate nombine;
///
/// use std::str::FromStr;
///
/// use combine::Parser;
///
/// named!(multi<&str, Vec<i32>>,
///     separated_list!(char!(','), map_res!(nom::digit, FromStr::from_str) )
/// );
///
/// # fn main() {
/// assert_eq!(
///     nombine::from_nom(multi).parse("1,2,34a"),
///     Ok((vec![1, 2, 34], "a")),
/// );
/// # }
///
/// ```
pub fn from_nom<I, O, E>(
    parse: NomParser<I, O, E>,
) -> impl Parser<Input = I, Output = O, PartialState = ()>
where
    I: FullRangeStream + Clone,
    I::Range: Range,
{
    convert_from_nom(parse, |err| {
        StreamErrorFor::<I>::message_message(err.description())
    })
}

/// Converts a nom parser into a combine parser.
///
/// Like `from_nom` but accepts a function to convert the `nom` error to `combine`.
pub fn convert_from_nom<I, O, E>(
    parse: NomParser<I, O, E>,
    mut convert_error: impl FnMut(nom::ErrorKind<E>) -> StreamErrorFor<I>,
) -> impl Parser<Input = I, Output = O, PartialState = ()>
where
    I: FullRangeStream + Clone,
    I::Range: Range,
{
    combine::parser(move |input: &mut I| match parse(input.clone()) {
        Ok((new_input, output)) => {
            let consumed = if input.position() == new_input.position() {
                Consumed::Empty(())
            } else {
                Consumed::Consumed(())
            };
            *input = new_input;
            Ok((output, consumed))
        }
        Err(err) => Err(match err {
            nom::Err::Incomplete(_) => {
                let len = input.range().len();
                let _ = input.uncons_range(len);
                Consumed::Consumed(
                    I::Error::from_error(input.position(), StreamErrorFor::<I>::end_of_input())
                        .into(),
                )
            }
            nom::Err::Error(err) => {
                Consumed::Empty(from_nom_context(input, err, &mut convert_error).into())
            }
            nom::Err::Failure(err) => {
                Consumed::Consumed(from_nom_context(input, err, &mut convert_error).into())
            }
        }),
    })
}

/// Converts a combine parser into a nom parser
///
/// ```
/// #[macro_use]
/// extern crate nom;
/// extern crate combine;
/// extern crate nombine;
///
/// use std::str;
///
/// use combine::{Parser, from_str, sep_by};
/// use combine::range::take_while1;
/// use combine::parser::char::{char, digit};
///
/// fn multi<'a>() -> impl Parser<Input = &'a str, Output = Vec<i32>> {
///     let int = from_str::<i32, _>(take_while1(|c: char| c.is_digit(10)));
///     sep_by(int, char(','))
/// }
///
/// # fn main() {
/// assert_eq!(
///     nombine::from_combine(multi())("1,2,34a"),
///     Ok(("a", vec![1, 2, 34]))
/// );
/// # }
///
/// ```
pub fn from_combine<I, P>(
    parser: P,
) -> impl FnMut(I) -> Result<(I, P::Output), nom::Err<I, I::Error>>
where
    P: Parser<Input = I>,
    I: Stream,
{
    convert_from_combine(parser, |err| err)
}

/// Converts a combine parser into a nom parser
///
/// Like `from_combine` but accepts a function to convert the `combine` error to `nom`.
pub fn convert_from_combine<I, P, E>(
    mut parser: P,
    mut convert_error: impl FnMut(I::Error) -> E,
) -> impl FnMut(I) -> Result<(I, P::Output), nom::Err<I, E>>
where
    P: Parser<Input = I>,
    I: Stream,
{
    move |mut input| match parser.parse_stream(&mut input) {
        Ok((output, _consumed)) => Ok((input, output)),
        Err(Consumed::Empty(err)) => Err(nom::Err::Error(nom::Context::Code(
            input,
            nom::ErrorKind::Custom(convert_error(err.error)),
        ))),
        Err(Consumed::Consumed(err)) => Err(nom::Err::Failure(nom::Context::Code(
            input,
            nom::ErrorKind::Custom(convert_error(err.error)),
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use combine::parser::char::char;
    use combine::parser::range;
    use combine::RangeStream;

    // Hex parser from https://github.com/Geal/nom
    #[derive(Debug, PartialEq)]
    pub struct Color {
        pub red: u8,
        pub green: u8,
        pub blue: u8,
    }

    fn from_hex(input: &str) -> Result<u8, core::num::ParseIntError> {
        u8::from_str_radix(input, 16)
    }

    fn is_hex_digit(c: char) -> bool {
        match c {
            '0'..='9' | 'a'..='f' | 'A'..='F' => true,
            _ => false,
        }
    }

    named!(hex_primary<&str, u8>,
      map_res!(take_while_m_n!(2, 2, is_hex_digit), from_hex)
    );

    named!(pub hex_color<&str, Color>,
      do_parse!(
               tag!("#")   >>
        red:   hex_primary >>
        green: hex_primary >>
        blue:  hex_primary >>
        (Color { red, green, blue })
      )
    );

    fn identifier<'a, I>() -> impl Parser<Input = I, Output = &'a str>
    where
        I: RangeStream<Item = char, Range = &'a str> + 'a,
        // Necessary due to rust-lang/rust#24159
        I::Error: ParseError<I::Item, I::Range, I::Position>,
    {
        range::take_while1(|c: char| c.is_alphabetic())
    }

    named!(field<&str, (&str, Color)>,
        map!(convert_from_combine((identifier(), char('='), from_nom(hex_color)), |_| 0), move |(name, _, value)| (name, value))
    );

    #[test]
    fn parse_color() {
        assert_eq!(
            hex_color("#2F14DF"),
            Ok((
                "",
                Color {
                    red: 47,
                    green: 20,
                    blue: 223,
                },
            ))
        );
    }

    #[test]
    fn test_from_nom() {
        assert_eq!(
            from_nom(hex_color).parse("#2F14DF"),
            Ok((
                Color {
                    red: 47,
                    green: 20,
                    blue: 223,
                },
                "",
            ))
        );
    }

    #[test]
    fn test_nested() {
        assert_eq!(
            field("color=#2F14DF"),
            Ok((
                "",
                (
                    "color",
                    Color {
                        red: 47,
                        green: 20,
                        blue: 223,
                    }
                ),
            ))
        );
    }

    #[test]
    fn test_or() {
        assert_eq!(
            from_nom(hex_primary).or(char('!').map(|_| 0)).parse("!a"),
            Ok((0, "a"))
        );
    }

    #[test]
    fn test_error() {
        assert!(from_nom(hex_primary).parse("!a").is_err());
    }
}

#[cfg(all(test, feature = "std"))]
mod std_tests {
    use super::*;

    use tests::*;

    use combine::parser::char::char;
    use combine::sep_by;

    #[test]
    fn test_from_combine() {
        assert_eq!(
            from_combine(sep_by(from_nom(hex_color), char(',')))("#2F14DF,#2F14DF"),
            Ok((
                "",
                vec![
                    Color {
                        red: 47,
                        green: 20,
                        blue: 223,
                    },
                    Color {
                        red: 47,
                        green: 20,
                        blue: 223,
                    },
                ],
            ))
        );
    }
}
