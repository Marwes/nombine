#![cfg_attr(not(feature = "std"), no_std)]

//! Converters between [combine][] and [nom][] parsers.
//!
//! [combine]:https://github.com/Marwes/combine
//! [nom]:https://github.com/Geal/nom
//!
//! ```
//! extern crate combine;
//! #[macro_use]
//! extern crate nom;
//! extern crate nombine;
//!
//! use std::collections::HashMap;
//!
//! use combine::error::ParseError;
//! use combine::parser::char::char;
//! use combine::parser::range;
//! use combine::stream::FullRangeStream;
//! use combine::{Parser, sep_by};
//!
//! use nombine::{convert_from_combine, from_combine, from_nom};
//!
//! fn from_hex(input: &str) -> Result<u8, std::num::ParseIntError> {
//!     u8::from_str_radix(input, 16)
//! }
//!
//! fn is_hex_digit(c: char) -> bool {
//!     match c {
//!         '0'..='9' | 'a'..='f' | 'A'..='F' => true,
//!         _ => false,
//!     }
//! }
//!
//! named!(hex<&str, u8>,
//!   map_res!(take_while_m_n!(2, 2, is_hex_digit), from_hex)
//! );
//!
//! fn identifier<'a, I>() -> impl Parser<Input = I, Output = &'a str>
//! where
//!     I: FullRangeStream<Item = char, Range = &'a str> + 'a,
//!     // Necessary due to rust-lang/rust#24159
//!     I::Error: ParseError<I::Item, I::Range, I::Position>,
//! {
//!     range::take_while1(|c: char| c.is_alphabetic())
//! }
//!
//! named!(field<&str, (&str, u8)>,
//!     map!(convert_from_combine((identifier(), char('='), from_nom(hex)), |_| 0), move |(name, _, value)| (name, value))
//! );
//!
//! fn fields<'a, I>() -> impl Parser<Input = I, Output = HashMap<&'a str, u8>>
//! where
//!     I: FullRangeStream<Item = char, Range = &'a str> + 'a,
//!     // Necessary due to rust-lang/rust#24159
//!     I::Error: ParseError<I::Item, I::Range, I::Position>,
//! {
//!     sep_by(from_nom(field), char(','))
//! }
//!
//!
//! fn main() {
//!     // Parse using nom's interface
//!     assert_eq!(
//!         from_combine(fields())("fieldA=2F,fieldB=00"),
//!         Ok((
//!             "",
//!             vec![
//!                 (
//!                     "fieldA",
//!                     47,
//!                 ),
//!                 (
//!                     "fieldB",
//!                     0,
//!                 ),
//!             ].into_iter().collect(),
//!         ))
//!     );
//!    
//!     // Parse using combine's interface
//!     assert_eq!(
//!         fields().easy_parse("fieldA=2F,fieldB=00"),
//!         Ok((
//!             vec![
//!                 (
//!                     "fieldA",
//!                     47,
//!                 ),
//!                 (
//!                     "fieldB",
//!                     0,
//!                 ),
//!             ].into_iter().collect(),
//!             "",
//!         ))
//!     );
//! }
//! ```

#![cfg(feature = "std")]
extern crate core;

pub extern crate combine;
#[cfg_attr(test, macro_use)]
pub extern crate nom;

use combine::error::{Consumed, ParseError, StreamError, Tracked};
use combine::stream::{FullRangeStream, Range, StreamErrorFor};
use combine::{Parser, Stream};

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
    parse: NomParser<I::Range, O, E>,
) -> impl Parser<Input = I, Output = O, PartialState = ()>
where
    I: FullRangeStream,
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
    parse: NomParser<I::Range, O, E>,
    mut convert_error: impl FnMut(nom::ErrorKind<E>) -> StreamErrorFor<I>,
) -> impl Parser<Input = I, Output = O, PartialState = ()>
where
    I: FullRangeStream,
    I::Range: Range,
{
    combine::parser(move |input: &mut I| {
        // Combine's `<I as StreamOnce>::Range` type is usually `&[u8]` or `&str` which is what nom
        // expects. By Using `I::Range` instead of `I` directly we get combine's `easy_parse` (and
        // many other stream wrappers) working and aren't limited to parsing the plain slices
        let start_range = input.range();
        let start_range_len = start_range.len();
        match parse(start_range) {
            Ok((new_input, output)) => {
                let consumed_len = start_range_len - new_input.len();
                let consumed = if consumed_len == 0 {
                    Consumed::Empty(())
                } else {
                    Consumed::Consumed(())
                };
                // Move the stream up to where `nom` left off
                let _ = input.uncons_range(consumed_len);
                Ok((output, consumed))
            }
            Err(err) => Err(match err {
                nom::Err::Incomplete(_) => {
                    // Marking the error as `EOF` + consumed will trigger combine's partial parsing
                    // to kick in (if it is enabled).
                    let len = input.range().len();
                    let _ = input.uncons_range(len);
                    Consumed::Consumed(
                        I::Error::from_error(input.position(), StreamErrorFor::<I>::end_of_input())
                            .into(),
                    )
                }
                nom::Err::Error(err) => from_nom_context(input, err, &mut convert_error),
                nom::Err::Failure(err) => Consumed::Consumed(
                    from_nom_context(input, err, &mut convert_error).into_inner(),
                ),
            }),
        }
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

fn position<I>(input: &mut I, range: I::Range) -> I::Position
where
    I: FullRangeStream,
    I::Range: Range,
{
    let distance = input.range().len() - range.len();
    let checkpoint = input.checkpoint();
    let _ = input.uncons_range(distance);
    let position = input.position();
    input.reset(checkpoint);
    position
}

fn from_nom_context<I, E>(
    input: &mut I,
    context: nom::Context<I::Range, E>,
    mut convert_error: impl FnMut(nom::ErrorKind<E>) -> StreamErrorFor<I>,
) -> Consumed<Tracked<I::Error>>
where
    I: FullRangeStream,
    I::Range: Range,
{
    let error_position;
    let error = match context {
        nom::Context::Code(error_input, err) => {
            error_position = position(input, error_input);
            I::Error::from_error(error_position.clone(), convert_error(err))
        }

        #[cfg(feature = "verbose-errors")]
        nom::Context::List(nom_errors) => {
            let mut nom_errors = nom_errors.into_iter();
            let (error_input, error_kind) = match nom_errors.next() {
                None => return Consumed::Empty(I::Error::empty(input.position()).into()),
                Some(nom_error) => nom_error,
            };

            let mut furthest_error_position = position(input, error_input);

            let mut err =
                I::Error::from_error(furthest_error_position.clone(), convert_error(error_kind));

            // Perform `combine`s error merging which only keeps the error the furthest into the
            // stream (this lets `combine` report that it expected one of multiple things at a
            // single location which is usually what one wants in error messages).
            for (error_input, error_kind) in nom_errors {
                use std::cmp::Ordering;

                let error_position = position(input, error_input);

                match error_position.cmp(&furthest_error_position) {
                    Ordering::Less => (),
                    Ordering::Equal => err.add(convert_error(error_kind)),
                    Ordering::Greater => {
                        err = I::Error::from_error(error_position, convert_error(error_kind));
                    }
                }
            }
            error_position = furthest_error_position;
            err
        }
    };
    if error_position == input.position() {
        Consumed::Empty(error.into())
    } else {
        Consumed::Consumed(error.into())
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

    named!(pub hex_primary<&str, u8>,
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
    use combine::{easy, sep_by};

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

    #[test]
    fn test_error_position_eof() {
        let input = "!a";
        assert_eq!(
            (char('!'), from_nom(hex_primary))
                .easy_parse(input)
                .map_err(|err| err.map_position(|p| p.translate_position(input))),
            Err(easy::Errors {
                position: 2,
                errors: vec![easy::Error::end_of_input()],
            })
        );
    }

    #[test]
    fn test_error_position() {
        let input = "!az";
        assert_eq!(
            (char('!'), from_nom(hex_primary).expected("hex"))
                .easy_parse(input)
                .map_err(|err| err.map_position(|p| p.translate_position(input))),
            Err(easy::Errors {
                position: 1,
                errors: vec![
                    easy::Error::message_message("TakeWhileMN"),
                    easy::Error::unexpected_token('a'),
                    easy::Error::expected_static_message("hex"),
                ],
            })
        );
    }
}
