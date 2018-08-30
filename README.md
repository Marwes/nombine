# nombine

Converters between [combine][] and [nom][].

[combine]:https://github.com/Marwes/combine
[nom]:https://github.com/Geal/nom

```rust
extern crate combine;
extern crate nom;
extern crate nombine;

use std::collections::HashMap;

use combine::error::ParseError;
use combine::parser::char::char;
use combine::parser::range;
use combine::{Parser, RangeStream, sep_by};

use nombine::{convert_from_combine, from_combine, from_nom};

fn from_hex(input: &str) -> Result<u8, std::num::ParseIntError> {
    u8::from_str_radix(input, 16)
}

fn is_hex_digit(c: char) -> bool {
    match c {
        '0'..='9' | 'a'..='f' | 'A'..='F' => true,
        _ => false,
    }
}

named!(hex<&str, u8>,
  map_res!(take_while_m_n!(2, 2, is_hex_digit), from_hex)
);

fn identifier<'a, I>() -> impl Parser<Input = I, Output = &'a str>
where
    I: RangeStream<Item = char, Range = &'a str> + 'a,
    // Necessary due to rust-lang/rust#24159
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    range::take_while1(|c: char| c.is_alphabetic())
}

named!(field<&str, (&str, u8)>,
    map!(convert_from_combine((identifier(), char('='), from_nom(hex)), |_| 0), move |(name, _, value)| (name, value))
);

fn fields<'a>() -> impl Parser<Input = &'a str, Output = HashMap<&'a str, u8>> {
    sep_by(from_nom(field), char(','))
}


// Parse using nom's interface
assert_eq!(
    from_combine(fields())("fieldA=2F,fieldB=00"),
    Ok((
        "",
        vec![
            (
                "fieldA",
                47,
            ),
            (
                "fieldB",
                0,
            ),
        ].into_iter().collect(),
    ))
);

// Parse using combine's interface
assert_eq!(
    fields().parse("fieldA=2F,fieldB=00"),
    Ok((
        vec![
            (
                "fieldA",
                47,
            ),
            (
                "fieldB",
                0,
            ),
        ].into_iter().collect(),
        "",
    ))
);
```
```
