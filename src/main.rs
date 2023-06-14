use normalize::Norm;

use crate::{
    elab::Elab,
    parse::parse_expr,
    types::{Loc, Pos},
};

mod alpha_equiv;
mod elab;
mod fresh;
mod normalize;
mod parse;
mod types;

fn main() {
    let expr = parse_expr("temp", "").unwrap();
    let loc = Loc {
        source: "<temp>".to_owned(),
        start: Pos { line: 1, col: 1 },
        end: Pos { line: 1, col: 1 },
    };
    let synth = Elab::new(loc).synth(&expr).unwrap();
    dbg!(synth);
    println!("Hello, world!");
}
