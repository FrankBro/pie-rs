use std::mem::size_of;

use elab::Synth;
use normalize::Norm;

use crate::{
    elab::Elab,
    parse::parse_expr,
    types::{Closure, Core, Loc, Pos, Value},
};

mod alpha_equiv;
mod elab;
mod fresh;
mod normalize;
mod parse;
mod types;

const SOURCE: &str = "<test input>";

fn elab() -> Elab {
    let loc = Loc {
        source: "<test suite>".to_owned(),
        start: Pos { line: 1, col: 1 },
        end: Pos { line: 1, col: 1 },
    };
    Elab::new(loc)
}

fn norm() -> Norm {
    Norm::default()
}

fn main() {
    /*
    let expr = parse_expr("temp", "").unwrap();
    let loc = Loc {
        source: "<temp>".to_owned(),
        start: Pos { line: 1, col: 1 },
        end: Pos { line: 1, col: 1 },
    };
    let synth = Elab::new(loc).synth(&expr).unwrap();
    dbg!(synth);
    println!("Hello, world!");
    */
    let input = "(which-Nat 40 't (lambda (x) 'nil))";
    let input_expr = parse_expr(SOURCE, input).unwrap();
    let Synth {
        the_type: actual_ty,
        the_expr: actual_core,
    } = elab().synth(&input_expr).unwrap();
    println!("Closure {}", size_of::<Closure<Value>>());
    println!("Core {}", size_of::<Core>());
    println!("Value {}", size_of::<Value>());
    println!("Box value {}", size_of::<Box<Value>>());
    let actual_value = norm().eval(&actual_core).unwrap();
    dbg!(actual_value);
}
