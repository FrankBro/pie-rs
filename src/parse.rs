use logos::{Lexer, Logos};

use crate::types::{Expr, ExprAt, Loc, Pos};

#[derive(Debug)]
enum Error {}

type Result<T, E = Error> = std::result::Result<T, E>;

struct Extras {
    line_breaks: usize,
}

impl Default for Extras {
    fn default() -> Self {
        Self { line_breaks: 1 }
    }
}

fn lex_tick(lex: &mut Lexer<Token>) -> Option<String> {
    let slice = lex.slice();
    let ident = slice[1..slice.len()].to_owned();
    Some(ident)
}

fn lex_var(lex: &mut Lexer<Token>) -> Option<String> {
    let slice = lex.slice();
    let ident = slice.to_owned();
    Some(ident)
}

fn lex_nat_lit(lex: &mut Lexer<Token>) -> Option<u64> {
    let slice = lex.slice();
    slice.parse::<u64>().ok()
}

#[derive(Logos, Debug, PartialEq)]
#[logos(subpattern constituent = r"[a-zA-Z]")]
#[logos(subpattern special_init = r"[!$%&*/:<=>?^_~]")]
#[logos(subpattern init = r"((?&constituent)|(?&special_init))")]
#[logos(subpattern subseq = r"((?&constituent)|(?&special_init)|[0-9+-.@])")]
#[logos(subpattern normal_ident = r"(?&init)(?&subseq)*")]
#[logos(subpattern special_ident = r"(\+|-|\.\.\.)(?&subseq)*")]
#[logos(subpattern ident = r"(?&normal_ident)|(?&special_ident)")]
#[logos(extras = Extras)]
enum Token {
    #[token("U")]
    U,
    #[token("Nat")]
    Nat,
    #[token("Atom")]
    Atom,
    #[token("zero")]
    Zero,
    #[token("Trivial")]
    Trivial,
    #[token("sole")]
    Sole,
    #[token("nil")]
    ListNil,
    #[token("Absurd")]
    Absurd,
    #[regex("'(?&ident)", lex_tick)]
    Tick(String),
    #[token("vecnil")]
    VecNil,
    #[token("TODO")]
    Todo,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("add1")]
    Add1,
    #[regex("(lambda|λ)")]
    Lambda,
    #[regex("(Pi|Π)")]
    Pi,
    #[regex("(->|→)")]
    Arrow,
    #[regex("(Sigma|Σ)")]
    Sigma,
    #[token("Pair")]
    Pair,
    #[token("cons")]
    Cons,
    #[token("which-Nat")]
    WhichNat,
    #[token("iter-Nat")]
    IterNat,
    #[token("rec-Nat")]
    RecNat,
    #[token("ind-Nat")]
    IndNat,
    #[token("car")]
    Car,
    #[token("cdr")]
    Cdr,
    #[token("the")]
    The,
    #[token("=")]
    Eq,
    #[token("same")]
    Same,
    #[token("replace")]
    Replace,
    #[token("trans")]
    Trans,
    #[token("cong")]
    Cong,
    #[token("symm")]
    Symm,
    #[token("ind-=")]
    IndEq,
    #[token("List")]
    List,
    #[token("::")]
    ListCons,
    #[token("rec-List")]
    RecList,
    #[token("ind-List")]
    IndList,
    #[token("Vec")]
    Vec,
    #[token("vec::")]
    VecCons,
    #[token("head")]
    VecHead,
    #[token("tail")]
    VecTail,
    #[token("ind-Vec")]
    IndVec,
    #[token("Either")]
    Either,
    #[token("left")]
    Left,
    #[token("right")]
    Right,
    #[token("ind-Either")]
    IndEither,
    #[token("ind-Absurd")]
    IndAbsurd,
    #[regex(r"(?&ident)", lex_var)]
    Var(String),
    #[regex("[0-9]", lex_nat_lit)]
    NatLit(u64),

    #[token("\n", |lex| {
        lex.extras.line_breaks += 1;
        logos::Skip
    })]
    #[error]
    #[regex(r"[ \t\f]+", logos::skip)]
    Error,
}

fn parse_loc(lex: &Lexer<Token>, source: &str) -> Loc {
    let line = lex.extras.line_breaks;
    let span = lex.span();
    Loc {
        source: source.to_owned(),
        start: Pos {
            line,
            col: span.start + 1,
        },
        end: Pos {
            line,
            col: span.end + 1,
        },
    }
}

fn parse_parens(lex: &mut Lexer<Token>, source: &str, open_loc: Loc) -> Result<Expr> {
    let l = &lex;
    let s = source;
    fn expr(lex: &mut Lexer<Token>, source: &str) -> Result<Expr> {
        parse_located_expr(lex, source)
    }
    let expr_at = match lex.next() {
        Some(Token::Add1) => ExprAt::Add1(expr(lex, source)?),
        Some(Token::WhichNat) => {
            ExprAt::WhichNat(expr(lex, source)?, expr(lex, source)?, expr(lex, source)?)
        }
        Some(Token::IterNat) => {
            ExprAt::IterNat(expr(lex, source)?, expr(lex, source)?, expr(lex, source)?)
        }
        Some(Token::RecNat) => {
            ExprAt::RecNat(expr(lex, source)?, expr(lex, source)?, expr(lex, source)?)
        }
        Some(Token::IndNat) => ExprAt::IndNat(
            expr(lex, source)?,
            expr(lex, source)?,
            expr(lex, source)?,
            expr(lex, source)?,
        ),
        _ => todo!(),
    };
    let close_loc = parse_loc(lex, source);
    Ok(Expr {
        loc: Loc::span(open_loc, close_loc),
        expr: Box::new(expr_at),
    })
}

fn parse_located_expr(lex: &mut Lexer<Token>, source: &str) -> Result<Expr> {
    let loc = parse_loc(lex, source);
    fn make(loc: Loc, expr_at: ExprAt<Loc>) -> Result<Expr> {
        Ok(Expr {
            loc,
            expr: Box::new(expr_at),
        })
    };
    match lex.next() {
        Some(Token::Tick(symbol)) => make(loc, ExprAt::Tick(symbol.into())),
        Some(Token::Var(symbol)) => make(loc, ExprAt::Var(symbol.into())),
        Some(Token::U) => make(loc, ExprAt::U),
        Some(Token::Nat) => make(loc, ExprAt::Nat),
        Some(Token::Trivial) => make(loc, ExprAt::Trivial),
        Some(Token::Sole) => make(loc, ExprAt::Sole),
        Some(Token::Atom) => make(loc, ExprAt::Atom),
        Some(Token::Zero) => make(loc, ExprAt::Zero),
        Some(Token::NatLit(n)) => make(loc, ExprAt::NatLit(n)),
        Some(Token::ListNil) => make(loc, ExprAt::ListNil),
        Some(Token::VecNil) => make(loc, ExprAt::VecNil),
        Some(Token::Absurd) => make(loc, ExprAt::Absurd),
        Some(Token::Todo) => make(loc, ExprAt::Todo),
        Some(Token::LParen) => parse_parens(lex, source, loc),
        _ => todo!(),
    }
}

fn parse_expr(source: &str, input: &str) -> Result<Expr> {
    let mut lex = Token::lexer(input);
    parse_located_expr(&mut lex, source)
}

#[cfg(test)]
mod tests {
    use crate::types::{Expr, ExprAt, Loc, Pos};

    use super::parse_expr;

    const SOURCE: &str = "<test input>";

    #[test]
    fn test_var_parse() {
        let input = "x";
        let expected = Expr {
            loc: Loc {
                source: SOURCE.to_owned(),
                start: Pos { line: 1, col: 1 },
                end: Pos { line: 1, col: 2 },
            },
            expr: Box::new(ExprAt::Var("x".into())),
        };
        let actual = parse_expr("<test input>", input).unwrap();
        assert_eq!(expected, actual);
    }
}
