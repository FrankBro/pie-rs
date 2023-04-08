use logos::{Lexer, Logos};
use vec1::Vec1;

use crate::types::{Expr, ExprAt, Loc, Pos, Symbol};

#[derive(Debug)]
pub enum Error {
    Arg(Option<Token>),
    TypedArg(Option<Token>),
    UnexpectedClosedParen,
    ExpectedClosedParen(Option<Token>),
    AppNoFn,
}

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

struct Parser<'a> {
    source: String,
    lex: Lexer<'a, Token>,
}

impl<'a> Parser<'a> {
    fn loc(&self) -> Loc {
        let line = self.lex.extras.line_breaks;
        let span = self.lex.span();
        Loc {
            source: self.source.clone(),
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

    fn args(&mut self) -> Result<Vec1<(Loc, Symbol)>> {
        match self.lex.next() {
            Some(Token::LParen) => (),
            token => {
                return Err(Error::Arg(token));
            }
        }
        let arg = match self.lex.next() {
            Some(Token::Var(symbol)) => {
                let loc = self.loc();
                (loc, symbol.into())
            }
            token => {
                return Err(Error::Arg(token));
            }
        };
        let mut args = Vec1::new(arg);
        loop {
            match self.lex.next() {
                Some(Token::Var(symbol)) => {
                    let loc = self.loc();
                    args.push((loc, symbol.into()));
                }
                Some(Token::RParen) => {
                    break;
                }
                token => {
                    return Err(Error::Arg(token));
                }
            };
        }
        Ok(args)
    }

    fn typed_args(&mut self) -> Result<Vec1<(Loc, Symbol, Expr)>> {
        match self.lex.next() {
            Some(Token::LParen) => (),
            token => {
                return Err(Error::TypedArg(token));
            }
        }
        let typed_arg = match self.lex.next() {
            Some(Token::Var(symbol)) => {
                let loc = self.loc();
                let expr = self.expr()?;
                (loc, symbol.into(), expr)
            }
            token => {
                return Err(Error::TypedArg(token));
            }
        };
        let mut typed_args = Vec1::new(typed_arg);
        loop {
            match self.lex.next() {
                Some(Token::Var(symbol)) => {
                    let loc = self.loc();
                    let expr = self.expr()?;
                    typed_args.push((loc, symbol.into(), expr));
                }
                Some(Token::RParen) => {
                    break;
                }
                token => {
                    return Err(Error::TypedArg(token));
                }
            };
        }
        Ok(typed_args)
    }

    fn exprs(&mut self) -> Result<Vec1<Expr>> {
        let expr = self.expr()?;
        let mut exprs = Vec1::new(expr);
        while let Some(expr) = self.expr_or_close()? {
            exprs.push(expr);
        }
        Ok(exprs)
    }

    fn parens(&mut self) -> Result<Expr> {
        let open_loc = self.loc();
        let expr_at = match self.lex.next() {
            Some(Token::Add1) => ExprAt::Add1(self.expr()?),
            Some(Token::WhichNat) => ExprAt::WhichNat(self.expr()?, self.expr()?, self.expr()?),
            Some(Token::IterNat) => ExprAt::IterNat(self.expr()?, self.expr()?, self.expr()?),
            Some(Token::RecNat) => ExprAt::RecNat(self.expr()?, self.expr()?, self.expr()?),
            Some(Token::IndNat) => {
                ExprAt::IndNat(self.expr()?, self.expr()?, self.expr()?, self.expr()?)
            }
            Some(Token::Lambda) => ExprAt::Lambda(self.args()?, self.expr()?),
            Some(Token::Pi) => ExprAt::Pi(self.typed_args()?, self.expr()?),
            Some(Token::Arrow) => ExprAt::Arrow(self.expr()?, self.exprs()?),
            Some(Token::The) => ExprAt::The(self.expr()?, self.expr()?),
            Some(Token::Sigma) => ExprAt::Sigma(self.typed_args()?, self.expr()?),
            Some(Token::Pair) => ExprAt::Pair(self.expr()?, self.expr()?),
            Some(Token::Cons) => ExprAt::Cons(self.expr()?, self.expr()?),
            Some(Token::Car) => ExprAt::Car(self.expr()?),
            Some(Token::Cdr) => ExprAt::Cdr(self.expr()?),
            Some(Token::Eq) => ExprAt::Eq(self.expr()?, self.expr()?, self.expr()?),
            Some(Token::Same) => ExprAt::Same(self.expr()?),
            Some(Token::Replace) => ExprAt::Replace(self.expr()?, self.expr()?, self.expr()?),
            Some(Token::Trans) => ExprAt::Trans(self.expr()?, self.expr()?),
            Some(Token::Cong) => ExprAt::Cong(self.expr()?, self.expr()?),
            Some(Token::Symm) => ExprAt::Symm(self.expr()?),
            Some(Token::IndEq) => ExprAt::IndEq(self.expr()?, self.expr()?, self.expr()?),
            Some(Token::List) => ExprAt::List(self.expr()?),
            Some(Token::ListCons) => ExprAt::ListCons(self.expr()?, self.expr()?),
            Some(Token::RecList) => ExprAt::RecList(self.expr()?, self.expr()?, self.expr()?),
            Some(Token::IndList) => {
                ExprAt::IndList(self.expr()?, self.expr()?, self.expr()?, self.expr()?)
            }
            Some(Token::Vec) => ExprAt::Vec(self.expr()?, self.expr()?),
            Some(Token::VecCons) => ExprAt::VecCons(self.expr()?, self.expr()?),
            Some(Token::VecHead) => ExprAt::VecHead(self.expr()?),
            Some(Token::VecTail) => ExprAt::VecTail(self.expr()?),
            Some(Token::IndVec) => ExprAt::IndVec(
                self.expr()?,
                self.expr()?,
                self.expr()?,
                self.expr()?,
                self.expr()?,
            ),
            Some(Token::Either) => ExprAt::Either(self.expr()?, self.expr()?),
            Some(Token::Left) => ExprAt::EitherLeft(self.expr()?),
            Some(Token::Right) => ExprAt::EitherRight(self.expr()?),
            Some(Token::IndEither) => {
                ExprAt::IndEither(self.expr()?, self.expr()?, self.expr()?, self.expr()?)
            }
            Some(Token::IndAbsurd) => ExprAt::IndAbsurd(self.expr()?, self.expr()?),
            token => {
                let expr = self.token_expr_or_close(token)?.ok_or(Error::AppNoFn)?;
                let exprs = self.exprs()?;
                ExprAt::App(expr, exprs)
            }
        };
        // Arrow already is in the context of the rparen
        match &expr_at {
            ExprAt::Arrow(_, _) => (),
            ExprAt::App(_, _) => (),
            _ => match self.lex.next() {
                Some(Token::RParen) => (),
                token => {
                    return Err(Error::ExpectedClosedParen(token));
                }
            },
        }
        let close_loc = self.loc();
        Ok(Expr {
            loc: Loc::span(open_loc, close_loc),
            expr: Box::new(expr_at),
        })
    }

    fn token_expr_or_close(&mut self, token: Option<Token>) -> Result<Option<Expr>> {
        match token {
            Some(Token::Tick(symbol)) => self.make(ExprAt::Tick(symbol.into())),
            Some(Token::Var(symbol)) => self.make(ExprAt::Var(symbol.into())),
            Some(Token::U) => self.make(ExprAt::U),
            Some(Token::Nat) => self.make(ExprAt::Nat),
            Some(Token::Trivial) => self.make(ExprAt::Trivial),
            Some(Token::Sole) => self.make(ExprAt::Sole),
            Some(Token::Atom) => self.make(ExprAt::Atom),
            Some(Token::Zero) => self.make(ExprAt::Zero),
            Some(Token::NatLit(n)) => self.make(ExprAt::NatLit(n)),
            Some(Token::ListNil) => self.make(ExprAt::ListNil),
            Some(Token::VecNil) => self.make(ExprAt::VecNil),
            Some(Token::Absurd) => self.make(ExprAt::Absurd),
            Some(Token::Todo) => self.make(ExprAt::Todo),
            Some(Token::LParen) => self.parens().map(Some),
            Some(Token::RParen) => Ok(None),
            _ => todo!(),
        }
    }

    fn expr_or_close(&mut self) -> Result<Option<Expr>> {
        let token = self.lex.next();
        self.token_expr_or_close(token)
    }

    fn expr(&mut self) -> Result<Expr> {
        match self.expr_or_close()? {
            Some(expr) => Ok(expr),
            None => Err(Error::UnexpectedClosedParen),
        }
    }

    fn make_with_loc(&self, expr_at: ExprAt<Loc>, loc: Loc) -> Result<Option<Expr>> {
        Ok(Some(Expr {
            loc,
            expr: Box::new(expr_at),
        }))
    }

    fn make(&mut self, expr_at: ExprAt<Loc>) -> Result<Option<Expr>> {
        let loc = self.loc();
        self.make_with_loc(expr_at, loc)
    }
}

pub fn parse_expr(source: &str, input: &str) -> Result<Expr> {
    let lex = Token::lexer(input);
    let mut parser = Parser {
        lex,
        source: source.to_owned(),
    };
    parser.expr()
}

#[cfg(test)]
mod tests {
    use vec1::vec1;

    use crate::types::{Expr, ExprAt, Loc, Pos};

    use super::parse_expr;

    const SOURCE: &str = "<test input>";

    fn loc(start: usize, end: usize) -> Loc {
        Loc {
            source: SOURCE.to_owned(),
            start: Pos {
                line: 1,
                col: start,
            },
            end: Pos { line: 1, col: end },
        }
    }

    #[test]
    fn test_var_parse() {
        let input = "x";
        let expected = Expr {
            loc: loc(1, 2),
            expr: Box::new(ExprAt::Var("x".into())),
        };
        let actual = parse_expr(SOURCE, input).unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_zero() {
        let input = "zero";
        let expected = Expr {
            loc: loc(1, 5),
            expr: Box::new(ExprAt::Zero),
        };
        let actual = parse_expr(SOURCE, input).unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_app() {
        let input = "(f x)";
        let expected = Expr {
            loc: loc(1, 6),
            expr: Box::new(ExprAt::App(
                Expr {
                    loc: loc(2, 3),
                    expr: Box::new(ExprAt::Var("f".into())),
                },
                vec1![Expr {
                    loc: loc(4, 5),
                    expr: Box::new(ExprAt::Var("x".into()))
                }],
            )),
        };
        let actual = parse_expr(SOURCE, input).unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_lambda() {
        let input = "(lambda (x y) (add1 x))";
        let expected = Expr {
            loc: loc(1, 24),
            expr: Box::new(ExprAt::Lambda(
                vec1![(loc(10, 11), "x".into()), (loc(12, 13), "y".into())],
                Expr {
                    loc: loc(15, 23),
                    expr: Box::new(ExprAt::Add1(Expr {
                        loc: loc(21, 22),
                        expr: Box::new(ExprAt::Var("x".into())),
                    })),
                },
            )),
        };
        let actual = parse_expr(SOURCE, input).unwrap();
        assert_eq!(expected, actual);
    }
}
