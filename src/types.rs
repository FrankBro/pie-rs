use std::fmt::Debug;

use vec1::Vec1;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Symbol {
    pub name: String,
}

impl From<String> for Symbol {
    fn from(name: String) -> Self {
        Symbol { name }
    }
}

impl From<&str> for Symbol {
    fn from(value: &str) -> Self {
        Symbol::from(value.to_owned())
    }
}

#[derive(Clone, PartialEq)]
pub struct Pos {
    pub line: usize,
    pub col: usize,
}

impl Debug for Pos {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

pub struct Positioned<T> {
    pub pos: Pos,
    pub t: T,
}

#[derive(Clone, PartialEq)]
pub struct Loc {
    pub source: String,
    pub start: Pos,
    pub end: Pos,
}

impl Loc {
    pub fn span(p1: Self, p2: Self) -> Self {
        Self {
            source: p1.source.clone(),
            start: p1.start,
            end: p2.end,
        }
    }
}

impl Debug for Loc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} from {:?} to {:?}", self.source, self.start, self.end)
    }
}

#[derive(Clone, Debug)]
pub struct Located<T> {
    pub loc: Loc,
    pub t: T,
}

#[derive(Clone, Debug, PartialEq)]
pub struct LocatedExpr<T> {
    pub loc: T,
    pub expr: Box<ExprAt<T>>,
}

pub type Expr = LocatedExpr<Loc>;

type OutExpr = LocatedExpr<()>;

pub type Arg<T> = (T, Symbol);
pub type TypedArg<T> = (T, Symbol, LocatedExpr<T>);

#[derive(Clone, Debug, PartialEq)]
pub enum ExprAt<T> {
    The(LocatedExpr<T>, LocatedExpr<T>),
    Var(Symbol),
    Atom,
    Tick(Symbol),
    Pair(LocatedExpr<T>, LocatedExpr<T>),
    Sigma(Vec1<TypedArg<T>>, LocatedExpr<T>),
    Cons(LocatedExpr<T>, LocatedExpr<T>),
    Car(LocatedExpr<T>),
    Cdr(LocatedExpr<T>),
    Arrow(LocatedExpr<T>, Vec1<LocatedExpr<T>>),
    Pi(Vec1<TypedArg<T>>, LocatedExpr<T>),
    Lambda(Vec1<Arg<T>>, LocatedExpr<T>),
    App(LocatedExpr<T>, Vec1<LocatedExpr<T>>),
    Nat,
    Zero,
    Add1(LocatedExpr<T>),
    NatLit(u64),
    WhichNat(LocatedExpr<T>, LocatedExpr<T>, LocatedExpr<T>),
    IterNat(LocatedExpr<T>, LocatedExpr<T>, LocatedExpr<T>),
    RecNat(LocatedExpr<T>, LocatedExpr<T>, LocatedExpr<T>),
    IndNat(
        LocatedExpr<T>,
        LocatedExpr<T>,
        LocatedExpr<T>,
        LocatedExpr<T>,
    ),
    List(LocatedExpr<T>),
    ListNil,
    ListCons(LocatedExpr<T>, LocatedExpr<T>),
    RecList(LocatedExpr<T>, LocatedExpr<T>, LocatedExpr<T>),
    IndList(
        LocatedExpr<T>,
        LocatedExpr<T>,
        LocatedExpr<T>,
        LocatedExpr<T>,
    ),
    Vec(LocatedExpr<T>, LocatedExpr<T>),
    VecNil,
    VecCons(LocatedExpr<T>, LocatedExpr<T>),
    VecHead(LocatedExpr<T>),
    VecTail(LocatedExpr<T>),
    IndVec(
        LocatedExpr<T>,
        LocatedExpr<T>,
        LocatedExpr<T>,
        LocatedExpr<T>,
        LocatedExpr<T>,
    ),
    Eq(LocatedExpr<T>, LocatedExpr<T>, LocatedExpr<T>),
    Same(LocatedExpr<T>),
    Symm(LocatedExpr<T>),
    Cong(LocatedExpr<T>, LocatedExpr<T>),
    Replace(LocatedExpr<T>, LocatedExpr<T>, LocatedExpr<T>),
    Trans(LocatedExpr<T>, LocatedExpr<T>),
    IndEq(LocatedExpr<T>, LocatedExpr<T>, LocatedExpr<T>),
    Either(LocatedExpr<T>, LocatedExpr<T>),
    EitherLeft(LocatedExpr<T>),
    EitherRight(LocatedExpr<T>),
    IndEither(
        LocatedExpr<T>,
        LocatedExpr<T>,
        LocatedExpr<T>,
        LocatedExpr<T>,
    ),
    Trivial,
    Sole,
    Absurd,
    IndAbsurd(LocatedExpr<T>, LocatedExpr<T>),
    U,
    Todo,
}

impl<T> ExprAt<T> {
    fn describe(&self) -> String {
        match self {
            Self::The(_, _) => "a type annotation".to_owned(),
            Self::Var(x) => format!("the variable {}", x.name),
            Self::Atom => "Atom".to_owned(),
            Self::Tick(a) => format!("'{}", a.name),
            Self::Pair(_, _) => "a Pair-expression".to_owned(),
            Self::Sigma(_, _) => "a Σ-expression".to_owned(),
            Self::Cons(_, _) => "a cons-expression".to_owned(),
            Self::Car(_) => "a car-expression".to_owned(),
            Self::Cdr(_) => "a cdr-expression".to_owned(),
            Self::Arrow(_, _) => "an arrow-expression".to_owned(),
            Self::Pi(_, _) => "a Π-expression".to_owned(),
            Self::Lambda(_, _) => "a λ-expression".to_owned(),
            Self::App(_, _) => "a function application".to_owned(),
            Self::Nat => "Nat".to_owned(),
            Self::Zero => "zero".to_owned(),
            Self::Add1(_) => "an add1-expression".to_owned(),
            Self::NatLit(n) => format!("the natural number {}", n),
            Self::WhichNat(_, _, _) => "a which-Nat-expression".to_owned(),
            Self::IterNat(_, _, _) => "an iter-Nat-expression".to_owned(),
            Self::RecNat(_, _, _) => "a rec-Nat-expression".to_owned(),
            Self::IndNat(_, _, _, _) => "an ind-Nat-expression".to_owned(),
            Self::List(_) => "a List type".to_owned(),
            Self::ListNil => "the empty list nil".to_owned(),
            Self::ListCons(_, _) => "a ::-expression".to_owned(),
            Self::RecList(_, _, _) => "a rec-List-expression".to_owned(),
            Self::IndList(_, _, _, _) => "an ind-List-expression".to_owned(),
            Self::Vec(_, _) => "a Vec type".to_owned(),
            Self::VecNil => "the empty Vec vecnil".to_owned(),
            Self::VecCons(_, _) => "a vec::-expression".to_owned(),
            Self::VecHead(_) => "a head-expression".to_owned(),
            Self::VecTail(_) => "a tail-expression".to_owned(),
            Self::IndVec(_, _, _, _, _) => "an ind-Vec-expression".to_owned(),
            Self::Eq(_, _, _) => "an =>-expression".to_owned(),
            Self::Same(_) => "a same-expression".to_owned(),
            Self::Symm(_) => "a symm-expression".to_owned(),
            Self::Cong(_, _) => "a cong-expression".to_owned(),
            Self::Replace(_, _, _) => "a replace-expression".to_owned(),
            Self::Trans(_, _) => "a trans-expression".to_owned(),
            Self::IndEq(_, _, _) => "an ind-Eq-expression".to_owned(),
            Self::Either(_, _) => "an Either type".to_owned(),
            Self::EitherLeft(_) => "a left-expression".to_owned(),
            Self::EitherRight(_) => "a right-expression".to_owned(),
            Self::IndEither(_, _, _, _) => "an ind-Either-expression".to_owned(),
            Self::Trivial => "Trivial".to_owned(),
            Self::Sole => "sole".to_owned(),
            Self::Absurd => "Absurd".to_owned(),
            Self::IndAbsurd(_, _) => "an ind-Absurd-expression".to_owned(),
            Self::U => "U".to_owned(),
            Self::Todo => "a TODO marker".to_owned(),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Core {
    The(Box<Core>, Box<Core>),
    Var(Symbol),
    Atom,
    Tick(Symbol),
    Sigma(Symbol, Box<Core>, Box<Core>),
    Cons(Box<Core>, Box<Core>),
    Car(Box<Core>),
    Cdr(Box<Core>),
    Pi(Symbol, Box<Core>, Box<Core>),
    Lambda(Symbol, Box<Core>),
    App(Box<Core>, Box<Core>),
    Nat,
    Zero,
    Add1(Box<Core>),
    WhichNat(Box<Core>, Box<Core>, Box<Core>, Box<Core>),
    IterNat(Box<Core>, Box<Core>, Box<Core>, Box<Core>),
    RecNat(Box<Core>, Box<Core>, Box<Core>, Box<Core>),
    IndNat(Box<Core>, Box<Core>, Box<Core>, Box<Core>),
    List(Box<Core>),
    ListNil,
    ListCons(Box<Core>, Box<Core>),
    RecList(Box<Core>, Box<Core>, Box<Core>, Box<Core>),
    IndList(Box<Core>, Box<Core>, Box<Core>, Box<Core>),
    Vec(Box<Core>, Box<Core>),
    VecNil,
    VecCons(Box<Core>, Box<Core>),
    VecHead(Box<Core>),
    VecTail(Box<Core>),
    IndVec(Box<Core>, Box<Core>, Box<Core>, Box<Core>, Box<Core>),
    Eq(Box<Core>, Box<Core>, Box<Core>),
    Same(Box<Core>),
    Symm(Box<Core>),
    Cong(Box<Core>, Box<Core>, Box<Core>),
    Replace(Box<Core>, Box<Core>, Box<Core>),
    Trans(Box<Core>, Box<Core>),
    IndEq(Box<Core>, Box<Core>, Box<Core>),
    Either(Box<Core>, Box<Core>),
    Left(Box<Core>),
    Right(Box<Core>),
    IndEither(Box<Core>, Box<Core>, Box<Core>, Box<Core>),
    Trivial,
    Sole,
    Absurd,
    IndAbsurd(Box<Core>, Box<Core>),
    U,
    Todo(Loc, Box<Core>),
}

enum TopLevel<T> {
    Claim(Located<Symbol>, T),
    Define(Located<Symbol>, T),
    CheckSame(T, T, T),
    Example(T),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Atom,
    Tick(Symbol),
    Sigma(Symbol, Box<Value>, Closure<Value>),
    Cons(Box<Value>, Box<Value>),
    Pi(Symbol, Box<Value>, Closure<Value>),
    Lambda(Symbol, Closure<Value>),
    Nat,
    Zero,
    Add1(Box<Value>),
    List(Box<Value>),
    ListNil,
    ListCons(Box<Value>, Box<Value>),
    Vec(Box<Value>, Box<Value>),
    VecNil,
    VecCons(Box<Value>, Box<Value>),
    Eq(Box<Value>, Box<Value>, Box<Value>),
    Same(Box<Value>),
    Either(Box<Value>, Box<Value>),
    Left(Box<Value>),
    Right(Box<Value>),
    Trivial,
    Sole,
    Absurd,
    U,
    Neu(Box<Value>, Box<Neutral>),
}

impl Value {
    pub fn as_pi(&self) -> Result<(&Symbol, &Box<Value>, &Closure<Value>), Value> {
        match self {
            Value::Pi(x, a, b) => Ok((x, a, b)),
            _ => Err(self.clone()),
        }
    }

    pub fn as_sigma(&self) -> Result<(&Symbol, &Box<Value>, &Closure<Value>), Value> {
        match self {
            Value::Sigma(x, a, b) => Ok((x, a, b)),
            _ => Err(self.clone()),
        }
    }

    pub fn as_list(&self) -> Result<&Box<Value>, Value> {
        match self {
            Value::List(e) => Ok(e),
            _ => Err(self.clone()),
        }
    }

    pub fn as_vec(&self) -> Result<(&Box<Value>, &Box<Value>), Value> {
        match self {
            Value::Vec(e, l) => Ok((e, l)),
            _ => Err(self.clone()),
        }
    }

    pub fn as_eq(&self) -> Result<(&Box<Value>, &Box<Value>, &Box<Value>), Value> {
        match self {
            Value::Eq(t, from, to) => Ok((t, from, to)),
            _ => Err(self.clone()),
        }
    }

    pub fn as_either(&self) -> Result<(&Box<Value>, &Box<Value>), Value> {
        match self {
            Value::Either(a, b) => Ok((a, b)),
            _ => Err(self.clone()),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Neutral {
    Var(Symbol),
    Car(Box<Neutral>),
    Cdr(Box<Neutral>),
    App(Box<Neutral>, Normal),
    WhichNat(Box<Neutral>, Normal, Normal),
    IterNat(Box<Neutral>, Normal, Normal),
    RecNat(Box<Neutral>, Normal, Normal),
    IndNat(Box<Neutral>, Normal, Normal, Normal),
    RecList(Box<Neutral>, Normal, Normal),
    IndList(Box<Neutral>, Normal, Normal, Normal),
    Head(Box<Neutral>),
    Tail(Box<Neutral>),
    IndVec12(Box<Neutral>, Box<Neutral>, Normal, Normal, Normal),
    IndVec2(Normal, Box<Neutral>, Normal, Normal, Normal),
    Symm(Box<Neutral>),
    Cong(Box<Neutral>, Normal),
    Replace(Box<Neutral>, Normal, Normal),
    Trans1(Box<Neutral>, Normal),
    Trans2(Normal, Box<Neutral>),
    Trans12(Box<Neutral>, Box<Neutral>),
    IndEq(Box<Neutral>, Normal, Normal),
    IndEither(Box<Neutral>, Normal, Normal, Normal),
    IndAbsurd(Box<Neutral>, Normal),
    Todo(Loc, Value),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Normal {
    The(Value, Value),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Closure<T> {
    pub env: Env<T>,
    pub expr: Core,
}

pub type Env<T> = Vec<(Symbol, T)>;

#[derive(Debug)]
pub enum MessagePart<T> {
    Text(String),
    Val(T),
}

#[derive(Clone)]
pub enum ElabInfo {
    ExprHasType(Core),
    ExprIsType,
    ExprWillHaveType(Core),
    ClaimAt(Loc),
    BoundAt(Loc),
    ExampleOut(Core),
    FoundTodo(Vec<(Symbol, Option<Loc>, Core)>, Core),
}

#[derive(Debug)]
pub struct ElabErr(Located<Vec<MessagePart<Core>>>);
