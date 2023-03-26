use std::collections::HashMap;

use crate::types::{Core, Symbol};

pub enum Equiv {
    Equiv,
    NotEquiv(Core, Core),
}

impl Equiv {
    fn and_then<F>(self, then: F) -> Self
    where
        F: FnOnce() -> Self,
    {
        match self {
            Self::Equiv => then(),
            Self::NotEquiv(_, _) => self,
        }
    }
}

pub fn alpha_equiv(e1: &Core, e2: &Core) -> Equiv {
    Env::default().equiv(e1, e2)
}

#[derive(Default)]
struct Env {
    left: HashMap<Symbol, u64>,
    right: HashMap<Symbol, u64>,
    i: u64,
}

impl Env {
    fn with_equiv(&mut self, x: &Symbol, y: &Symbol) -> Equiv {
        self.left.insert(x.clone(), self.i);
        self.right.insert(y.clone(), self.i);
        self.i += 1;
        Equiv::Equiv
    }

    fn equiv_vars(&self, x: &Symbol, y: &Symbol) -> Equiv {
        match (self.left.get(x), self.right.get(y)) {
            (None, None) => {
                if x == y {
                    Equiv::Equiv
                } else {
                    Equiv::NotEquiv(Core::Var(x.clone()), Core::Var(y.clone()))
                }
            }
            (Some(i), Some(j)) => {
                if i == j {
                    Equiv::Equiv
                } else {
                    Equiv::NotEquiv(Core::Var(x.clone()), Core::Var(y.clone()))
                }
            }
            _ => Equiv::NotEquiv(Core::Var(x.clone()), Core::Var(y.clone())),
        }
    }

    fn equiv(&mut self, e1: &Core, e2: &Core) -> Equiv {
        let require = |b: bool| -> Equiv {
            if b {
                Equiv::Equiv
            } else {
                Equiv::NotEquiv(e1.clone(), e2.clone())
            }
        };
        match (e1, e2) {
            (Core::Tick(x), Core::Tick(y)) => require(*x == *y),
            (Core::Atom, Core::Atom) => Equiv::Equiv,
            (Core::Zero, Core::Zero) => Equiv::Equiv,
            (Core::Add1(j), Core::Add1(k)) => self.equiv(j, k),
            (Core::WhichNat(tg1, bt1, base1, step1), Core::WhichNat(tg2, bt2, base2, step2)) => {
                self.equiv(tg1, tg2)
                    .and_then(|| self.equiv(bt1, bt2))
                    .and_then(|| self.equiv(base1, base2))
                    .and_then(|| self.equiv(step1, step2))
            }
            (Core::IterNat(tgt1, bt1, base1, step1), Core::IterNat(tgt2, bt2, base2, step2)) => {
                self.equiv(tgt1, tgt2)
                    .and_then(|| self.equiv(bt1, bt2))
                    .and_then(|| self.equiv(base1, base2))
                    .and_then(|| self.equiv(step1, step2))
            }
            (Core::RecNat(tgt1, bt1, base1, step1), Core::RecNat(tgt2, bt2, base2, step2)) => self
                .equiv(tgt1, tgt2)
                .and_then(|| self.equiv(bt1, bt2))
                .and_then(|| self.equiv(base1, base2))
                .and_then(|| self.equiv(step1, step2)),
            (Core::IndNat(tgt1, mot1, base1, step1), Core::IndNat(tgt2, mot2, base2, step2)) => {
                self.equiv(tgt1, tgt2)
                    .and_then(|| self.equiv(mot1, mot2))
                    .and_then(|| self.equiv(base1, base2))
                    .and_then(|| self.equiv(step1, step2))
            }
            (Core::Nat, Core::Nat) => Equiv::Equiv,
            (Core::Var(x), Core::Var(y)) => self.equiv_vars(x, y),
            (Core::Pi(x, dom1, ran1), Core::Pi(y, dom2, ran2)) => self
                .equiv(dom1, dom2)
                .and_then(|| self.with_equiv(x, y))
                .and_then(|| self.equiv(ran1, ran2)),
            (Core::Lambda(x, body1), Core::Lambda(y, body2)) => {
                self.with_equiv(x, y).and_then(|| self.equiv(body1, body2))
            }
            (Core::App(rator1, rand1), Core::App(rator2, rand2)) => self
                .equiv(rator1, rator2)
                .and_then(|| self.equiv(rand1, rand2)),
            (Core::Sigma(x, a1, d1), Core::Sigma(y, a2, d2)) => self
                .equiv(a1, a2)
                .and_then(|| self.with_equiv(x, y))
                .and_then(|| self.equiv(d1, d2)),
            (Core::Cons(a1, d1), Core::Cons(a2, d2)) => {
                self.equiv(a1, a2).and_then(|| self.equiv(d1, d2))
            }
            (Core::Car(p1), Core::Car(p2)) => self.equiv(p1, p2),
            (Core::Cdr(p1), Core::Cdr(p2)) => self.equiv(p1, p2),
            (Core::Trivial, Core::Trivial) => Equiv::Equiv,
            (Core::Sole, Core::Sole) => Equiv::Equiv,
            (Core::Eq(a, f1, t1), Core::Eq(b, f2, t2)) => self
                .equiv(a, b)
                .and_then(|| self.equiv(f1, f2))
                .and_then(|| self.equiv(t1, t2)),
            (Core::Same(e1), Core::Same(e2)) => self.equiv(e1, e2),
            (Core::Replace(tgt1, mot1, base1), Core::Replace(tgt2, mot2, base2)) => self
                .equiv(tgt1, tgt2)
                .and_then(|| self.equiv(mot1, mot2))
                .and_then(|| self.equiv(base1, base2)),
            (Core::Trans(a1, b1), Core::Trans(a2, b2)) => {
                self.equiv(a1, a2).and_then(|| self.equiv(b1, b2))
            }
            (Core::Cong(a1, b1, c1), Core::Cong(a2, b2, c2)) => self
                .equiv(a1, a2)
                .and_then(|| self.equiv(b1, b2))
                .and_then(|| self.equiv(c1, c2)),
            (Core::Symm(p1), Core::Symm(p2)) => self.equiv(p1, p2),
            (Core::IndEq(tgt1, mot1, base1), Core::IndEq(tgt2, mot2, base2)) => self
                .equiv(tgt1, tgt2)
                .and_then(|| self.equiv(mot1, mot2))
                .and_then(|| self.equiv(base1, base2)),
            (Core::List(e1), Core::List(e2)) => self.equiv(e1, e2),
            (Core::ListNil, Core::ListNil) => Equiv::Equiv,
            (Core::ListCons(e1, es1), Core::ListCons(e2, es2)) => {
                self.equiv(e1, e2).and_then(|| self.equiv(es1, es2))
            }
            (Core::RecList(tgt1, bt1, base1, step1), Core::RecList(tgt2, bt2, base2, step2)) => {
                self.equiv(tgt1, tgt2)
                    .and_then(|| self.equiv(bt1, bt2))
                    .and_then(|| self.equiv(base1, base2))
                    .and_then(|| self.equiv(step1, step2))
            }
            (Core::IndList(tgt1, bt1, base1, step1), Core::IndList(tgt2, bt2, base2, step2)) => {
                self.equiv(tgt1, tgt2)
                    .and_then(|| self.equiv(bt1, bt2))
                    .and_then(|| self.equiv(base1, base2))
                    .and_then(|| self.equiv(step1, step2))
            }
            (Core::Vec(e1, len1), Core::Vec(e2, len2)) => {
                self.equiv(e1, e2).and_then(|| self.equiv(len1, len2))
            }
            (Core::VecNil, Core::VecNil) => Equiv::Equiv,
            (Core::VecCons(e1, es1), Core::VecCons(e2, es2)) => {
                self.equiv(e1, e2).and_then(|| self.equiv(es1, es2))
            }
            (Core::VecHead(es1), Core::VecHead(es2)) => self.equiv(es1, es2),
            (Core::VecTail(es1), Core::VecTail(es2)) => self.equiv(es1, es2),
            (
                Core::IndVec(len1, es1, mot1, base1, step1),
                Core::IndVec(len2, es2, mot2, base2, step2),
            ) => self
                .equiv(len1, len2)
                .and_then(|| self.equiv(es1, es2))
                .and_then(|| self.equiv(mot1, mot2))
                .and_then(|| self.equiv(base1, base2))
                .and_then(|| self.equiv(step1, step2)),
            (Core::Either(l1, r1), Core::Either(l2, r2)) => {
                self.equiv(l1, l2).and_then(|| self.equiv(r1, r2))
            }
            (Core::Left(l1), Core::Left(l2)) => self.equiv(l1, l2),
            (Core::Right(r1), Core::Right(r2)) => self.equiv(r1, r2),
            (
                Core::IndEither(tgt1, mot1, left1, right1),
                Core::IndEither(tgt2, mot2, left2, right2),
            ) => self
                .equiv(tgt1, tgt2)
                .and_then(|| self.equiv(mot1, mot2))
                .and_then(|| self.equiv(left1, left2))
                .and_then(|| self.equiv(right1, right2)),
            (Core::Absurd, Core::Absurd) => Equiv::Equiv,
            (Core::IndAbsurd(tgt1, mot1), Core::IndAbsurd(tgt2, mot2)) => {
                self.equiv(tgt1, tgt2).and_then(|| self.equiv(mot1, mot2))
            }
            // (Core::The(Core::Absurd, _), Core::The(Core::Absurd, _)) => Equiv::Equiv,
            (Core::The(a1, _), Core::The(a2, _))
                if **a1 == Core::Absurd && **a2 == Core::Absurd =>
            {
                Equiv::Equiv
            }
            (Core::The(t1, e1), Core::The(t2, e2)) => {
                self.equiv(t1, t2).and_then(|| self.equiv(e1, e2))
            }
            (Core::U, Core::U) => Equiv::Equiv,
            (Core::Todo(loc1, _), Core::Todo(loc2, _)) => require(loc1 == loc2),
            _ => Equiv::NotEquiv(e1.clone(), e2.clone()),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        alpha_equiv::{alpha_equiv, Equiv},
        types::{Core, Loc, Pos, Symbol},
    };

    #[test]
    fn test_alpha_equiv() {
        fn sym(name: &str) -> Symbol {
            let name = name.to_owned();
            Symbol { name }
        }
        let loc1 = Loc {
            source: "hello.pie".to_owned(),
            start: Pos { line: 1, col: 1 },
            end: Pos { line: 1, col: 5 },
        };
        let loc2 = Loc {
            source: "hello.pie".to_owned(),
            start: Pos { line: 3, col: 4 },
            end: Pos { line: 3, col: 8 },
        };
        fn lambda(name: &str, body: Core) -> Core {
            Core::Lambda(sym(name), Box::new(body))
        }
        fn var(name: &str) -> Core {
            Core::Var(sym(name))
        }
        fn app(e1: Core, e2: Core) -> Core {
            Core::App(Box::new(e1), Box::new(e2))
        }
        let zero = || Core::Zero;
        fn add1(e: Core) -> Core {
            Core::Add1(Box::new(e))
        }
        fn tick(name: &str) -> Core {
            Core::Tick(sym(name))
        };
        let nat = || Core::Nat;
        fn sigma(name: &str, e1: Core, e2: Core) -> Core {
            Core::Sigma(sym(name), Box::new(e1), Box::new(e2))
        }
        fn eq(e1: Core, e2: Core, e3: Core) -> Core {
            Core::Eq(Box::new(e1), Box::new(e2), Box::new(e3))
        }
        fn the(e1: Core, e2: Core) -> Core {
            Core::The(Box::new(e1), Box::new(e2))
        }
        let absurd = || Core::Absurd;
        fn todo(loc: Loc, e: Core) -> Core {
            Core::Todo(loc, Box::new(e))
        }
        fn pi(name: &str, e1: Core, e2: Core) -> Core {
            Core::Pi(sym(name), Box::new(e1), Box::new(e2))
        }
        let cases = &[
            (lambda("x", var("x")), (lambda("x", var("x"))), true),
            (lambda("x", var("x")), (lambda("y", var("y"))), true),
            (
                lambda("x", lambda("y", var("x"))),
                lambda("x", lambda("y", var("x"))),
                true,
            ),
            (
                lambda("x", lambda("y", var("x"))),
                lambda("y", lambda("z", var("y"))),
                true,
            ),
            (
                lambda("x", lambda("y", var("x"))),
                lambda("y", lambda("z", var("z"))),
                false,
            ),
            (
                lambda("x", lambda("y", var("x"))),
                lambda("y", lambda("x", var("x"))),
                false,
            ),
            (lambda("x", var("x")), lambda("y", var("x")), false),
            (var("x"), var("x"), true),
            (var("x"), var("y"), false),
            (app(var("f"), var("x")), app(var("f"), var("x")), true),
            (app(var("f"), var("x")), app(var("g"), var("x")), false),
            (
                lambda("f", app(var("f"), var("x"))),
                lambda("g", app(var("g"), var("x"))),
                true,
            ),
            (zero(), zero(), true),
            (add1(zero()), add1(zero()), true),
            (tick("rugbrød"), tick("rugbrød"), true),
            (tick("rugbrød"), tick("rundstykker"), false),
            (
                sigma(
                    "half",
                    nat(),
                    eq(nat(), var("n"), app(var("double"), var("half"))),
                ),
                sigma(
                    "blurgh",
                    nat(),
                    eq(nat(), var("n"), app(var("double"), var("blurgh"))),
                ),
                true,
            ),
            (
                sigma(
                    "half",
                    nat(),
                    eq(nat(), var("n"), app(var("double"), var("half"))),
                ),
                sigma(
                    "half",
                    nat(),
                    eq(nat(), var("n"), app(var("twice"), var("half"))),
                ),
                false,
            ),
            (the(absurd(), var("x")), the(absurd(), var("x")), true),
            (the(absurd(), var("x")), the(absurd(), var("y")), true),
            (
                the(absurd(), var("x")),
                the(absurd(), app(var("find-the-proof"), var("x"))),
                true,
            ),
            (todo(loc1.clone(), nat()), todo(loc1.clone(), nat()), true),
            (todo(loc1, nat()), todo(loc2, nat()), false),
            (zero(), var("naught"), false),
            (
                pi("n", nat(), eq(nat(), var("n"), var("n"))),
                pi("m", nat(), eq(nat(), var("m"), var("m"))),
                true,
            ),
            (
                pi("n", nat(), eq(nat(), var("n"), var("n"))),
                pi("m", nat(), eq(nat(), var("n"), var("n"))),
                false,
            ),
            (
                pi("n", nat(), eq(nat(), var("n"), var("n"))),
                sigma("m", nat(), eq(nat(), var("m"), var("m"))),
                false,
            ),
        ];
        for (left, right, res) in cases {
            let act = match alpha_equiv(left, right) {
                Equiv::Equiv => true,
                Equiv::NotEquiv(_, _) => false,
            };
            assert_eq!(*res, act, "{:?} α≡? {:?}", left, right);
        }
    }
}
