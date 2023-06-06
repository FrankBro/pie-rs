use crate::{
    alpha_equiv::{alpha_equiv, Equiv},
    fresh::freshen,
    types::{Closure, Core, Env, Neutral, Normal, Symbol, Value},
};

#[derive(Debug)]
pub enum Error {
    NotAFunction(Value),
    VarNotFound(Symbol),
    BadCar(Value),
    BadCdr(Value),
    ReadBackNeutralMismatchedTypes(Core, Core),
}

type Result<T, E = Error> = std::result::Result<T, E>;

#[derive(Default)]
pub struct Norm {
    bound: Vec<Symbol>,
    env: Env<Value>,
}

impl Norm {
    pub fn new(bound: Vec<Symbol>, env: Env<Value>) -> Self {
        Self { bound, env }
    }

    fn with_env(&self, env: Env<Value>) -> Norm {
        Self {
            bound: self.bound.clone(),
            env,
        }
    }

    fn in_bound(&mut self, x: Symbol) {
        self.bound.push(x)
    }

    fn fresh(&self, x: &str) -> Symbol {
        freshen(&self.bound, x.into())
    }

    fn close(&self, expr: Core) -> Closure<Value> {
        let env = self.env.clone();
        Closure { env, expr }
    }

    pub fn instantiate(&self, clos: Closure<Value>, x: Symbol, v: Value) -> Result<Value> {
        let mut env = clos.env.clone();
        env.push((x, v));
        self.with_env(env).eval(&clos.expr)
    }

    fn var(&self, x: &Symbol) -> Result<Value> {
        match self.env.iter().find(|(y, v)| x == y) {
            Some((_, v)) => Ok(v.clone()),
            None => Err(Error::VarNotFound(x.clone())),
        }
    }

    pub fn eval(&mut self, core: &Core) -> Result<Value> {
        match core {
            Core::Tick(x) => Ok(Value::Tick(x.clone())),
            Core::Atom => Ok(Value::Atom),
            Core::Zero => Ok(Value::Zero),
            Core::Add1(n) => Ok(Value::Add1(Box::new(self.eval(n)?))),
            Core::WhichNat(tgt, ty, base, step) => {
                let tgtv = self.eval(tgt)?;
                let tyv = self.eval(ty)?;
                let basev = self.eval(base)?;
                let stepv = self.eval(step)?;
                self.which_nat(tgtv, tyv, basev, stepv)
            }
            Core::IterNat(tgt, ty, base, step) => {
                let tgtv = self.eval(tgt)?;
                let tyv = self.eval(ty)?;
                let basev = self.eval(base)?;
                let stepv = self.eval(step)?;
                self.iter_nat(tgtv, tyv, basev, stepv)
            }
            Core::RecNat(tgt, ty, base, step) => {
                let tgtv = self.eval(tgt)?;
                let tyv = self.eval(ty)?;
                let basev = self.eval(base)?;
                let stepv = self.eval(step)?;
                self.rec_nat(tgtv, tyv, basev, stepv)
            }
            Core::IndNat(tgt, mot, base, step) => {
                let tgtv = self.eval(tgt)?;
                let motv = self.eval(mot)?;
                let basev = self.eval(base)?;
                let stepv = self.eval(step)?;
                self.ind_nat(tgtv, motv, basev, stepv)
            }
            Core::Nat => Ok(Value::Nat),
            Core::Var(x) => self.var(x),
            Core::Pi(x, dom, ran) => Ok(Value::Pi(
                x.clone(),
                Box::new(self.eval(dom)?),
                self.close(*ran.clone()),
            )),
            Core::Lambda(x, body) => Ok(Value::Lambda(x.clone(), self.close(*body.clone()))),
            Core::App(rator, rand) => {
                let fun = self.eval(rator)?;
                let arg = self.eval(rand)?;
                self.apply(fun, arg)
            }
            Core::Sigma(x, a, d) => Ok(Value::Sigma(
                x.clone(),
                self.eval(a)?.into(),
                self.close(*d.clone()),
            )),
            Core::Cons(a, d) => Ok(Value::Cons(self.eval(a)?.into(), self.eval(d)?.into())),
            Core::Trivial => Ok(Value::Trivial),
            Core::Sole => Ok(Value::Sole),
            Core::Eq(ty, from, to) => Ok(Value::Eq(
                Box::new(self.eval(ty)?),
                Box::new(self.eval(from)?),
                Box::new(self.eval(to)?),
            )),
            Core::Same(e) => Ok(Value::Same(Box::new(self.eval(e)?))),
            Core::List(elem) => Ok(Value::List(self.eval(elem)?.into())),
            Core::ListNil => Ok(Value::ListNil),
            Core::The(_, e) => self.eval(e),
            e => todo!("{:?}", e),
        }
    }

    fn apply(&self, f: Value, arg: Value) -> Result<Value> {
        match f {
            Value::Lambda(x, clos) => self.instantiate(clos, x, arg),
            Value::Neu(v, f) => match *v {
                Value::Pi(x, a, b) => Ok(Value::Neu(
                    Box::new(self.instantiate(b, x, arg.clone())?),
                    Box::new(Neutral::App(f, Normal::The(*a, arg))),
                )),
                _ => unreachable!(),
            },
            other => Err(Error::NotAFunction(other)),
        }
    }

    fn car(&self, v: &Value) -> Result<Value> {
        match v {
            Value::Cons(a, _) => Ok(*a.clone()),
            Value::Neu(sig, ne) => match *sig.clone() {
                Value::Sigma(_, a_t, _) => Ok(Value::Neu(a_t, Neutral::Car(ne.clone()).into())),
                _ => Err(Error::BadCar(v.clone())),
            },
            _ => Err(Error::BadCar(v.clone())),
        }
    }

    fn cdr(&self, v: &Value) -> Result<Value> {
        match v {
            Value::Cons(_, d) => Ok(*d.clone()),
            Value::Neu(sig, ne) => match *sig.clone() {
                Value::Sigma(x, _, d_t) => {
                    let a = self.car(v)?;
                    let t = self.instantiate(d_t, x, a)?;
                    Ok(Value::Neu(t.into(), Neutral::Cdr(ne.clone()).into()))
                }
                _ => Err(Error::BadCdr(v.clone())),
            },
            _ => Err(Error::BadCdr(v.clone())),
        }
    }

    fn which_nat(&self, tgt: Value, t: Value, base: Value, step: Value) -> Result<Value> {
        match tgt {
            Value::Zero => Ok(base),
            Value::Add1(k) => self.apply(step, *k),
            Value::Neu(v, ne) => match *v {
                Value::Nat => {
                    let ty_name = self.fresh("ty");
                    let k = self.fresh("k");
                    let core =
                        Core::Pi(k, Box::new(Core::Nat), Box::new(Core::Var(ty_name.clone())));
                    let step_ty = self.with_env(vec![(ty_name, t.clone())]).eval(&core)?;
                    Ok(Value::Neu(
                        Box::new(t.clone()),
                        Box::new(Neutral::WhichNat(
                            ne,
                            Normal::The(t, base),
                            Normal::The(step_ty, step),
                        )),
                    ))
                }
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }

    fn iter_nat(&self, tgt: Value, t: Value, base: Value, step: Value) -> Result<Value> {
        match tgt {
            Value::Zero => Ok(base),
            Value::Add1(k) => {
                let so_far = self.iter_nat(*k, t, base, step.clone())?;
                self.apply(step, so_far)
            }
            Value::Neu(v, ne) => match *v {
                Value::Nat => {
                    let ty_name = self.fresh("ty");
                    let k = self.fresh("k");
                    let core = Core::Pi(
                        k,
                        Box::new(Core::Var(ty_name.clone())),
                        Box::new(Core::Var(ty_name.clone())),
                    );
                    let step_ty = self.with_env(vec![(ty_name, t.clone())]).eval(&core)?;
                    Ok(Value::Neu(
                        Box::new(t.clone()),
                        Box::new(Neutral::IterNat(
                            ne,
                            Normal::The(t, base),
                            Normal::The(step_ty, step),
                        )),
                    ))
                }
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }

    fn rec_nat(&self, tgt: Value, t: Value, base: Value, step: Value) -> Result<Value> {
        match tgt {
            Value::Zero => Ok(base),
            Value::Add1(k) => {
                let so_far = self.rec_nat(*k.clone(), t, base, step.clone())?;
                let step_k = self.apply(step, *k)?;
                self.apply(step_k, so_far)
            }
            Value::Neu(v, ne) => match *v {
                Value::Nat => {
                    let ty_name = self.fresh("ty");
                    let k = self.fresh("k");
                    let x = self.fresh("x");
                    let core = Core::Pi(
                        k,
                        Box::new(Core::Nat),
                        Box::new(Core::Pi(
                            x,
                            Box::new(Core::Var(ty_name.clone())),
                            Box::new(Core::Var(ty_name.clone())),
                        )),
                    );
                    let step_ty = self.with_env(vec![(ty_name, t.clone())]).eval(&core)?;
                    Ok(Value::Neu(
                        Box::new(t.clone()),
                        Box::new(Neutral::RecNat(
                            ne,
                            Normal::The(t, base),
                            Normal::The(step_ty, step),
                        )),
                    ))
                }
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }

    fn ind_nat(&self, tgt: Value, mot: Value, base: Value, step: Value) -> Result<Value> {
        match tgt.clone() {
            Value::Zero => Ok(base),
            Value::Add1(k) => {
                let so_far = self.ind_nat(*k.clone(), mot, base, step.clone())?;
                let this_step = self.apply(step, *k)?;
                self.apply(this_step, so_far)
            }
            Value::Neu(v, ne) => match *v {
                Value::Nat => {
                    let t = self.apply(mot.clone(), tgt)?;
                    let k = self.fresh("k");
                    let mot_ty = Value::Pi(
                        k.clone(),
                        Box::new(Value::Nat),
                        Closure {
                            env: Vec::new(),
                            expr: Core::U,
                        },
                    );
                    let base_ty = self.apply(mot.clone(), Value::Zero)?;
                    let so_far = self.fresh("so-far");
                    let mot_name = self.fresh("mot");
                    let core = Core::Pi(
                        k.clone(),
                        Box::new(Core::Nat),
                        Box::new(Core::Pi(
                            so_far,
                            Box::new(Core::App(
                                Box::new(Core::Var(mot_name.clone())),
                                Box::new(Core::Var(k.clone())),
                            )),
                            Box::new(Core::App(
                                Box::new(Core::Var(mot_name.clone())),
                                Box::new(Core::Add1(Box::new(Core::Var(k)))),
                            )),
                        )),
                    );
                    let step_ty = self.with_env(vec![(mot_name, mot.clone())]).eval(&core)?;
                    Ok(Value::Neu(
                        Box::new(t),
                        Box::new(Neutral::IndNat(
                            ne,
                            Normal::The(mot_ty, mot),
                            Normal::The(base_ty, base),
                            Normal::The(step_ty, step),
                        )),
                    ))
                }
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }

    pub fn read_back(&mut self, n: &Normal) -> Result<Core> {
        match n {
            Normal::The(Value::Atom, Value::Tick(x)) => Ok(Core::Tick(x.clone())),
            Normal::The(Value::Nat, Value::Zero) => Ok(Core::Zero),
            Normal::The(Value::Nat, Value::Add1(k)) => self
                .read_back(&Normal::The(Value::Nat, *k.clone()))
                .map(|k| Core::Add1(Box::new(k))),
            Normal::The(Value::Pi(x, dom, ran), fun) => {
                let y = self.fresh(base_name(x, fun));
                let y_val = Value::Neu(dom.clone(), Box::new(Neutral::Var(y.clone())));
                let body_val = self.apply(fun.clone(), y_val.clone())?;
                let body_type = self.instantiate(ran.clone(), x.clone(), y_val)?;
                let body = self.read_back(&Normal::The(body_type, body_val))?;
                Ok(Core::Lambda(y, Box::new(body)))
            }
            Normal::The(Value::Sigma(x, a_t, d_t), p) => {
                let a_v = self.car(p)?;
                let a = self.read_back(&Normal::The(*a_t.clone(), a_v.clone()))?;
                let d_t = self.instantiate(d_t.clone(), x.clone(), a_v)?;
                let d_v = self.cdr(p)?;
                let d = self.read_back(&Normal::The(d_t, d_v))?;
                Ok(Core::Cons(a.into(), d.into()))
            }
            Normal::The(Value::Trivial, _) => Ok(Core::Sole),
            Normal::The(Value::Eq(ty, _, _), Value::Same(v)) => Ok(Core::Same(Box::new(
                self.read_back(&Normal::The(*ty.clone(), *v.clone()))?,
            ))),
            Normal::The(Value::List(_), Value::ListNil) => Ok(Core::ListNil),
            Normal::The(Value::List(t), Value::ListCons(a, d)) => Ok(Core::ListCons(
                self.read_back(&Normal::The(*t.clone(), *a.clone()))?.into(),
                self.read_back(&Normal::The(Value::List(t.clone()), *d.clone()))?
                    .into(),
            )),
            // readBack (NThe (VList t) (VListCons a d)) =
            //   CListCons <$> readBack (NThe t a) <*> readBack (NThe (VList t) d)
            Normal::The(Value::Absurd, Value::Neu(_, ne)) => Ok(Core::The(
                Box::new(Core::Absurd),
                Box::new(self.read_back_neutral(ne)?),
            )),
            Normal::The(t1, Value::Neu(t2, neu)) => {
                let t1 = self.read_back_type(t1)?;
                let t2 = self.read_back_type(t2)?;
                match alpha_equiv(&t1, &t2) {
                    Equiv::Equiv => self.read_back_neutral(neu),
                    Equiv::NotEquiv(_, _) => Err(Error::ReadBackNeutralMismatchedTypes(t1, t2)),
                }
            }
            e => todo!("{:?}", e),
        }
    }

    pub fn read_back_type(&mut self, v: &Value) -> Result<Core> {
        match v {
            Value::Atom => Ok(Core::Atom),
            Value::Nat => Ok(Core::Nat),
            Value::Pi(x, dom, ran) => {
                let y = self.fresh(&x.name);
                let ran_v = self.instantiate(
                    ran.clone(),
                    x.clone(),
                    Value::Neu(dom.clone(), Box::new(Neutral::Var(y.clone()))),
                )?;
                self.in_bound(y.clone());
                Ok(Core::Pi(
                    y,
                    Box::new(self.read_back_type(dom)?),
                    Box::new(self.read_back_type(&ran_v)?),
                ))
            }
            Value::Sigma(x, a, d) => {
                let y = self.fresh(&x.name);
                let d_v = self.instantiate(
                    d.clone(),
                    x.clone(),
                    Value::Neu(a.clone(), Neutral::Var(y.clone()).into()),
                )?;
                let a = self.read_back_type(a)?;
                self.in_bound(y.clone());
                let d_v = self.read_back_type(&d_v)?;
                Ok(Core::Sigma(y, a.into(), d_v.into()))
            }
            Value::Trivial => Ok(Core::Absurd),
            Value::Eq(t, from, to) => Ok(Core::Eq(
                self.read_back_type(t)?.into(),
                self.read_back(&Box::new(Normal::The(*t.clone(), *from.clone())))?
                    .into(),
                self.read_back(&Box::new(Normal::The(*t.clone(), *to.clone())))?
                    .into(),
            )),
            Value::List(elem) => Ok(Core::List(self.read_back_type(elem)?.into())),
            Value::U => Ok(Core::U),
            e => todo!("{:?}", e),
        }
    }

    fn read_back_neutral(&mut self, n: &Neutral) -> Result<Core> {
        match n {
            Neutral::Var(x) => Ok(Core::Var(x.clone())),
            Neutral::WhichNat(tgt, base @ Normal::The(t, _), step) => Ok(Core::WhichNat(
                self.read_back_neutral(tgt)?.into(),
                self.read_back_type(t)?.into(),
                self.read_back(base)?.into(),
                self.read_back(step)?.into(),
            )),
            Neutral::IterNat(tgt, base @ Normal::The(t, _), step) => Ok(Core::IterNat(
                self.read_back_neutral(tgt)?.into(),
                self.read_back_type(t)?.into(),
                self.read_back(base)?.into(),
                self.read_back(step)?.into(),
            )),
            Neutral::App(neu, arg) => Ok(Core::App(
                self.read_back_neutral(neu)?.into(),
                self.read_back(arg)?.into(),
            )),
            e => todo!("{:?}", e),
        }
    }
}

fn base_name<'a>(def: &'a Symbol, v: &'a Value) -> &'a str {
    match v {
        Value::Lambda(x, _) => &x.name,
        _ => &def.name,
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        elab::{Elab, Synth},
        parse::parse_expr,
        types::{Closure, Core, Loc, Pos, Value},
    };

    use super::Norm;

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

    #[test]
    fn test_synth_arrow() {
        let input = "(the (-> (-> Nat Nat) (-> Nat Nat)) (lambda (f) (lambda (x) (f x))))";
        let input_expr = parse_expr(SOURCE, input).unwrap();
        let Synth {
            the_type: actual_ty,
            the_expr: actual_core,
        } = elab().synth(&input_expr).unwrap();
        let expected_ty = Value::Pi(
            "x".into(),
            Value::Pi(
                "x".into(),
                Value::Nat.into(),
                Closure {
                    env: Vec::new(),
                    expr: Core::Nat,
                },
            )
            .into(),
            Closure {
                env: Vec::new(),
                expr: Core::Pi("x₁".into(), Core::Nat.into(), Core::Nat.into()),
            },
        );
        assert_eq!(expected_ty, actual_ty);
        let expected_core = Core::The(
            Core::Pi(
                "x".into(),
                Core::Pi("x".into(), Core::Nat.into(), Core::Nat.into()).into(),
                Core::Pi("x₁".into(), Core::Nat.into(), Core::Nat.into()).into(),
            )
            .into(),
            Core::Lambda(
                "f".into(),
                Core::Lambda(
                    "x".into(),
                    Core::App(Core::Var("f".into()).into(), Core::Var("x".into()).into()).into(),
                )
                .into(),
            )
            .into(),
        );
        assert_eq!(expected_core, actual_core);
    }

    #[test]
    fn test_synth_lambda() {
        let input = "(the (Pi ((x Trivial) (y Trivial)) (= Trivial x y)) (lambda (x y) (same x)))";
        let input_expr = parse_expr(SOURCE, input).unwrap();
        let Synth {
            the_type: actual_ty,
            the_expr: actual_core,
        } = elab().synth(&input_expr).unwrap();
        let expected_ty = Value::Pi(
            "x".into(),
            Value::Trivial.into(),
            Closure {
                env: Vec::new(),
                expr: Core::Pi(
                    "y".into(),
                    Box::new(Core::Trivial),
                    Box::new(Core::Eq(
                        Box::new(Core::Trivial),
                        Box::new(Core::Var("x".into())),
                        Box::new(Core::Var("y".into())),
                    )),
                ),
            },
        );
        assert_eq!(expected_ty, actual_ty);
        let expected_core = Core::The(
            Box::new(Core::Pi(
                "x".into(),
                Box::new(Core::Trivial),
                Box::new(Core::Pi(
                    "y".into(),
                    Box::new(Core::Trivial),
                    Box::new(Core::Eq(
                        Box::new(Core::Trivial),
                        Box::new(Core::Var("x".into())),
                        Box::new(Core::Var("y".into())),
                    )),
                )),
            )),
            Box::new(Core::Lambda(
                "x".into(),
                Box::new(Core::Lambda(
                    "y".into(),
                    Box::new(Core::Same(Box::new(Core::Var("x".into())))),
                )),
            )),
        );
        assert_eq!(expected_core, actual_core);
    }

    #[test]
    fn test_norm() {
        let cases = &[
            /*
            ("(the Trivial sole)", "sole"),
            ("4", "(add1 (add1 (add1 (add1 zero))))"),
            (
                "(the (Pi ((x Trivial) (y Trivial)) (= Trivial x y)) (lambda (x y) (same x)))",
                "(the (Pi ((x Trivial) (y Trivial)) (= Trivial x y)) (lambda (x y) (same sole)))",
            ),
            (
                "(the (Pi ((x (Pair Trivial Trivial))) (Pair Trivial Trivial)) (lambda (x) x))",
                "(the (Pi ((y (Pair Trivial Trivial))) (Pair Trivial Trivial)) (lambda (z) (cons sole sole)))"
            ),
            (
                "(the (-> (-> Trivial Trivial) (-> Trivial Trivial)) (lambda (x) x))",
                "(the (-> (-> Trivial Trivial) (-> Trivial Trivial)) (lambda (f) (lambda (x) sole)))"
            ),
            (
                "(the (-> (-> Nat Nat) (-> Nat Nat)) (lambda (x) x))",
                "(the (-> (-> Nat Nat) (-> Nat Nat)) (lambda (f) (lambda (x) (f x))))",
            ),
            (
                "(the (-> (-> Nat Nat) Nat Nat) (lambda (f x) (f x)))",
                "(the (-> (-> Nat Nat) Nat Nat) (lambda (f x) (f x)))"
            ),
            ("(which-Nat zero 't (lambda (x) 'nil))", "(the Atom 't)"),
            ("(which-Nat 13 't (lambda (x) 'nil))", "(the Atom 'nil)"),
            (
                "(the (-> Nat Atom) (lambda (n) (which-Nat n 't (lambda (x) 'nil))))",
                "(the (-> Nat Atom) (lambda (n) (which-Nat n 't (lambda (x) 'nil))))"
            ),
            ("(iter-Nat zero 3 (lambda (x) (add1 x)))" , "(the Nat 3)"),
            ("(iter-Nat 2 3 (lambda (x) (add1 x)))" , "(the Nat 5)"),
            (
                "(the (-> Nat Nat Nat) (lambda (j k) (iter-Nat j k (lambda (x) (add1 x)))))",
                "(the (-> Nat Nat Nat) (lambda (j k) (iter-Nat j k (lambda (x) (add1 x)))))"
            ),
            */
            (
                "(rec-Nat zero (the (List Nat) nil) (lambda (n-1 almost) (:: n-1 almost)))",
                "(the (List Nat) nil)",
            ),
            /*
            (
                "(rec-Nat 3 (the (List Nat) nil) (lambda (n-1 almost) (:: n-1 almost)))",
                "(the (List Nat) (:: 2 (:: 1 (:: 0 nil))))"
            ),
            (
                "(the (-> Nat (List Nat)) (lambda (n) (rec-Nat n (the (List Nat) nil) (lambda (n-1 almost) (:: n-1 almost)))))",
                "(the (-> Nat (List Nat)) (lambda (n) (rec-Nat n (the (List Nat) nil) (lambda (n-1 almost) (:: n-1 almost)))))"
            ),
            (
                "(ind-Nat zero (lambda (k) (Vec Nat k)) vecnil (lambda (n-1 almost) (vec:: n-1 almost)))",
                "(the (Vec Nat 0) vecnil)"
            ),
            (
                "(ind-Nat 2 (lambda (k) (Vec Nat k)) vecnil (lambda (n-1 almost) (vec:: n-1 almost)))",
                "(the (Vec Nat 2) (vec:: 1 (vec:: 0 vecnil)))"
            ),
            (
                "(the (Pi ((n Nat)) (Vec Nat n)) (lambda (j) (ind-Nat j (lambda (k) (Vec Nat k)) vecnil (lambda (n-1 almost) (vec:: n-1 almost)))))",
                "(the (Pi ((n Nat)) (Vec Nat n)) (lambda (j) (ind-Nat j (lambda (k) (Vec Nat k)) vecnil (lambda (n-1 almost) (vec:: n-1 almost)))))"
            ),
            (
                "(the (-> (Sigma ((x Atom)) (= Atom x 'syltetøj)) Atom) (lambda (p) (car p)))",
                "(the (-> (Sigma ((x Atom)) (= Atom x 'syltetøj)) Atom) (lambda (p) (car p)))"
            ),
            ("(car (the (Pair Nat Nat) (cons 2 3)))", "2"),
            ("(cdr (the (Pair Nat Nat) (cons 2 3)))", "3"),
            (
                "(the (Pi ((p (Sigma ((x Atom)) (= Atom x 'syltetøj)))) (= Atom (car p) 'syltetøj)) (lambda (p) (cdr p)))",
                "(the (Pi ((p (Sigma ((x Atom)) (= Atom x 'syltetøj)))) (= Atom (car p) 'syltetøj)) (lambda (p) (cdr p)))"
            ),
            (
                "(the (-> (Pair Trivial Nat) (Pair Trivial Nat)) (lambda (x) x))",
                "(the (-> (Pair Trivial Nat) (Pair Trivial Nat)) (lambda (x) (cons sole (cdr x))))"
            ),
            ("(the Trivial sole)", "(the Trivial sole)"),
            (
                "(the (Pi ((t1 Trivial) (t2 Trivial)) (= Trivial t1 t2)) (lambda (t1 t2) (same t1)))",
                "(the (Pi ((t1 Trivial) (t2 Trivial)) (= Trivial t1 t2)) (lambda (t1 t2) (same sole)))"
            ),
            ("(the (= Nat 0 0) (same 0))", "(the (= Nat 0 0) (same 0))"),
            (
                "(the (Pi ((n Nat)) (-> (= Nat n 0) (= Nat 0 n))) (lambda (n eq) (symm eq)))",
                "(the (Pi ((n Nat)) (-> (= Nat n 0) (= Nat 0 n))) (lambda (n eq) (symm eq)))"
            ),
            (
                "(the (Pi ((j Nat) (n Nat)) (-> (= Nat n j) (= Nat j n))) (lambda (j n eq) (replace eq (lambda (k) (= Nat k n)) (same n))))",
                "(the (Pi ((j Nat) (n Nat)) (-> (= Nat n j) (= Nat j n))) (lambda (j n eq) (replace eq (lambda (k) (= Nat k n)) (same n))))"
            ),
            (
                "((the (Pi ((j Nat) (n Nat)) (-> (= Nat n j) (= Nat j n))) (lambda (j n eq) (replace eq (lambda (k) (= Nat k n)) (same n)))) 0 0 (same 0))",
                "(the (= Nat 0 0) (same 0))"
            ),
            (
                "(the (Pi ((i Nat) (j Nat) (k Nat)) (-> (= Nat i j) (= Nat j k) (= Nat i k))) (lambda (i j k a b) (trans a b)))",
                "(the (Pi ((i Nat) (j Nat) (k Nat)) (-> (= Nat i j) (= Nat j k) (= Nat i k))) (lambda (i j k a b) (trans a b)))"
            ),
            (
                "(trans (the (= Nat 2 2) (same 2)) (the (= Nat 2 2) (same 2)))",
                "(the (= Nat 2 2) (same 2))"
            ),
            (
                "(the (-> (= Nat 0 0) (= Nat 0 0)) (lambda (eq1) (trans eq1 (the (= Nat 0 0) (same 0)))))",
                "(the (-> (= Nat 0 0) (= Nat 0 0)) (lambda (eq1) (trans eq1 (the (= Nat 0 0) (same 0)))))"
            ),
            (
                "(the (-> (= Nat 0 0) (= Nat 0 0)) (lambda (eq1) (trans (the (= Nat 0 0) (same 0)) eq1)))",
                "(the (-> (= Nat 0 0) (= Nat 0 0)) (lambda (eq1) (trans (the (= Nat 0 0) (same 0)) eq1)))"
            ),
            (
                "(the (Pi ((j Nat) (k Nat) (f (-> Nat Atom))) (-> (= Nat j k) (= Atom (f j) (f k)))) (lambda (j k f eq) (cong eq f)))",
                "(the (Pi ((j Nat) (k Nat) (f (-> Nat Atom))) (-> (= Nat j k) (= Atom (f j) (f k)))) (lambda (j k f eq) (cong eq f)))"
            ),
            ("(rec-List (the (List Atom) nil) 0 (lambda (_ _ l) (add1 l)))" , "(the Nat 0)"),
            ("(rec-List (the (List Atom) (:: 'a (:: 'b nil))) 0 (lambda (_ _ l) (add1 l)))" , "(the Nat 2)"),
            (
                "(the (Pi ((E U)) (-> (List E) Nat)) (lambda (E es) (rec-List es 0 (lambda (_ _ l) (add1 l)))))",
                "(the (Pi ((E U)) (-> (List E) Nat)) (lambda (E es) (rec-List es 0 (lambda (_ _ l) (add1 l)))))"
            ),
            (
                "(the (Pi ((P U) (S U)) (-> (Either P S) (Either S P))) (lambda (P S x) (ind-Either x (lambda (ig) (Either S P)) (lambda (l) (right l)) (lambda (r) (left r)))))",
                "(the (Pi ((P U) (S U)) (-> (Either P S) (Either S P))) (lambda (P S x) (ind-Either x (lambda (ig) (Either S P)) (lambda (l) (right l)) (lambda (r) (left r)))))"
            ),
            (
                "(the (-> Absurd (= Nat 1 2)) (lambda (x) (ind-Absurd x (= Nat 1 2))))",
                "(the (-> Absurd (= Nat 1 2)) (lambda (x) (ind-Absurd (the Absurd x) (= Nat 1 2))))"
            ),
            (
                "(the (Pi ((len Nat)) (-> (Vec Atom (add1 (add1 (add1 len)))) Atom)) (lambda (len es) (head (tail (tail es)))))",
                "(the (Pi ((len Nat)) (-> (Vec Atom (add1 (add1 (add1 len)))) Atom)) (lambda (len es) (head (tail (tail es)))))"
            ),
            (
                "(the (Pi ((len Nat) (es (Vec Atom len))) (= (Vec Atom (add1 len)) (vec:: 'prickly-pear es) (vec:: 'prickly-pear es))) (lambda (len es) (ind-Vec len es (lambda (k xs) (= (Vec Atom (add1 k)) (vec:: 'prickly-pear xs) (vec:: 'prickly-pear xs))) (same (vec:: 'prickly-pear vecnil)) (lambda (k x xs so-far) (same (vec:: 'prickly-pear (vec:: x xs)))))))",
                "(the (Pi ((len Nat) (es (Vec Atom len))) (= (Vec Atom (add1 len)) (vec:: 'prickly-pear es) (vec:: 'prickly-pear es))) (lambda (len es) (ind-Vec len es (lambda (k xs) (= (Vec Atom (add1 k)) (vec:: 'prickly-pear xs) (vec:: 'prickly-pear xs))) (same (vec:: 'prickly-pear vecnil)) (lambda (k x xs so-far) (same (vec:: 'prickly-pear (vec:: x xs)))))))"
            ),
            (
                "(the (Pi ((E U) (es (List E))) (= (List E) es (rec-List es (the (List E) nil) (lambda (x xs so-far) (:: x so-far))))) (lambda (E es) (ind-List es (lambda (xs) (= (List E) xs (rec-List xs (the (List E) nil) (lambda (y ys so-far) (:: y so-far))))) (same nil) (lambda (x xs so-far) (cong so-far (the (-> (List E) (List E)) (lambda (tl) (:: x tl))))))))",
                "(the (Pi ((E U) (es (List E))) (= (List E) es (rec-List es (the (List E) nil) (lambda (x xs so-far) (:: x so-far))))) (lambda (E es) (ind-List es (lambda (xs) (= (List E) xs (rec-List xs (the (List E) nil) (lambda (y ys so-far) (:: y so-far))))) (same nil) (lambda (x xs so-far) (cong so-far (the (-> (List E) (List E)) (lambda (tl) (:: x tl))))))))"
            ),
            (
                "((the (Pi ((E U) (es (List E))) (= (List E) es (rec-List es (the (List E) nil) (lambda (x xs so-far) (:: x so-far))))) (lambda (E es) (ind-List es (lambda (xs) (= (List E) xs (rec-List xs (the (List E) nil) (lambda (y ys so-far) (:: y so-far))))) (same nil) (lambda (x xs so-far) (cong so-far (the (-> (List E) (List E)) (lambda (tl) (:: x tl)))))))) Atom nil)",
                "(the (= (List Atom) nil nil) (same nil))"
            ),
            (
                "((the (Pi ((E U) (es (List E))) (= (List E) es (rec-List es (the (List E) nil) (lambda (x xs so-far) (:: x so-far))))) (lambda (E es) (ind-List es (lambda (xs) (= (List E) xs (rec-List xs (the (List E) nil) (lambda (y ys so-far) (:: y so-far))))) (same nil) (lambda (x xs so-far) (cong so-far (the (-> (List E) (List E)) (lambda (tl) (:: x tl)))))))) Atom (:: 'kanelsnegl nil))",
                "(the (= (List Atom) (:: 'kanelsnegl nil) (:: 'kanelsnegl nil)) (same (:: 'kanelsnegl nil)))"
            ),
            (
                "(the U (Pair Nat (Sigma ((x Nat) (f (-> Absurd Trivial Nat))) (= Nat x 13))))",
                "(the U (Pair Nat (Sigma ((x Nat) (f (-> Absurd Trivial Nat))) (= Nat x 13))))"
            ),
            (
                "(the U (-> Atom Nat (Pi ((x Nat) (y (List Nat))) (= Nat x 13))))",
                "(the U (-> Atom Nat (Pi ((x Nat) (y (List Nat))) (= Nat x 13))))"
            ),
            */
        ];
        for (input, normal) in cases {
            let norm_expr = parse_expr(SOURCE, normal).unwrap();
            let input_expr = parse_expr(SOURCE, input).unwrap();
            let Synth {
                the_type: ty1,
                the_expr: norm_core,
            } = elab().synth(&norm_expr).unwrap();
            let Synth {
                the_type: ty2,
                the_expr: input_core,
            } = elab().synth(&input_expr).unwrap();
            elab().same_type(&ty1, &ty2).unwrap();
            let v1 = norm().eval(&norm_core).unwrap();
            let v2 = norm().eval(&input_core).unwrap();
            elab().same(&ty1, &v1, &v2).unwrap()
        }
    }
}
