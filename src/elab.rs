use crate::{
    alpha_equiv::{alpha_equiv, Equiv},
    fresh::freshen,
    normalize::{self, Norm},
    types::{
        Closure, Core, ElabErr, ElabInfo, Env, Expr, ExprAt, Loc, Located, Neutral, Normal, Symbol,
        Value,
    },
};

#[derive(Debug)]
pub enum Error {
    Normalize(normalize::Error),
    Elab(ElabErr),
    UnknownVariable(Symbol, Vec<Symbol>),
    NotSame(Core, Core, Option<(Core, Core)>),
    NotSameType(Core, Core, Option<(Core, Core)>),
    CheckLambdaExpectedPi(Value),
    CheckSameExpectedEq(Value),
    CheckConsExpectedSigma(Value),
    CheckListNilExpectedList(Value),
    CheckVecNilExpectedVec(Value),
    VecNilWrongLength(Core),
    CheckVecConsExpectedVec(Value),
    VecConsNotAdd1(Core),
    CheckEitherLeftExpectedEither(Value),
    CheckEitherRightExpectedEither(Value),
    SynthAppNotPiType(Core),
    InvalidAtom,
    CarNotSigma(Core),
    CdrNotSigma(Core),
    CantSynth(ExprAt<Loc>),
    SynthSymmNotEqType(Core),
    SynthReplaceNotEqType(Core),
    SynthTransLeftNotEqType(Core),
    SynthTransRightNotEqType(Core),
    SynthCongNotArrowType(Core),
    SynthCongNotEqType(Core),
    SynthRecListNotListType(Core),
    SynthIndEitherNotEitherType(Core),
    SynthVecHeadEmpty(Core),
    SynthVecHeadNotVec(Core),
    SynthVecTailEmpty(Core),
    SynthVecTailNotVec(Core),
    SynthIndVecExpectedVec(Core),
    SynthIndListNotList(Core),
}

type Result<T, E = Error> = std::result::Result<T, E>;

#[derive(Clone, Debug)]
enum ContextEntry<T> {
    HasType(Option<Loc>, T),
    Claimed(Loc, T),
    Defined(Loc, T, T),
}

impl<T> ContextEntry<T> {
    fn entry_type(&self) -> &T {
        match self {
            ContextEntry::HasType(_, t) => t,
            ContextEntry::Defined(_, t, _) => t,
            ContextEntry::Claimed(_, t) => t,
        }
    }

    fn in_scope(&self) -> bool {
        !matches!(self, ContextEntry::Claimed(_, _))
    }
}

#[derive(Clone, Debug)]
struct Context<T>(Vec<(Symbol, ContextEntry<T>)>);

impl<T> Context<T> {
    fn names(&self) -> Vec<Symbol> {
        self.0.iter().map(|(name, _)| name).cloned().collect()
    }
}

impl Context<Value> {
    fn to_env(&self) -> Env<Value> {
        self.0
            .iter()
            .filter_map(|(x, e)| match e {
                ContextEntry::HasType(_, t) => Some((
                    x.clone(),
                    Value::Neu(Box::new(t.clone()), Box::new(Neutral::Var(x.clone()))),
                )),
                ContextEntry::Defined(_, _, d) => Some((x.clone(), d.clone())),
                ContextEntry::Claimed(_, _) => None,
            })
            .collect::<Vec<(Symbol, Value)>>()
            .into()
    }
}

#[derive(Clone)]
pub struct Elab {
    context: Context<Value>,
    loc: Loc,
    ren: Vec<(Symbol, Symbol)>,
    logs: Vec<Located<ElabInfo>>,
}

impl Elab {
    pub fn new(loc: Loc) -> Self {
        Self {
            context: Context(Vec::new()),
            loc,
            ren: Vec::new(),
            logs: Vec::new(),
        }
    }

    fn log_info(&mut self, t: ElabInfo) -> Result<()> {
        let loc = self.loc.clone();
        self.logs.push(Located { loc, t });
        Ok(())
    }

    fn fresh(&self, x: Symbol) -> Symbol {
        let used = self.context.names();
        freshen(&used, x)
    }

    fn with_context<T, F>(&mut self, x: Symbol, loc: Option<Loc>, t: Value, f: F) -> Result<T>
    where
        F: FnOnce(Self) -> Result<T>,
    {
        let mut sub = self.clone();
        sub.context.0.push((x, ContextEntry::HasType(loc, t)));
        f(sub)
    }

    fn apply_renaming(&mut self, x: &Symbol) -> Result<Symbol> {
        match self.ren.iter().find(|(ren, _)| x == ren) {
            None => Err(Error::UnknownVariable(
                x.clone(),
                self.ren.iter().map(|(ren, _)| ren.clone()).collect(),
            )),
            Some((_, y)) => Ok(y.clone()),
        }
    }

    fn rename(&mut self, from: Symbol, to: Symbol) {
        self.ren.push((from, to));
    }

    fn run_norm(&mut self) -> Norm {
        let used_names = self.context.names();
        let init_env = self.context.to_env();
        Norm::new(used_names, init_env)
    }

    fn eval(&mut self, expr: &Core) -> Result<Value> {
        let mut norm = self.run_norm();
        norm.eval(expr).map_err(Error::Normalize)
    }

    fn eval_in_env(&mut self, env: Env<Value>, c: Core) -> Result<Value> {
        let used_names = self.context.names();
        Norm::new(used_names, env)
            .eval(&c)
            .map_err(Error::Normalize)
    }

    fn car(&mut self, v: Value) -> Result<Value> {
        let norm = self.run_norm();
        norm.car(&v).map_err(Error::Normalize)
    }

    fn apply(&mut self, fun: Value, arg: Value) -> Result<Value> {
        let norm = self.run_norm();
        norm.apply(fun, arg).map_err(Error::Normalize)
    }

    fn apply_many(&mut self, fun: Value, args: Vec<Value>) -> Result<Value> {
        let norm = self.run_norm();
        norm.apply_many(fun, args).map_err(Error::Normalize)
    }

    fn instantiate(&mut self, clos: Closure<Value>, x: Symbol, v: Value) -> Result<Value> {
        let norm = self.run_norm();
        norm.instantiate(clos, x, v).map_err(Error::Normalize)
    }

    fn read_back_type(&mut self, v: &Value) -> Result<Core> {
        let mut norm = self.run_norm();
        norm.read_back_type(v).map_err(Error::Normalize)
    }

    fn read_back(&mut self, n: &Normal) -> Result<Core> {
        let mut norm = self.run_norm();
        norm.read_back(n).map_err(Error::Normalize)
    }

    fn in_expr<T, F>(&self, expr: &Expr, f: F) -> Result<T>
    where
        F: FnOnce(&mut Self, &ExprAt<Loc>) -> Result<T>,
    {
        let mut sub = self.clone();
        sub.loc = expr.loc.clone();
        f(&mut sub, &expr.expr)
    }

    fn is_type(&mut self, expr: &Expr) -> Result<Core> {
        let res = self.in_expr(expr, Elab::is_type_at)?;
        self.in_expr(expr, |elab, _| elab.log_info(ElabInfo::ExprIsType))?;
        Ok(res)
    }

    fn is_type_at(&mut self, expr: &ExprAt<Loc>) -> Result<Core> {
        match expr {
            ExprAt::Atom => Ok(Core::Atom),
            ExprAt::Sigma(as1, d) => {
                let mut elab = self.clone();
                let mut checked_as = Vec::with_capacity(as1.len());
                for (loc, x, a) in as1 {
                    let a = elab.is_type(a)?;
                    let a_v = elab.eval(&a)?;
                    let fresh_x = elab.fresh(x.clone());
                    elab = elab.with_context(fresh_x.clone(), Some(loc.clone()), a_v, Ok)?;
                    elab.rename(x.clone(), fresh_x);
                    checked_as.push((x, a));
                }
                let mut acc = elab.is_type(d)?;
                for (x, a) in checked_as.into_iter().rev() {
                    acc = Core::Sigma(x.clone(), a.into(), acc.into());
                }
                Ok(acc)
            }
            ExprAt::Pair(a, d) => {
                let x = self.fresh("x".into());
                let a = self.is_type(a)?;
                let a_val = self.eval(&a)?;
                let d = self.with_context(x.clone(), None, a_val, |mut elab| elab.is_type(d))?;
                Ok(Core::Sigma(x, a.into(), d.into()))
            }
            ExprAt::Pi(args, r) => {
                let mut elab = self.clone();
                let mut checked_args = Vec::with_capacity(args.len());
                for (loc, x, arg) in args {
                    let arg = elab.is_type(arg)?;
                    let arg_val = elab.eval(&arg)?;
                    let fresh_x = elab.fresh(x.clone());
                    elab = elab.with_context(fresh_x.clone(), Some(loc.clone()), arg_val, Ok)?;
                    elab.rename(x.clone(), fresh_x);
                    checked_args.push((x, arg));
                }
                let mut acc = elab.is_type(r)?;
                for (x, arg) in checked_args.into_iter().rev() {
                    acc = Core::Pi(x.clone(), Box::new(arg), Box::new(acc));
                }
                Ok(acc)
            }
            ExprAt::Arrow(arg, ts) => {
                let mut elab = self.clone();
                let mut arg_t = arg;
                let mut checked_rs = Vec::new();
                for t in ts {
                    let x = elab.fresh("x".into());
                    let arg = elab.is_type(arg_t)?;
                    let arg_val = elab.eval(&arg)?;
                    elab = elab.with_context(x.clone(), None, arg_val, Ok)?;
                    checked_rs.push((x, arg));
                    arg_t = t;
                }
                let mut acc = elab.is_type(arg_t)?;
                for (x, r) in checked_rs.into_iter().rev() {
                    acc = Core::Pi(x, r.into(), acc.into());
                }
                Ok(acc)
            }
            ExprAt::Nat => Ok(Core::Nat),
            ExprAt::List(e) => Ok(Core::List(self.is_type(e)?.into())),
            ExprAt::Vec(e, len) => Ok(Core::Vec(
                self.is_type(e)?.into(),
                self.check(&Value::Nat, len)?.into(),
            )),
            ExprAt::Eq(x, from, to) => {
                let x = self.is_type(x)?;
                let x_val = self.eval(&x)?;
                Ok(Core::Eq(
                    Box::new(x),
                    Box::new(self.check(&x_val, from)?),
                    Box::new(self.check(&x_val, to)?),
                ))
            }
            ExprAt::Either(p, s) => Ok(Core::Either(
                self.is_type(p)?.into(),
                self.is_type(s)?.into(),
            )),
            ExprAt::Trivial => Ok(Core::Trivial),
            ExprAt::Absurd => Ok(Core::Absurd),
            ExprAt::U => Ok(Core::U),
            other => self.check_at(&Value::U, other),
        }
    }

    fn find_var(&mut self, x: Symbol) -> Result<Synth> {
        match self
            .context
            .0
            .iter()
            .find(|(y, info)| &x == y && info.in_scope())
        {
            Some((_, info)) => Ok(Synth::The(info.entry_type().clone(), Core::Var(x))),
            None => Err(Error::UnknownVariable(
                x,
                self.context.0.iter().map(|(x, _)| x.clone()).collect(),
            )),
        }
    }

    pub fn synth(&mut self, expr: &Expr) -> Result<Synth> {
        let res = self.in_expr(expr, Elab::synth_at)?;
        let t = self.read_back_type(res.the_type())?;
        self.in_expr(expr, move |elab, _| elab.log_info(ElabInfo::ExprHasType(t)))?;
        Ok(res)
    }

    fn synth_at(&mut self, expr: &ExprAt<Loc>) -> Result<Synth> {
        match expr {
            ExprAt::The(ty, e) => {
                let ty = self.is_type(ty)?;
                let tv = self.eval(&ty)?;
                let e = self.check(&tv, e)?;
                Ok(Synth::The(tv, Core::The(Box::new(ty), Box::new(e))))
            }
            ExprAt::Var(x) => {
                let x = self.apply_renaming(x)?;
                self.find_var(x)
            }
            ExprAt::Tick(sym) => {
                // TODO: Can this even happen with the lexer/parser?
                if sym
                    .name
                    .chars()
                    .all(|c| c.is_ascii_alphabetic() || c == '-')
                    && !sym.name.is_empty()
                {
                    Ok(Synth::The(Value::Atom, Core::Tick(sym.clone())))
                } else {
                    Err(Error::InvalidAtom)
                }
            }
            ExprAt::Car(pr) => {
                let Synth::The(ty, pr) = self.synth(pr)?;
                match ty {
                    Value::Sigma(_x, a_t, _d_t) => Ok(Synth::The(*a_t, Core::Car(pr.into()))),
                    other => {
                        let ty = self.read_back_type(&other)?;
                        Err(Error::CarNotSigma(ty))
                    }
                }
            }
            ExprAt::Cdr(pr) => {
                let Synth::The(ty, pr) = self.synth(pr)?;
                match ty {
                    Value::Sigma(x, _a_t, d_t) => {
                        let a = self.eval(&pr).and_then(|v| self.car(v))?;
                        let d_v = self.instantiate(d_t, x, a)?;
                        Ok(Synth::The(d_v, Core::Cdr(pr.into())))
                    }
                    other => {
                        let ty = self.read_back_type(&other)?;
                        Err(Error::CdrNotSigma(ty))
                    }
                }
            }
            ExprAt::App(f, args) => {
                let Synth::The(mut f_t, mut f) = self.synth(f)?;
                for arg in args {
                    match f_t {
                        Value::Pi(x, dom, ran) => {
                            let arg = self.check(&dom, arg)?;
                            let arg_v = self.eval(&arg)?;
                            let expr_ty = self.instantiate(ran, x, arg_v)?;
                            f_t = expr_ty;
                            f = Core::App(f.into(), arg.into());
                        }
                        other => {
                            let t = self.read_back_type(&other)?;
                            return Err(Error::SynthAppNotPiType(t));
                        }
                    }
                }
                Ok(Synth::The(f_t, f))
            }
            ExprAt::Zero => Ok(Synth::The(Value::Nat, Core::Zero)),
            ExprAt::Add1(n) => {
                let n = self.check(&Value::Nat, n)?;
                Ok(Synth::The(Value::Nat, Core::Add1(Box::new(n))))
            }
            ExprAt::NatLit(n) => {
                let mut acc = Core::Zero;
                for _ in 0..*n {
                    acc = Core::Add1(acc.into());
                }
                Ok(Synth::The(Value::Nat, acc))
            }
            ExprAt::WhichNat(tgt, base, step) => {
                let tgt = self.check(&Value::Nat, tgt)?;
                let Synth::The(bt_v, base) = self.synth(base)?;
                let step_t = self.eval_in_env(
                    Env::default().with("base-type", bt_v.clone()),
                    Core::pi("x", Core::Nat, Core::var("base-type")),
                )?;
                let step = self.check(&step_t, step)?;
                let bt = self.read_back_type(&bt_v)?;
                Ok(Synth::The(
                    bt_v,
                    Core::WhichNat(tgt.into(), bt.into(), base.into(), step.into()),
                ))
            }
            ExprAt::IterNat(tgt, base, step) => {
                let tgt = self.check(&Value::Nat, tgt)?;
                let Synth::The(bt_v, base) = self.synth(base)?;
                let step_t = self.eval_in_env(
                    Env::default().with("base-type", bt_v.clone()),
                    Core::pi("x", Core::var("base-type"), Core::var("base-type")),
                )?;
                let step = self.check(&step_t, step)?;
                let bt = self.read_back_type(&bt_v)?;
                Ok(Synth::The(
                    bt_v,
                    Core::IterNat(tgt.into(), bt.into(), base.into(), step.into()),
                ))
            }
            ExprAt::RecNat(tgt, base, step) => {
                let tgt = self.check(&Value::Nat, tgt)?;
                let Synth::The(bt_v, base) = self.synth(base)?;
                let step_t = self.eval_in_env(
                    Env::default().with("base-type", bt_v.clone()),
                    Core::pi(
                        "n",
                        Core::Nat,
                        Core::pi("x", Core::var("base-type"), Core::var("base-type")),
                    ),
                )?;
                let step = self.check(&step_t, step)?;
                let bt = self.read_back_type(&bt_v)?;
                Ok(Synth::The(
                    bt_v,
                    Core::RecNat(tgt.into(), bt.into(), base.into(), step.into()),
                ))
            }
            ExprAt::IndNat(tgt, mot, base, step) => {
                let tgt = self.check(&Value::Nat, tgt)?;
                let mot = self.check(
                    &Value::Pi("x".into(), Value::Nat.into(), Closure::new(Core::U)),
                    mot,
                )?;
                let mot_v = self.eval(&mot)?;
                let base_t = self.apply(mot_v.clone(), Value::Zero)?;
                let base = self.check(&base_t, base)?;
                let step_t = self.eval_in_env(
                    Env::default().with("mot", mot_v.clone()),
                    Core::pi(
                        "k",
                        Core::Nat,
                        Core::pi(
                            "almost",
                            Core::App(Core::var("mot").into(), Core::var("k").into()),
                            Core::App(
                                Core::var("mot").into(),
                                Core::Add1(Core::var("k").into()).into(),
                            ),
                        ),
                    ),
                )?;
                let step = self.check(&step_t, step)?;
                let tgt_v = self.eval(&tgt)?;
                let ty = self.apply(mot_v, tgt_v)?;
                Ok(Synth::The(
                    ty,
                    Core::IndNat(tgt.into(), mot.into(), base.into(), step.into()),
                ))
            }
            ExprAt::ListCons(e, es) => {
                let Synth::The(et, e) = self.synth(e)?;
                let es = self.check(&Value::List(et.clone().into()), es)?;
                Ok(Synth::The(
                    Value::List(et.into()),
                    Core::ListCons(e.into(), es.into()),
                ))
            }
            ExprAt::RecList(tgt, base, step) => {
                let Synth::The(lst_t, tgt) = self.synth(tgt)?;
                match lst_t {
                    Value::List(et) => {
                        let Synth::The(bt_v, base) = self.synth(base)?;
                        let step_t = self.eval_in_env(
                            Env::default()
                                .with("E", *et)
                                .with("base-type", bt_v.clone()),
                            Core::pi(
                                "e",
                                Core::var("E"),
                                Core::pi(
                                    "es",
                                    Core::List(Core::var("E").into()),
                                    Core::pi(
                                        "almost",
                                        Core::var("base-type"),
                                        Core::var("base-type"),
                                    ),
                                ),
                            ),
                        )?;
                        let step = self.check(&step_t, step)?;
                        let bt = self.read_back_type(&bt_v)?;
                        Ok(Synth::The(
                            bt_v,
                            Core::RecList(tgt.into(), bt.into(), base.into(), step.into()),
                        ))
                    }
                    other => {
                        let t = self.read_back_type(&other)?;
                        Err(Error::SynthRecListNotListType(t))
                    }
                }
            }
            ExprAt::IndList(tgt, mot, base, step) => {
                let Synth::The(lst_t, tgt) = self.synth(tgt)?;
                match lst_t {
                    Value::List(elem) => {
                        let mot_t = self.eval_in_env(
                            Env::default().with("E", *elem.clone()),
                            Core::pi("es", Core::List(Core::var("E").into()), Core::U),
                        )?;
                        let mot = self.check(&mot_t, mot)?;
                        let mot_v = self.eval(&mot)?;
                        let base_t = self.eval_in_env(
                            Env::default().with("mot", mot_v.clone()),
                            Core::App(Core::var("mot").into(), Core::ListNil.into()),
                        )?;
                        let base = self.check(&base_t, base)?;
                        let step_t = self.eval_in_env(
                            Env::default().with("E", *elem).with("mot", mot_v.clone()),
                            Core::pi(
                                "e",
                                Core::var("E"),
                                Core::pi(
                                    "es",
                                    Core::List(Core::var("E").into()),
                                    Core::pi(
                                        "so-far",
                                        Core::App(Core::var("mot").into(), Core::var("es").into()),
                                        Core::App(
                                            Core::var("mot").into(),
                                            Core::ListCons(
                                                Core::var("e").into(),
                                                Core::var("es").into(),
                                            )
                                            .into(),
                                        ),
                                    ),
                                ),
                            ),
                        )?;
                        let step = self.check(&step_t, step)?;
                        let tgt_v = self.eval(&tgt)?;
                        let ty = self.apply(mot_v, tgt_v)?;
                        Ok(Synth::The(
                            ty,
                            Core::IndList(tgt.into(), mot.into(), base.into(), step.into()),
                        ))
                    }
                    other => {
                        let t = self.read_back_type(&other)?;
                        Err(Error::SynthIndListNotList(t))
                    }
                }
            }
            ExprAt::VecHead(es) => {
                let Synth::The(es_t, es) = self.synth(es)?;
                match es_t {
                    Value::Vec(elem_t, len) => match *len {
                        Value::Add1(k) => Ok(Synth::The(*elem_t, Core::VecHead(es.into()))),
                        other => {
                            let len = self.read_back(&Normal::The(Value::Nat, other))?;
                            Err(Error::SynthVecHeadEmpty(len))
                        }
                    },
                    other => {
                        let t = self.read_back_type(&other)?;
                        Err(Error::SynthVecHeadNotVec(t))
                    }
                }
            }
            ExprAt::VecTail(es) => {
                let Synth::The(es_t, es) = self.synth(es)?;
                match es_t {
                    Value::Vec(elem_t, len) => match *len {
                        Value::Add1(k) => {
                            Ok(Synth::The(Value::Vec(elem_t, k), Core::VecTail(es.into())))
                        }
                        other => {
                            let len = self.read_back(&Normal::The(Value::Nat, other))?;
                            Err(Error::SynthVecTailEmpty(len))
                        }
                    },
                    other => {
                        let t = self.read_back_type(&other)?;
                        Err(Error::SynthVecTailNotVec(t))
                    }
                }
            }
            ExprAt::IndVec(len, es, mot, base, step) => {
                let len = self.check(&Value::Nat, len)?;
                let len_v = self.eval(&len)?;
                let Synth::The(es_t, es) = self.synth(es)?;
                match es_t {
                    Value::Vec(elem, vec_len) => {
                        self.same(&Value::Nat, &len_v, &vec_len)?;
                        let mot_t = self.eval_in_env(
                            Env::default().with("E", *elem.clone()),
                            Core::pi(
                                "k",
                                Core::Nat,
                                Core::pi(
                                    "es",
                                    Core::Vec(Core::var("E").into(), Core::var("k").into()),
                                    Core::U,
                                ),
                            ),
                        )?;
                        let mot = self.check(&mot_t, mot)?;
                        let mot_v = self.eval(&mot)?;
                        let base_t =
                            self.apply_many(mot_v.clone(), vec![Value::Zero, Value::VecNil])?;
                        let base = self.check(&base_t, base)?;
                        let step_t = self.eval_in_env(
                            Env::default().with("E", *elem).with("mot", mot_v.clone()),
                            Core::pi(
                                "k",
                                Core::Nat,
                                Core::pi(
                                    "e",
                                    Core::var("E"),
                                    Core::pi(
                                        "es",
                                        Core::Vec(Core::var("E").into(), Core::var("K").into()),
                                        Core::pi(
                                            "so-far",
                                            Core::App(
                                                Core::App(
                                                    Core::var("mot").into(),
                                                    Core::var("k").into(),
                                                )
                                                .into(),
                                                Core::var("es").into(),
                                            ),
                                            Core::App(
                                                Core::App(
                                                    Core::var("mot").into(),
                                                    Core::Add1(Core::var("k").into()).into(),
                                                )
                                                .into(),
                                                Core::VecCons(
                                                    Core::var("e").into(),
                                                    Core::var("es").into(),
                                                )
                                                .into(),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        )?;
                        let step = self.check(&step_t, step)?;
                        let len_v = self.eval(&len)?;
                        let es_v = self.eval(&es)?;
                        let ty = self.apply_many(mot_v, vec![len_v, es_v])?;
                        Ok(Synth::The(
                            ty,
                            Core::IndVec(
                                len.into(),
                                es.into(),
                                mot.into(),
                                base.into(),
                                step.into(),
                            ),
                        ))
                    }
                    other => {
                        let t = self.read_back_type(&other)?;
                        Err(Error::SynthIndVecExpectedVec(t))
                    }
                }
            }
            ExprAt::Replace(tgt, mot, base) => {
                let Synth::The(tgt_t, tgt) = self.synth(tgt)?;
                match tgt_t {
                    Value::Eq(a, from, to) => {
                        let mot_t = self.eval_in_env(
                            Env::default().with("A", *a.clone()),
                            Core::pi("x", Core::var("A"), Core::U),
                        )?;
                        let mot = self.check(&mot_t, mot)?;
                        let mot_v = self.eval(&mot)?;
                        let base_t = self.apply(mot_v.clone(), *from)?;
                        let base = self.check(&base_t, base)?;
                        let ty = self.apply(mot_v, *to)?;
                        Ok(Synth::The(
                            ty,
                            Core::Replace(tgt.into(), mot.into(), base.into()),
                        ))
                    }
                    _ => {
                        let t = self.read_back_type(&tgt_t)?;
                        Err(Error::SynthReplaceNotEqType(t))
                    }
                }
            }
            ExprAt::Cong(tgt, fun) => {
                let Synth::The(tgt_t, tgt) = self.synth(tgt)?;
                let Synth::The(fun_t, fun) = self.synth(fun)?;
                match (tgt_t, fun_t) {
                    (Value::Eq(ty, from, to), Value::Pi(x, dom, ran)) => {
                        self.same_type(&ty, &dom)?;
                        let ran = self.instantiate(ran, x, *from.clone())?;
                        let fun_v = self.eval(&fun)?;
                        let new_from = self.apply(fun_v.clone(), *from)?;
                        let new_to = self.apply(fun_v, *to)?;
                        let ty = self.read_back_type(&ran)?;
                        Ok(Synth::The(
                            Value::Eq(ran.into(), new_from.into(), new_to.into()),
                            Core::Cong(tgt.into(), ty.into(), fun.into()),
                        ))
                    }
                    (Value::Eq(_, _, _), other) => {
                        let t = self.read_back_type(&other)?;
                        Err(Error::SynthCongNotArrowType(t))
                    }
                    (other, _) => {
                        let t = self.read_back_type(&other)?;
                        Err(Error::SynthCongNotEqType(t))
                    }
                }
            }
            ExprAt::Symm(tgt) => {
                let Synth::The(tgt_t, tgt) = self.synth(tgt)?;
                match tgt_t {
                    Value::Eq(a, from, to) => {
                        Ok(Synth::The(Value::Eq(a, to, from), Core::Symm(tgt.into())))
                    }
                    _ => {
                        let t = self.read_back_type(&tgt_t)?;
                        Err(Error::SynthSymmNotEqType(t))
                    }
                }
            }
            ExprAt::Trans(p1, p2) => {
                let Synth::The(t1, p1) = self.synth(p1)?;
                let Synth::The(t2, p2) = self.synth(p2)?;
                match (t1, t2) {
                    (Value::Eq(a, from, mid_l), Value::Eq(b, mid_r, to)) => {
                        self.same_type(&a, &b)?;
                        self.same(&a, &mid_l, &mid_r)?;
                        Ok(Synth::The(
                            Value::Eq(a, from, to),
                            Core::Trans(p1.into(), p2.into()),
                        ))
                    }
                    (Value::Eq(_, _, _), t2) => {
                        let not_eq = self.read_back_type(&t2)?;
                        Err(Error::SynthTransRightNotEqType(not_eq))
                    }
                    (t1, Value::Eq(_, _, _)) => {
                        let not_eq = self.read_back_type(&t1)?;
                        Err(Error::SynthTransLeftNotEqType(not_eq))
                    }
                    (t1, _) => {
                        let not_eq = self.read_back_type(&t1)?;
                        Err(Error::SynthTransLeftNotEqType(not_eq))
                    }
                }
            }
            ExprAt::IndEq(_, _, _) => todo!(),
            ExprAt::IndEither(tgt, mot, l, r) => {
                let Synth::The(tgt_t, tgt) = self.synth(tgt)?;
                match tgt_t {
                    Value::Either(lt, rt) => {
                        let mot_t = self.eval_in_env(
                            Env::default().with("L", *lt.clone()).with("R", *rt.clone()),
                            Core::pi(
                                "x",
                                Core::Either(Core::var("L").into(), Core::var("R").into()),
                                Core::U,
                            ),
                        )?;
                        let mot = self.check(&mot_t, mot)?;
                        let mot_v = self.eval(&mot)?;
                        let lm_t = self.eval_in_env(
                            Env::default().with("L", *lt).with("mot", mot_v.clone()),
                            Core::pi(
                                "l",
                                Core::var("L"),
                                Core::App(
                                    Core::var("mot").into(),
                                    Core::Left(Core::var("l").into()).into(),
                                ),
                            ),
                        )?;
                        let l = self.check(&lm_t, l)?;
                        let rm_t = self.eval_in_env(
                            Env::default().with("R", *rt).with("mot", mot_v.clone()),
                            Core::pi(
                                "r",
                                Core::var("R"),
                                Core::App(
                                    Core::var("mot").into(),
                                    Core::Right(Core::var("r").into()).into(),
                                ),
                            ),
                        )?;
                        let r = self.check(&rm_t, r)?;
                        let tgt_v = self.eval(&tgt)?;
                        let ty = self.eval_in_env(
                            Env::default().with("tgt", tgt_v).with("mot", mot_v),
                            Core::App(Core::var("mot").into(), Core::var("tgt").into()),
                        )?;
                        Ok(Synth::The(
                            ty,
                            Core::IndEither(tgt.into(), mot.into(), l.into(), r.into()),
                        ))
                    }
                    other => {
                        let t = self.read_back_type(&other)?;
                        Err(Error::SynthIndEitherNotEitherType(t))
                    }
                }
            }
            ExprAt::Sole => Ok(Synth::The(Value::Trivial, Core::Sole)),
            ExprAt::IndAbsurd(tgt, mot) => {
                let tgt = self.check(&Value::Absurd, tgt)?;
                let mot = self.check(&Value::U, mot)?;
                let mot_v = self.eval(&mot)?;
                Ok(Synth::The(mot_v, Core::IndAbsurd(tgt.into(), mot.into())))
            }
            ExprAt::Atom => Ok(Synth::The(Value::U, Core::Atom)),
            ExprAt::Sigma(arg_as, d) => {
                let mut elab = self.clone();
                let mut checked_as = Vec::new();
                for (loc, x, a) in arg_as {
                    let a = elab.check(&Value::U, a)?;
                    let a_val = elab.eval(&a)?;
                    let fresh_x = elab.fresh(x.clone());
                    elab = elab.with_context(fresh_x.clone(), Some(loc.clone()), a_val, Ok)?;
                    elab.rename(x.clone(), fresh_x);
                    checked_as.push((x, a));
                }
                let mut acc = elab.check(&Value::U, d)?;
                for (x, a) in checked_as.into_iter().rev() {
                    acc = Core::Sigma(x.clone(), a.into(), acc.into());
                }
                Ok(Synth::The(Value::U, acc))
            }
            ExprAt::Pair(a, d) => {
                let a = self.check(&Value::U, a)?;
                let a_val = self.eval(&a)?;
                let x = self.fresh("a".into());
                let mut elab = self.with_context(x.clone(), None, a_val, Ok)?;
                let d = elab.check(&Value::U, d)?;
                Ok(Synth::The(Value::U, Core::Sigma(x, a.into(), d.into())))
            }
            ExprAt::Pi(args, ran) => {
                let mut elab = self.clone();
                let mut checked_args = Vec::new();
                for (loc, x, dom) in args {
                    let dom = elab.check(&Value::U, dom)?;
                    let dom_val = elab.eval(&dom)?;
                    let fresh_x = elab.fresh(x.clone());
                    elab = elab.with_context(fresh_x.clone(), Some(loc.clone()), dom_val, Ok)?;
                    elab.rename(x.clone(), fresh_x.clone());
                    checked_args.push((fresh_x, dom));
                }
                let mut acc = elab.check(&Value::U, ran)?;
                for (x, dom) in checked_args.into_iter().rev() {
                    acc = Core::Pi(x.clone(), dom.into(), acc.into());
                }
                Ok(Synth::The(Value::U, acc))
            }
            ExprAt::Arrow(dom, ts) => {
                let mut elab = self.clone();
                let mut checked_ts = Vec::new();
                for t in ts {
                    let x = elab.fresh("x".into());
                    let dom = elab.check(&Value::U, dom)?;
                    let dom_val = elab.eval(&dom)?;
                    elab = elab.with_context(x.clone(), None, dom_val, Ok)?;
                    checked_ts.push((x, dom));
                }
                let mut acc = self.check(&Value::U, dom)?;
                for (x, dom) in checked_ts.into_iter().rev() {
                    acc = Core::Pi(x, dom.into(), acc.into());
                }
                Ok(Synth::The(Value::U, acc))
            }
            ExprAt::Nat => Ok(Synth::The(Value::U, Core::Nat)),
            ExprAt::List(elem) => {
                let elem = self.check(&Value::U, elem)?;
                Ok(Synth::The(Value::U, Core::List(elem.into())))
            }
            ExprAt::Vec(elem, len) => Ok(Synth::The(
                Value::U,
                Core::Vec(
                    self.check(&Value::U, elem)?.into(),
                    self.check(&Value::Nat, len)?.into(),
                ),
            )),
            ExprAt::Eq(ty, from, to) => {
                let ty = self.check(&Value::U, ty)?;
                let tv = self.eval(&ty)?;
                let from = self.check(&tv, from)?;
                let to = self.check(&tv, to)?;
                Ok(Synth::The(
                    Value::U,
                    Core::Eq(ty.into(), from.into(), to.into()),
                ))
            }
            ExprAt::Either(l, r) => {
                let l = self.check(&Value::U, l)?;
                let r = self.check(&Value::U, r)?;
                Ok(Synth::The(Value::U, Core::Either(l.into(), r.into())))
            }
            ExprAt::Trivial => Ok(Synth::The(Value::U, Core::Trivial)),
            ExprAt::Absurd => Ok(Synth::The(Value::U, Core::Absurd)),
            e => Err(Error::CantSynth(e.clone())),
        }
    }

    fn check(&mut self, t: &Value, e: &Expr) -> Result<Core> {
        let res = self.in_expr(e, |elab, e| elab.check_at(t, e))?;
        let tc = self.read_back_type(t)?;
        self.in_expr(e, move |elab, _| elab.log_info(ElabInfo::ExprHasType(tc)))?;
        Ok(res)
    }

    fn check_at(&mut self, t: &Value, e: &ExprAt<Loc>) -> Result<Core> {
        match e {
            ExprAt::Cons(a, d) => {
                let (x, a_t, d_t) = t.as_sigma().map_err(Error::CheckConsExpectedSigma)?;
                let a = self.check(a_t, a)?;
                let a_v = self.eval(&a)?;
                let d_t = self.instantiate(d_t.clone(), x.clone(), a_v)?;
                let d = self.check(&d_t, d)?;
                Ok(Core::Cons(a.into(), d.into()))
            }
            ExprAt::Lambda(xs, body) => {
                let mut elab = self.clone();
                let mut t = t.clone();
                let mut zs = Vec::new();
                for (loc, x) in xs.iter() {
                    let (y, dom, ran) = t.as_pi().map_err(Error::CheckLambdaExpectedPi)?;
                    let z = elab.fresh(x.clone());
                    elab = elab.with_context(z.clone(), Some(loc.clone()), *dom.clone(), Ok)?;
                    let body_t = elab.instantiate(
                        ran.clone(),
                        y.clone(),
                        Value::Neu(dom.clone(), Box::new(Neutral::Var(z.clone()))),
                    )?;
                    elab.rename(x.clone(), z.clone());
                    zs.push(z);
                    t = body_t;
                }
                let mut out = None;
                for z in zs.iter().rev() {
                    match out {
                        Some(cur) => {
                            out = Some(Core::Lambda(z.clone(), Box::new(cur)));
                        }
                        None => {
                            let body = elab.check(&t, body)?;
                            out = Some(Core::Lambda(z.clone(), Box::new(body)));
                        }
                    }
                }
                Ok(out.unwrap())
            }
            ExprAt::ListNil => {
                let _ = t.as_list().map_err(Error::CheckListNilExpectedList)?;
                Ok(Core::ListNil)
            }
            ExprAt::VecNil => {
                let (_, len) = t.as_vec().map_err(Error::CheckVecNilExpectedVec)?;
                match *len.clone() {
                    Value::Zero => Ok(Core::VecNil),
                    other_len => {
                        let len = self.read_back(&Normal::The(Value::Nat, other_len))?;
                        Err(Error::VecNilWrongLength(len))
                    }
                }
            }
            ExprAt::VecCons(e, es) => {
                let (elem, len) = t.as_vec().map_err(Error::CheckVecConsExpectedVec)?;
                match *len.clone() {
                    Value::Add1(k) => Ok(Core::VecCons(
                        self.check(elem, e)?.into(),
                        self.check(&Value::Vec(elem.clone(), k), es)?.into(),
                    )),
                    other_len => {
                        let len = self.read_back(&Normal::The(Value::Nat, other_len))?;
                        Err(Error::VecConsNotAdd1(len))
                    }
                }
            }
            ExprAt::Same(e) => {
                let (ty, from, to) = t.as_eq().map_err(Error::CheckSameExpectedEq)?;
                let e = self.check(ty, e)?;
                let v = self.eval(&e)?;
                self.same(ty, from, &v)?;
                self.same(ty, &v, to)?;
                Ok(Core::Same(Box::new(e)))
            }
            ExprAt::EitherLeft(l) => {
                let (lt, _) = t
                    .as_either()
                    .map_err(Error::CheckEitherLeftExpectedEither)?;
                Ok(Core::Left(self.check(lt, l)?.into()))
            }
            ExprAt::EitherRight(r) => {
                let (_, rt) = t
                    .as_either()
                    .map_err(Error::CheckEitherRightExpectedEither)?;
                Ok(Core::Right(self.check(rt, r)?.into()))
            }
            ExprAt::Todo => {
                let t = self.read_back_type(t)?;
                let loc = self.loc.clone();
                // let ctx =
                todo!()
            }
            other => {
                let Synth::The(other_t, other) = self.synth_at(other)?;
                self.same_type(t, &other_t)?;
                Ok(other)
            }
        }
    }

    pub fn same(&mut self, ty: &Value, v1: &Value, v2: &Value) -> Result<()> {
        let c1 = self.read_back(&Normal::The(ty.clone(), v1.clone()))?;
        let c2 = self.read_back(&Normal::The(ty.clone(), v2.clone()))?;
        match alpha_equiv(&c1, &c2) {
            Equiv::NotEquiv(l, r) => {
                let diff = if l != c1 { Some((l, r)) } else { None };
                Err(Error::NotSame(c1, c2, diff))
            }
            Equiv::Equiv => Ok(()),
        }
    }

    pub fn same_type(&mut self, v1: &Value, v2: &Value) -> Result<()> {
        let c1 = self.read_back_type(v1)?;
        let c2 = self.read_back_type(v2)?;
        match alpha_equiv(&c1, &c2) {
            Equiv::NotEquiv(l, r) => {
                let diff = if l != c1 { Some((l, r)) } else { None };
                Err(Error::NotSameType(c1, c2, diff))
            }
            Equiv::Equiv => Ok(()),
        }
    }
}

#[derive(Debug)]
pub enum Synth {
    The(Value, Core),
}

impl Synth {
    fn the_type(&self) -> &Value {
        let Synth::The(t, _) = &self;
        t
    }
}
