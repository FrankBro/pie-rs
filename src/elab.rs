use crate::{
    alpha_equiv::{alpha_equiv, Equiv},
    fresh::freshen,
    normalize::{self, Norm},
    types::{
        Closure, Core, ElabErr, ElabInfo, Env, Expr, ExprAt, Loc, Located, LocatedExpr,
        MessagePart, Neutral, Normal, Symbol, TypedArg, Value,
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
}

type Result<T, E = Error> = std::result::Result<T, E>;

#[derive(Clone)]
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

#[derive(Clone)]
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
            .collect()
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

    fn with_context(&mut self, x: Symbol, loc: Option<Loc>, t: Value) {
        self.context.0.push((x, ContextEntry::HasType(loc, t)))
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

    fn instantiate(&mut self, clos: Closure<Value>, x: Symbol, v: Value) -> Result<Value> {
        let mut norm = self.run_norm();
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

    fn in_expr<T, F>(&self, expr: &Expr, mut f: F) -> Result<T>
    where
        F: FnOnce(&mut Self, &ExprAt<Loc>) -> Result<T>,
    {
        let mut sub = self.clone();
        sub.loc = expr.loc.clone();
        let res = f(&mut sub, &expr.expr);
        res
    }

    fn is_type(&mut self, expr: &Expr) -> Result<Core> {
        let res = self.in_expr(expr, Elab::is_type_at)?;
        self.in_expr(expr, |elab, _| elab.log_info(ElabInfo::ExprIsType))?;
        Ok(res)
    }

    fn is_type_at(&mut self, expr: &ExprAt<Loc>) -> Result<Core> {
        match expr {
            ExprAt::Atom => Ok(Core::Atom),
            ExprAt::Pair(a, d) => {
                let x = self.fresh("x".into());
                let a = self.is_type(a)?;
                let a_val = self.eval(&a)?;
                self.with_context(x.clone(), None, a_val);
                let d = self.is_type(d)?;
                Ok(Core::Sigma(x, a.into(), d.into()))
            }
            ExprAt::Pi(args, r) => {
                let mut checked_args = Vec::new();
                for arg in args {
                    let (loc, x, arg) = arg;
                    let arg = self.is_type(arg)?;
                    let arg_val = self.eval(&arg)?;
                    let fresh_x = self.fresh(x.clone());
                    self.with_context(fresh_x.clone(), Some(loc.clone()), arg_val);
                    self.rename(x.clone(), fresh_x);
                    checked_args.push((x, arg));
                }
                let mut acc = self.is_type(r)?;
                while let Some((x, arg)) = checked_args.pop() {
                    acc = Core::Pi(x.clone(), Box::new(arg), Box::new(acc));
                }
                Ok(acc)
            }
            ExprAt::Arrow(arg, ts) => {
                let mut checked_rs = Vec::new();
                for t in ts {
                    let x = self.fresh("x".into());
                    let arg = self.is_type(arg)?;
                    let arg_val = self.eval(&arg)?;
                    self.with_context(x.clone(), None, arg_val);
                    let r = self.is_type(t)?;
                    checked_rs.push((x, r));
                }
                let mut acc = self.is_type(arg)?;
                for (x, r) in checked_rs.into_iter().rev() {
                    acc = Core::Pi(x, r.into(), acc.into());
                }
                Ok(acc)
            }
            // isType' (Arrow arg (t:|ts)) =
            //   do x <- fresh (Symbol (T.pack "x"))
            //      arg' <- isType arg
            //      argVal <- eval arg'
            //      r' <- withCtxExtension x Nothing argVal $
            //            case ts of
            //              -- FunF→1
            //              [] ->
            //                isType t
            //              -- FunF→2
            //              (ty : tys) ->
            //                isType' (Arrow t (ty :| tys))
            //      return (CPi x arg' r')
            ExprAt::Eq(x, from, to) => {
                let x = self.is_type(x)?;
                let x_val = self.eval(&x)?;
                Ok(Core::Eq(
                    Box::new(x),
                    Box::new(self.check(&x_val, from)?),
                    Box::new(self.check(&x_val, to)?),
                ))
            }
            ExprAt::Trivial => Ok(Core::Trivial),
            e => todo!("{:?}", e),
        }
    }

    fn find_var(&mut self, x: Symbol) -> Result<Synth> {
        match self
            .context
            .0
            .iter()
            .find(|(y, info)| &x == y && info.in_scope())
        {
            Some((_, info)) => Ok(Synth {
                the_type: info.entry_type().clone(),
                the_expr: Core::Var(x),
            }),
            None => todo!(),
        }
    }

    pub fn synth(&mut self, expr: &Expr) -> Result<Synth> {
        let res = self.in_expr(expr, Elab::synth_at)?;
        let t = self.read_back_type(&res.the_type)?;
        self.in_expr(expr, move |elab, _| elab.log_info(ElabInfo::ExprHasType(t)))?;
        Ok(res)
    }

    fn synth_at(&mut self, expr: &ExprAt<Loc>) -> Result<Synth> {
        match expr {
            ExprAt::The(ty, e) => {
                let ty = self.is_type(ty)?;
                let tv = self.eval(&ty)?;
                let e = self.check(&tv, e)?;
                Ok(Synth {
                    the_type: tv,
                    the_expr: Core::The(Box::new(ty), Box::new(e)),
                })
            }
            ExprAt::Var(x) => {
                let x = self.apply_renaming(x)?;
                self.find_var(x)
            }
            ExprAt::Zero => Ok(Synth {
                the_type: Value::Nat,
                the_expr: Core::Zero,
            }),
            ExprAt::Add1(n) => {
                let n = self.check(&Value::Nat, n)?;
                Ok(Synth {
                    the_type: Value::Nat,
                    the_expr: Core::Add1(Box::new(n)),
                })
            }
            ExprAt::NatLit(n) => {
                if *n == 0 {
                    self.synth_at(&ExprAt::Zero)
                } else {
                    self.synth_at(&ExprAt::Add1(Expr {
                        loc: self.loc.clone(),
                        expr: Box::new(ExprAt::NatLit(*n - 1)),
                    }))
                }
            }
            ExprAt::Sole => Ok(Synth {
                the_type: Value::Trivial,
                the_expr: Core::Sole,
            }),
            ExprAt::Trivial => Ok(Synth {
                the_type: Value::U,
                the_expr: Core::Trivial,
            }),
            e => todo!("{:?}", e),
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
                // When the loop is done, type of the last body
                let mut t = t.clone();
                let mut zs = Vec::new();
                for (loc, x) in xs.iter() {
                    let (y, dom, ran) = t.as_pi().map_err(Error::CheckLambdaExpectedPi)?;
                    let z = self.fresh(x.clone());
                    self.with_context(z.clone(), Some(loc.clone()), *dom.clone());
                    let body_t = self.instantiate(
                        ran.clone(),
                        y.clone(),
                        Value::Neu(dom.clone(), Box::new(Neutral::Var(z.clone()))),
                    )?;
                    self.rename(x.clone(), y.clone());
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
                            let body = self.check(&t, body)?;
                            out = Some(Core::Lambda(z.clone(), Box::new(body)));
                        }
                    }
                }
                Ok(out.unwrap())
            }
            ExprAt::Same(e) => {
                let (ty, from, to) = t.as_eq().map_err(Error::CheckSameExpectedEq)?;
                let e = self.check(ty, e)?;
                let v = self.eval(&e)?;
                self.same(ty, from, &v)?;
                self.same(ty, &v, to)?;
                Ok(Core::Same(Box::new(e)))
            }
            other => {
                let Synth {
                    the_type: other_t,
                    the_expr: other,
                } = self.synth_at(other)?;
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
pub struct Synth {
    pub the_type: Value,
    pub the_expr: Core,
}
