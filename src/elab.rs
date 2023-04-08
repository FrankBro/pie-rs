use crate::{
    alpha_equiv::{alpha_equiv, Equiv},
    fresh::freshen,
    normalize::{self, Norm},
    types::{
        Core, ElabErr, ElabInfo, Env, Expr, ExprAt, Loc, Located, MessagePart, Neutral, Normal,
        Symbol, Value,
    },
};

#[derive(Debug)]
pub enum Error {
    Normalize(normalize::Error),
    Elab(ElabErr),
    UnknownVariable(Symbol, Vec<Symbol>),
    NotSame(Core, Core, Option<(Core, Core)>),
    NotSameType(Core, Core, Option<(Core, Core)>),
}

type Result<T, E = Error> = std::result::Result<T, E>;

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

    fn apply_renaming(&mut self, x: &Symbol) -> Result<Symbol> {
        match self.ren.iter().find(|(ren, _)| x == ren) {
            None => Err(Error::UnknownVariable(
                x.clone(),
                self.ren.iter().map(|(ren, _)| ren.clone()).collect(),
            )),
            Some((_, y)) => Ok(y.clone()),
        }
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

    fn read_back_type(&mut self, v: &Value) -> Result<Core> {
        let mut norm = self.run_norm();
        norm.read_back_type(v).map_err(Error::Normalize)
    }

    fn read_back(&mut self, n: &Normal) -> Result<Core> {
        let mut norm = self.run_norm();
        norm.read_back(n).map_err(Error::Normalize)
    }

    fn in_expr<T, F>(&mut self, expr: &Expr, mut f: F) -> Result<T>
    where
        F: FnOnce(&mut Self, &ExprAt<Loc>) -> Result<T>,
    {
        let old_loc = self.loc.clone();
        self.loc = expr.loc.clone();
        let res = f(self, &expr.expr);
        self.loc = old_loc;
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
            ExprAt::Trivial => Ok(Core::Trivial),
            _ => todo!(),
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
            _ => todo!(),
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

pub struct Synth {
    pub the_type: Value,
    pub the_expr: Core,
}
