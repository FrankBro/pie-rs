use crate::{
    fresh::freshen,
    types::{Closure, Core, Env, Neutral, Normal, Symbol, Value},
};

pub enum Error {
    NotAFunction(Value),
}

type Result<T, E = Error> = std::result::Result<T, E>;

struct Norm {
    bound: Vec<Symbol>,
    env: Env<Value>,
}

impl Norm {
    fn with_env(&self, env: Env<Value>) -> Norm {
        Self {
            bound: self.bound.clone(),
            env,
        }
    }

    fn fresh(&self, x: &str) -> Symbol {
        freshen(&self.bound, x.into())
    }

    fn instantiate(&self, clos: Closure<Value>, x: Symbol, v: Value) -> Result<Value> {
        let mut env = clos.env.clone();
        env.push((x, v));
        self.with_env(env).eval(&clos.expr)
    }

    fn eval(&mut self, core: &Core) -> Result<Value> {
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
            _ => todo!(),
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
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_norm() {}
}
