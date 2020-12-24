use core::fmt;
use std::{
    fmt::Debug,
    iter::once,
    ops::{BitAnd, BitOr, Neg},
};

use super::{Constraint, Encoder, Lit, SatVar, VarMap};

impl<V: SatVar + Debug> Constraint<V> for Lit<V> {
    fn encode<E: Encoder<V>>(self, solver: &mut E) {
        let var = solver.varmap().add_var(self);
        solver.add_clause([var].iter().copied());
    }
}

#[derive(Clone)]
pub struct Clause<I>(pub I);

impl<V: SatVar, I: Clone> Constraint<V> for Clause<I>
where
    V: Debug + Clone,
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn encode<E: Encoder<V>>(self, solver: &mut E) {
        let clause: Vec<_> = self.0.map(|lit| solver.varmap().add_var(lit)).collect();
        solver.add_clause(clause.into_iter());
    }
}

impl<I, V> Debug for Clause<I>
where
    V: Debug,
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.0.clone()).finish()
    }
}

/// Tseitin Encoding of propositional logic formulas.
#[derive(Clone)]
pub enum Expr<V> {
    And(Box<Expr<V>>, Box<Expr<V>>),
    Or(Box<Expr<V>>, Box<Expr<V>>),
    Neg(Box<Expr<V>>),
    Lit(Lit<V>),
    Constraint(ExprConstraint<V>),
}

impl<V: Debug> Debug for Expr<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::And(lhs, rhs) => f.debug_tuple("And").field(&lhs).field(&rhs).finish(),
            Expr::Or(lhs, rhs) => f.debug_tuple("Or").field(&lhs).field(&rhs).finish(),
            Expr::Neg(e) => f.debug_tuple("Neg").field(&e).finish(),
            Expr::Lit(lit) => f.debug_tuple("Lit").field(&lit).finish(),
            Expr::Constraint(constraint) => {
                f.debug_tuple("Constraint").field(&constraint.0).finish()
            }
        }
    }
}

pub struct ExprConstraint<V>(Box<dyn DynConstraint<V>>);

impl<V> Clone for ExprConstraint<V> {
    fn clone(&self) -> Self {
        Self(self.0.dyn_clone())
    }
}

impl<V: SatVar> Debug for ExprConstraint<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<V: SatVar> ExprConstraint<V> {
    fn new<C>(constraint: C) -> Self
    where
        C: Constraint<V> + Clone + 'static,
    {
        Self(Box::new(constraint))
    }
}

impl<V: SatVar> Expr<V> {
    pub fn from_constraint<C>(constraint: C) -> Self
    where
        C: Constraint<V> + Clone + 'static,
    {
        Self::Constraint(ExprConstraint::new(constraint))
    }
}

struct ExprEncoder<'a, V> {
    clauses: Vec<Vec<i32>>,
    varmap: &'a mut VarMap<V>,
}

impl<'a, V> Encoder<V> for ExprEncoder<'a, V> {
    fn add_clause<I>(&mut self, lits: I)
    where
        I: Iterator<Item = i32>,
    {
        self.clauses.push(lits.collect());
    }

    fn varmap(&mut self) -> &mut VarMap<V> {
        &mut self.varmap
    }
}

trait DynConstraint<V>: Debug {
    fn encode(self: Box<Self>, solver: &mut ExprEncoder<V>);

    fn dyn_clone(&self) -> Box<dyn DynConstraint<V>>;
}

impl<C, V> DynConstraint<V> for C
where
    V: SatVar,
    C: Constraint<V> + Clone + 'static,
{
    fn encode(self: Box<Self>, solver: &mut ExprEncoder<V>) {
        let this = *self;
        <Self as Constraint<V>>::encode(this, solver);
    }

    fn dyn_clone(&self) -> Box<dyn DynConstraint<V>> {
        Box::new(<Self as Clone>::clone(self))
    }
}

impl<V: SatVar> Expr<V> {
    fn encode_tree<E: Encoder<V>>(self, solver: &mut E) -> i32 {
        match self {
            Expr::Or(lhs, rhs) => {
                let lhs_var = lhs.encode_tree(solver);
                let rhs_var = rhs.encode_tree(solver);
                let new_var = solver.varmap().new_var();

                solver.add_clause([-new_var, lhs_var, rhs_var].iter().copied());
                solver.add_clause([new_var, -lhs_var].iter().copied());
                solver.add_clause([new_var, -rhs_var].iter().copied());

                new_var
            }
            Expr::And(lhs, rhs) => {
                let lhs_var = lhs.encode_tree(solver);
                let rhs_var = rhs.encode_tree(solver);
                let new_var = solver.varmap().new_var();

                solver.add_clause([-new_var, lhs_var].iter().copied());
                solver.add_clause([-new_var, rhs_var].iter().copied());
                solver.add_clause([-lhs_var, -rhs_var, new_var].iter().copied());

                new_var
            }
            Expr::Neg(e) => {
                let new_var = solver.varmap().new_var();
                let e = e.encode_tree(solver);
                solver.add_clause([-e, -new_var].iter().copied());
                solver.add_clause([e, new_var].iter().copied());
                new_var
            }
            Expr::Lit(e) => solver.varmap().add_var(e),
            Expr::Constraint(constraint) => {
                let mut solver_wrapper = ExprEncoder {
                    clauses: Vec::new(),
                    varmap: solver.varmap(),
                };

                constraint.0.encode(&mut solver_wrapper);

                let ExprEncoder { clauses, .. } = solver_wrapper;

                // Every clause generated by constraint gets a representant,
                // which encodes the same logical value.
                let mut clause_repr = Vec::new();

                for clause in clauses {
                    let repr = solver.varmap().new_var();

                    solver.add_clause(clause.iter().copied().chain(once(-repr)));

                    for v in clause {
                        solver.add_clause([-v, repr].iter().copied());
                    }

                    clause_repr.push(repr);
                }

                // Finally create representant which is true if all clauses are true.
                let and_repr = solver.varmap().new_var();

                solver.add_clause(clause_repr.iter().map(|i| -i).chain(once(and_repr)));

                for repr in clause_repr {
                    solver.add_clause([-and_repr, repr].iter().copied());
                }

                and_repr
            }
        }
    }
}

impl<V> From<Lit<V>> for Expr<V> {
    fn from(v: Lit<V>) -> Self {
        Self::Lit(v)
    }
}

impl<V, R: Into<Self>> BitAnd<R> for Expr<V> {
    type Output = Expr<V>;

    fn bitand(self, rhs: R) -> Self::Output {
        let rhs = rhs.into();
        Self::And(Box::new(self), Box::new(rhs))
    }
}

impl<V, R: Into<Self>> BitOr<R> for Expr<V> {
    type Output = Expr<V>;

    fn bitor(self, rhs: R) -> Self::Output {
        let rhs = rhs.into();
        Self::Or(Box::new(self), Box::new(rhs))
    }
}

impl<V> Neg for Expr<V> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::Neg(Box::new(self))
    }
}

impl<V: Debug + SatVar> Constraint<V> for Expr<V> {
    fn encode<E: Encoder<V>>(self, solver: &mut E) {
        let v = self.encode_tree(solver);
        solver.add_clause([v].iter().copied());
    }
}

#[derive(Clone)]
pub struct AtMostK<I> {
    pub lits: I,
    pub k: u32,
}

impl<V, I> Constraint<V> for AtMostK<I>
where
    V: SatVar + Clone + Debug,
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn encode<E: Encoder<V>>(self, solver: &mut E) {

        if self.k == 0 {
            for v in self.lits {
                let v = solver.varmap().add_var(-v);
                solver.add_clause(once(v));
            }
            return;
        }

        let vars: Vec<_> = self.lits.map(|v| solver.varmap().add_var(v)).collect();
        let n = vars.len();
        let k = self.k as usize;

        let mut prev_s: Vec<_> = (0..k).map(|_| solver.varmap().new_var()).collect();

        if let Some(v) = vars.first() {
            solver.add_clause([-v, prev_s[0]].iter().copied());
        } else {
            return;
        }

        for s in prev_s.iter().skip(1) {
            solver.add_clause([-s].iter().copied());
        }

        for (i, v) in vars.iter().enumerate().skip(1) {
            if i + 1 == n {
                solver.add_clause([-v, -prev_s[k - 1]].iter().copied());
                break;
            }

            let new_s: Vec<_> = (0..k).map(|_| solver.varmap().new_var()).collect();

            solver.add_clause([-v, new_s[0]].iter().copied());
            solver.add_clause([-prev_s[0], new_s[0]].iter().copied());

            for j in 1usize..(k as usize) {
                solver.add_clause([-v, -prev_s[j - 1], new_s[j]].iter().copied());
                solver.add_clause([-prev_s[j], new_s[j]].iter().copied());
            }

            solver.add_clause([-v, -prev_s[k - 1]].iter().copied());
            prev_s = new_s;
        }
    }
}

impl<V: Debug, I> Debug for AtMostK<I>
where
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lits: Vec<_> = self.lits.clone().collect();

        f.debug_struct("AtMostK")
            .field("k", &self.k)
            .field("vars", &lits)
            .finish()
    }
}

#[derive(Clone)]
pub struct AtleastK<I> {
    pub lits: I,
    pub k: u32,
}

impl<V, I> Constraint<V> for AtleastK<I>
where
    V: SatVar + Debug + Clone,
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn encode<E: Encoder<V>>(self, solver: &mut E) {
        let k = self.k as usize;

        let vars: Vec<_> = self.lits.map(|v| solver.varmap().add_var(v)).collect();

        if k == 0 {
            return;
        } else
        if k == 1 {
            solver.add_clause(vars.into_iter());
            return;
        }

        let n = vars.len();

        let mut prev_s: Vec<_> = (0..k).map(|_| solver.varmap().new_var()).collect();

        solver.add_clause([vars[0], prev_s[k - 1]].iter().copied());
        solver.add_clause([prev_s[k - 1], prev_s[k - 2]].iter().copied());

        for (i, &v) in vars.iter().enumerate().skip(1) {
            if i + 1 == n {
                solver.add_clause([-prev_s[0], v].iter().copied());
                for j in 1..k {
                    solver.add_clause([-prev_s[j]].iter().copied());
                }

                break;
            }

            let mut new_s: Vec<_> = (0..k).map(|_| solver.varmap().new_var()).collect();

            solver.add_clause([-prev_s[0], new_s[0], v].iter().copied());

            for j in 1..k {
                solver.add_clause([-prev_s[j], new_s[j], v].iter().copied());
                solver.add_clause([-prev_s[j], new_s[j], new_s[j - 1]].iter().copied());
            }

            std::mem::swap(&mut prev_s, &mut new_s);
        }
    }
}

impl<V: Debug, I> Debug for AtleastK<I>
where
    I: Iterator<Item = Lit<V>> + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lits: Vec<_> = self.lits.clone().collect();

        f.debug_struct("AtleastK")
            .field("k", &self.k)
            .field("vars", &lits)
            .finish()
    }
}

pub struct If<I1, C> {
    pub cond: I1, // if all lits of cond iterator are true
    pub then: C,  // then this condition has to be true as well.
}

struct IfThenEncoderWrapper<'a, E> {
    internal: &'a mut E,
    prefix: Vec<i32>,
}

impl<'a, V, E: Encoder<V>> Encoder<V> for IfThenEncoderWrapper<'a, E> {
    fn add_clause<I>(&mut self, lits: I)
    where
        I: Iterator<Item = i32>,
    {
        self.internal
            .add_clause(lits.chain(self.prefix.iter().copied()));
    }

    fn varmap(&mut self) -> &mut VarMap<V> {
        self.internal.varmap()
    }
}

impl<V, C, I1> Constraint<V> for If<I1, C>
where
    V: Debug + Clone + SatVar,
    C: Constraint<V>,
    I1: Iterator<Item = Lit<V>> + Clone,
{
    fn encode<E: Encoder<V>>(self, solver: &mut E) {
        let prefix = self.cond.map(|lit| solver.varmap().add_var(-lit)).collect();

        let mut solver = IfThenEncoderWrapper {
            internal: solver,
            prefix,
        };

        self.then.encode(&mut solver);
    }
}

impl<V: Debug, I, C> Debug for If<I, C>
where
    I: Iterator<Item = Lit<V>> + Clone,
    C: Constraint<V>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lits: Vec<_> = self.cond.clone().collect();

        f.debug_tuple("If").field(&lits).field(&self.then).finish()
    }
}
