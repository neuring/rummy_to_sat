#![allow(unused)]

use core::fmt;
use std::{collections::{HashMap, HashSet}, fmt::Debug, hash::Hash, marker::PhantomData, ops::{Add, BitAnd, BitOr, Neg}};

pub mod prelude {
    pub use super::{Lit::*, Clause, Encoder, Solver};
}

pub trait Encoder<V>: Sized {
    fn add_clause<I>(&mut self, lits: I)
    where
        I: Iterator<Item = i32>;

    fn varmap(&mut self) -> &mut VarMap<V>;

    fn add_constraint<C: Constraint<V>>(&mut self, constraint: C) {
        constraint.encode(self);
    }
}

pub trait Constraint<V> {
    fn encode<E: Encoder<V>>(self, solver: &mut E);
}

pub struct Clause<I>(pub I);

impl<V: SatVar, I> Constraint<V> for Clause<I> 
where I: Iterator<Item = Lit<V>>
{
    fn encode<E: Encoder<V>>(self, solver: &mut E) {
        let clause: Vec<_> = self.0.map(|lit| solver.varmap().add_var(lit)).collect();
        solver.add_clause(clause.into_iter());
    }
}

#[derive(Debug)]
pub enum Expr<V> {
    And(Box<Expr<V>>, Box<Expr<V>>),
    Or(Box<Expr<V>>, Box<Expr<V>>),
    Neg(Box<Expr<V>>),
    Lit(Lit<V>),
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
            Expr::Lit(e) => {
                solver.varmap().add_var(e)
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


impl<V: SatVar> Constraint<V> for Expr<V> {
    fn encode<E: Encoder<V>>(self, solver: &mut E) {
        let v = self.encode_tree(solver);
        solver.add_clause([v].iter().copied());
    }
}

#[derive(Clone)]
pub struct AtMostK<I> {
    pub vars: I,
    pub k: u32,
}

impl<V: SatVar, I> Constraint<V> for AtMostK<I>
where
    I: Iterator<Item = Lit<V>>,
{
    fn encode<E: Encoder<V>>(self, solver: &mut E) {
        let vars: Vec<_> = self.vars.map(|v| solver.varmap().add_var(v)).collect();
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

#[derive(Clone)]
pub struct AtleastK<I> {
    pub vars: I,
    pub k: u32,
}

impl<V: SatVar, I> Constraint<V> for AtleastK<I>
where
    I: Iterator<Item = Lit<V>>,
{
    fn encode<E: Encoder<V>>(self, solver: &mut E) {
        let k = self.k as usize;

        let vars: Vec<_> = self.vars.map(|v| solver.varmap().add_var(v)).collect();;

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

pub struct IfThen<I1, C> {
    pub cond: I1,
    pub then: C,
}

struct IfThenEncoderWrapper<'a, E> {
    internal: &'a mut E,
    prefix: Vec<i32>,
}

impl<'a, V, E: Encoder<V>> Encoder<V> for IfThenEncoderWrapper<'a, E> {
    fn add_clause<I>(&mut self, lits: I)
    where
        I: Iterator<Item = i32> {
        self.internal.add_clause(lits.chain(self.prefix.iter().copied()));
    }

    fn varmap(&mut self) -> &mut VarMap<V> {
        self.internal.varmap()
    }
}

impl<V: SatVar, C, I1> Constraint<V> for IfThen<I1, C>
where C: Constraint<V>,
      I1: Iterator<Item=Lit<V>>,
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

pub trait SatVar: Hash + Eq + Clone {}

impl<V: Hash + Eq + Clone> SatVar for V {}

pub struct VarMap<V> {
    forward: HashMap<V, i32>,
    reverse: HashMap<i32, V>,
    next_id: i32,
}

impl<V> Default for VarMap<V> {
    fn default() -> Self {
        Self {
            forward: Default::default(),
            reverse: Default::default(),
            next_id: 1,
        }
    }
}

impl<V: fmt::Debug> fmt::Debug for VarMap<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut map: Vec<_> = self.forward.iter().collect();
        map.sort_by_key(|&(_, &i)| i);

        f.debug_list().entries(map).finish()
    }
}

impl<V: SatVar> VarMap<V>
where
{
    fn add_var(&mut self, var: Lit<V>) -> i32 {
        let (var, pol) = match var {
            Lit::Pos(v) => (v, 1),
            Lit::Neg(v) => (v, -1),
        };

        let id = if let Some(id) = self.forward.get(&var) {
            *id
        } else {
            let id = self.new_var();

            self.forward.insert(var.clone(), id);
            self.reverse.insert(id, var);

            id
        };

        pol * id
    }

    #[allow(unused)]
    fn get_var(&self, var: Lit<V>) -> Option<i32> {
        let (var, pol) = match var {
            Lit::Pos(v) => (v, 1),
            Lit::Neg(v) => (v, -1),
        };

        Some(pol * self.forward.get(&var).copied()?)
    }

    fn reverse_get(&self, id: i32) -> Option<&V> {
        self.reverse.get(&id)
    }

    // Returns the number of used variables.
    // NOTE: This might be larger than the used SATVars.
    fn num_vars(&self) -> usize {
        self.next_id as usize
    }
}

impl<V> VarMap<V> {
    fn new_var(&mut self) -> i32 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    fn fresh_vars(&mut self) -> impl FnMut() -> i32 + '_ {
        move || self.new_var()
    }
}

pub struct Solver<V> {
    pub internal: cadical::Solver,
    varmap: VarMap<V>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum Lit<V> {
    Pos(V),
    Neg(V),
}

impl<V> Lit<V> {
    #[allow(unused)]
    pub fn var(&self) -> &V {
        match self {
            Lit::Pos(v) | Lit::Neg(v) => v,
        }
    }
}

impl<V> Neg for Lit<V> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            Lit::Pos(v) => Lit::Neg(v),
            Lit::Neg(v) => Lit::Pos(v),
        }
    }
}

impl<V: SatVar> Solver<V>
{
    pub fn new() -> Self {
        Self {
            internal: cadical::Solver::new(),
            varmap: VarMap::default(),
        }
    }

    pub fn varmap(&self) -> &VarMap<V> {
        &self.varmap
    }

    pub fn solve(&mut self) -> Option<HashSet<Lit<V>>> {
        let result = self.internal.solve();

        if let Some(true) = result {
            let result = (1..=self.varmap.num_vars())
                .filter_map(|v| {
                    let sat_var = self.varmap.reverse_get(v as i32)?.clone();

                    if self.internal.value(v as i32).unwrap_or(true) {
                        Some(Lit::Pos(sat_var))
                    } else {
                        Some(Lit::Neg(sat_var))
                    }
                })
                .collect();
            Some(result)
        } else {
            None
        }
    }
}

impl<V> Encoder<V> for Solver<V> {
    fn add_clause<I>(&mut self, lits: I)
    where
        I: Iterator<Item = i32>,
    {
        self.internal.add_clause(lits);
    }

    fn varmap(&mut self) -> &mut VarMap<V> {
        &mut self.varmap
    }
}

#[derive(Debug)]
pub struct DebugSolver<V>(PhantomData<V>);

impl<V: Debug> DebugSolver<V> {
    #[allow(unused)]
    pub fn new() -> Self {
        Self(PhantomData)
    }

    #[allow(unused)]
    pub fn solve(&mut self) -> Option<HashSet<Lit<V>>> {
        panic!("Cannot solve a debug a solver")
    }

    #[allow(unused)]
    pub fn add_clause<I>(&mut self, clause: I)
    where
        I: IntoIterator<Item = Lit<V>>,
    {
        let clause: Vec<_> = clause.into_iter().collect();

        println!("Clause: {:?}", clause);
    }

    #[allow(unused)]
    pub fn at_most_k<I>(&mut self, vars: I, k: u32)
    where
        I: IntoIterator<Item = Lit<V>>,
    {
        let vars: Vec<_> = vars.into_iter().collect();

        println!("AtMost {}: {:?}", k, vars);
    }

    #[allow(unused)]
    pub fn atleast_k<I>(&mut self, vars: I, k: u32)
    where
        I: IntoIterator<Item = Lit<V>>,
    {
        let vars: Vec<_> = vars.into_iter().collect();

        println!("AtLeast {}: {:?}", k, vars);
    }
}
