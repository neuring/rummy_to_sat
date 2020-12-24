#![allow(unused)]

use core::fmt;
use std::{collections::{HashMap, HashSet}, fmt::Debug, hash::Hash, marker::PhantomData, ops::{Add, BitAnd, BitOr, Neg}};

pub mod prelude {
    pub use super::Lit::*;
    pub use super::Solver;
}

trait Encoder {
    fn add_clause<I>(&mut self, lits: I)
    where
        I: Iterator<Item = i32>;

    fn at_most_k<I, F>(&mut self, vars: I, k: u32, mut fresh_var: F)
    where
        I: Iterator<Item = i32>,
        F: FnMut() -> i32,
    {
        let vars: Vec<_> = vars.collect();
        let n = vars.len();
        let k = k as usize;

        let mut prev_s: Vec<_> = (0..k).map(|_| fresh_var()).collect();

        if let Some(v) = vars.first() {
            self.add_clause([-v, prev_s[0]].iter().copied());
        } else {
            return;
        }

        for s in prev_s.iter().skip(1) {
            self.add_clause([-s].iter().copied());
        }

        for (i, v) in vars.iter().enumerate().skip(1) {
            if i + 1 == n {
                self.add_clause([-v, -prev_s[k - 1]].iter().copied());
                break;
            }

            let new_s: Vec<_> = (0..k).map(|_| fresh_var()).collect();

            self.add_clause([-v, new_s[0]].iter().copied());
            self.add_clause([-prev_s[0], new_s[0]].iter().copied());

            for j in 1usize..(k as usize) {
                self.add_clause([-v, -prev_s[j - 1], new_s[j]].iter().copied());
                self.add_clause([-prev_s[j], new_s[j]].iter().copied());
            }

            self.add_clause([-v, -prev_s[k - 1]].iter().copied());
            prev_s = new_s;
        }
    }

    fn atleast_k<I, F>(&mut self, vars: I, k: u32, mut fresh_var: F)
    where
        I: Iterator<Item = i32>,
        F: FnMut() -> i32,
    {
        let k = k as usize;

        if k == 1 {
            self.add_clause(vars);
            return
        }

        let vars: Vec<_> = vars.collect();
        let n = vars.len();

        let mut prev_s: Vec<_> = (0..k).map(|_| fresh_var()).collect();

        self.add_clause([vars[0], prev_s[k - 1]].iter().copied());
        self.add_clause([prev_s[k - 1], prev_s[k - 2]].iter().copied());

        for (i, &v) in vars.iter().enumerate().skip(1) {

            if i + 1 == n {
                self.add_clause([-prev_s[0], v].iter().copied());
                for j in 1..k {
                    self.add_clause([-prev_s[j]].iter().copied());
                }

                break;
            }

            let mut new_s: Vec<_> = (0..k).map(|_| fresh_var()).collect();

            self.add_clause([-prev_s[0], new_s[0], v].iter().copied());

            for j in 1..k {
                self.add_clause([-prev_s[j], new_s[j], v].iter().copied());
                self.add_clause([-prev_s[j], new_s[j], new_s[j - 1]].iter().copied());
            }

            std::mem::swap(&mut prev_s, &mut new_s);
        }
    }
}

impl Encoder for cadical::Solver {
    fn add_clause<I>(&mut self, lits: I)
    where
        I: Iterator<Item = i32>,
    {
        self.add_clause(lits);
    }
}

#[derive(Debug)]
pub enum Expr<V> {
    And(Box<Expr<V>>, Box<Expr<V>>),
    Or(Box<Expr<V>>, Box<Expr<V>>),
    Neg(Box<Expr<V>>),
    Var(V),
}

impl<V> From<V> for Expr<V> {
    fn from(v: V) -> Self {
        Self::Var(v)
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

pub trait Constraint<V> {
    fn encode(&self, solver: &mut Solver<V>);
}

pub struct AtMostK<I> {
    vars: I,
    k: u32,
}

impl<V, I> Constraint<V> for AtMostK<I> 
    where I: Iterator<Item=V>,
{
    fn encode(&self, solver: &mut Solver<V>) {
    }
}

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

impl<V> VarMap<V>
where
    V: Hash + Eq + Clone,
{
    fn add_var(&mut self, var: Lit<V>) -> i32 {
        let (var, pol) = match var {
            Lit::Pos(v) => (v, 1),
            Lit::Neg(v) => (v, -1),
        };

        let id = if let Some(id) = self.forward.get(&var) {
            *id
        } else {
            let id = self.next_id();

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
    fn next_id(&mut self) -> i32 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    fn fresh_vars(&mut self) -> impl FnMut() -> i32 + '_ {
        move || self.next_id()
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

impl<V> Solver<V>
where
    V: Clone + Hash + Eq,
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

    pub fn add_clause<I>(&mut self, clause: I)
    where
        I: IntoIterator<Item = Lit<V>>,
    {
        let clause = clause.into_iter();

        let varmap = &mut self.varmap;

        self.internal.add_clause(clause.map(|v| varmap.add_var(v)));
    }

    pub fn at_most_k<I>(&mut self, vars: I, k: u32)
    where
        I: IntoIterator<Item = Lit<V>>,
    {
        let vars = vars.into_iter();

        let varmap = &mut self.varmap;
        let vars: Vec<_> = vars.map(|v| varmap.add_var(v)).collect();

        self.internal
            .at_most_k(vars.into_iter(), k, varmap.fresh_vars());
    }

    pub fn atleast_k<I>(&mut self, vars: I, k: u32)
    where
        I: IntoIterator<Item = Lit<V>>,
    {
        let vars = vars.into_iter();

        let varmap = &mut self.varmap;
        let vars: Vec<_> = vars.map(|v| varmap.add_var(v)).collect();

        self.internal
            .atleast_k(vars.into_iter(), k, varmap.fresh_vars());
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
