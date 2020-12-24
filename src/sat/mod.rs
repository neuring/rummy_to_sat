#![allow(unused)]

use core::fmt;
use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
    marker::PhantomData,
    ops::{Add, BitAnd, BitOr, Neg},
};

mod constraints;

pub mod prelude {
    pub use super::{constraints::Clause, Encoder, Lit::{self, *}, Solver};
}

pub use constraints::{AtMostK, AtleastK, If, Expr};

pub trait Encoder<V>: Sized {
    fn add_clause<I>(&mut self, lits: I)
    where
        I: Iterator<Item = i32>;

    fn varmap(&mut self) -> &mut VarMap<V>;

    fn add_constraint<C: Constraint<V>>(&mut self, constraint: C) {
        constraint.encode(self);
    }
}

pub trait Constraint<V>: Debug {
    fn encode<E: Encoder<V>>(self, solver: &mut E);
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

impl<V: Debug> Debug for VarMap<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut map: Vec<_> = self.forward.iter().collect();
        map.sort_by_key(|&(_, &i)| i);

        f.debug_list().entries(map).finish()
    }
}

impl<V: SatVar> VarMap<V> {
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

impl<V: SatVar> Solver<V> {
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
pub struct DebugSolver<V>(VarMap<V>);

impl<V> DebugSolver<V> {
    pub fn new() -> Self {
        Self(Default::default())
    }

    pub fn solve(&mut self) -> Option<HashSet<Lit<V>>> {
        panic!("Cannot solve a DebugSolver");
    }
}

impl<V> Encoder<V> for DebugSolver<V> {
    fn add_clause<I>(&mut self, lits: I)
    where
        I: Iterator<Item = i32>,
    {
    }

    fn varmap(&mut self) -> &mut VarMap<V> {
        &mut self.0
    }

    fn add_constraint<C: Constraint<V>>(&mut self, constraint: C) {
        dbg!(constraint);
    }
}
