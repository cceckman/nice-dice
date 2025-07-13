//! Types for the symbolic evaluation approach.
//!
//! With symbols, evaluation proceeds in three phases, indicated by types:
//!
//! 1.  Parsing. Produces an Expression<BindingAtom>, which may include bindings for some
//!     expressions.
//! 2.  Semantic analysis / binding extraction. Produces an Expression<SymbolAtom> and a
//!     HashMap<Symbol, Expression<Atom>>. Bindings are bubbled up and replaced with symbols.
//! 3.  Substitution. For each combination of symbol values, produces an Expression<Atom>.
//!     This expression can be evaluated for its distribution.

use crate::{ComparisonOp, Ranker, parse::Symbol};

/// A constant value.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Constant(usize);

/// A die, ranging from 1 to a given size.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Die(usize);

/// An atomic unit of a distribution.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Atom {
    Constant(Constant),
    Die(Die),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum SymbolicAtom {
    Constant(Constant),
    Die(Die),
    Symbol(Symbol),
}

/// An atomic unit of a distribution, that may include bindings of subexpressions.
#[derive(Clone)]
pub enum BindingAtom {
    Constant(Constant),
    Die(Die),
    Symbol(Symbol),
    Binding {
        symbol: Symbol,
        expression: Box<Expression<Atom>>,
    },
}

impl From<Constant> for Atom {
    fn from(value: Constant) -> Self {
        Atom::Constant(value)
    }
}

impl From<Die> for Atom {
    fn from(value: Die) -> Self {
        Atom::Die(value)
    }
}

impl From<Constant> for SymbolicAtom {
    fn from(value: Constant) -> Self {
        SymbolicAtom::Constant(value)
    }
}

impl From<Die> for SymbolicAtom {
    fn from(value: Die) -> Self {
        SymbolicAtom::Die(value)
    }
}

/// An expression tree, generic over some atom.
///
/// This allows the expression tree to be symbolic (if atoms include symbols) or unconditional (if
/// atoms are not symbolic).
#[derive(Clone)]
pub enum Expression<AtomT> {
    Atom(AtomT),

    Negated(Box<Self>),
    Repeated {
        count: Box<Self>,
        value: Box<Self>,
        ranker: Ranker,
    },
    Product(Box<Self>, Box<Self>),
    Sum(Vec<Self>),
    Floor(Box<Self>, Box<Self>),
    Comparison {
        a: Box<Self>,
        b: Box<Self>,
        op: ComparisonOp,
    },
}

impl<AtomT> From<Constant> for Expression<AtomT>
where
    AtomT: From<Constant>,
{
    fn from(value: Constant) -> Self {
        let a: AtomT = value.into();
        Self::Atom(a)
    }
}

impl<AtomT> From<Die> for Expression<AtomT>
where
    AtomT: From<Die>,
{
    fn from(value: Die) -> Self {
        let a: AtomT = value.into();
        Self::Atom(a)
    }
}

impl<AtomT> From<Symbol> for Expression<AtomT>
where
    AtomT: From<Symbol>,
{
    fn from(value: Symbol) -> Self {
        let a: AtomT = value.into();
        Self::Atom(a)
    }
}

pub type Unconditional = Expression<Atom>;
pub type Symbolic = Expression<SymbolicAtom>;

impl From<Atom> for Unconditional {
    fn from(value: Atom) -> Self {
        Self::Atom(value)
    }
}

impl From<SymbolicAtom> for Symbolic {
    fn from(value: SymbolicAtom) -> Self {
        Self::Atom(value)
    }
}
