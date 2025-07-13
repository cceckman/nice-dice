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
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(proptest_derive::Arbitrary))]
pub struct Constant(pub usize);

impl std::fmt::Display for Constant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

/// A die, ranging from 1 to a given size.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(proptest_derive::Arbitrary))]
pub struct Die(pub usize);

impl std::fmt::Display for Die {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "d{}", self.0)
    }
}

/// An atomic unit of a distribution.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(proptest_derive::Arbitrary))]
pub enum UnqualifiedAtom {
    Constant(Constant),
    Die(Die),
}

impl std::fmt::Display for UnqualifiedAtom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnqualifiedAtom::Constant(c) => c.fmt(f),
            UnqualifiedAtom::Die(d) => d.fmt(f),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SymbolicAtom {
    Constant(Constant),
    Die(Die),
    Symbol(Symbol),
}

impl std::fmt::Display for SymbolicAtom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Constant(c) => c.fmt(f),
            Self::Die(d) => d.fmt(f),
            Self::Symbol(s) => s.fmt(f),
        }
    }
}

/// A grammatical construct: "atom" includes bindings, to allow for later substitution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BindingAtom {
    Constant(Constant),
    Die(Die),
    Symbol(Symbol),
    Binding {
        symbol: Symbol,
        expression: Box<Expression<BindingAtom>>,
    },
}

impl std::fmt::Display for BindingAtom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Constant(c) => c.fmt(f),
            Self::Die(d) => d.fmt(f),
            Self::Symbol(s) => s.fmt(f),
            Self::Binding { symbol, expression } => write!(f, "[ {symbol}: {expression} ]"),
        }
    }
}

impl From<Constant> for UnqualifiedAtom {
    fn from(value: Constant) -> Self {
        UnqualifiedAtom::Constant(value)
    }
}

impl From<Die> for UnqualifiedAtom {
    fn from(value: Die) -> Self {
        UnqualifiedAtom::Die(value)
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

impl From<Constant> for BindingAtom {
    fn from(value: Constant) -> Self {
        BindingAtom::Constant(value)
    }
}

impl From<Die> for BindingAtom {
    fn from(value: Die) -> Self {
        BindingAtom::Die(value)
    }
}

impl From<Symbol> for SymbolicAtom {
    fn from(value: Symbol) -> Self {
        SymbolicAtom::Symbol(value)
    }
}

impl From<Symbol> for BindingAtom {
    fn from(value: Symbol) -> Self {
        BindingAtom::Symbol(value)
    }
}

/// An expression tree, generic over some atom.
///
/// This allows the expression tree to be symbolic (if atoms include symbols) or unconditional (if
/// atoms are not symbolic).
#[derive(Debug, Clone, PartialEq, Eq)]
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

pub type Unconditional = Expression<UnqualifiedAtom>;
pub type Symbolic = Expression<SymbolicAtom>;

impl From<UnqualifiedAtom> for Unconditional {
    fn from(value: UnqualifiedAtom) -> Self {
        Self::Atom(value)
    }
}

impl From<SymbolicAtom> for Symbolic {
    fn from(value: SymbolicAtom) -> Self {
        Self::Atom(value)
    }
}

impl From<BindingAtom> for Expression<BindingAtom> {
    fn from(value: BindingAtom) -> Self {
        Self::Atom(value)
    }
}

impl<AtomT> Expression<AtomT>
where
    AtomT: Atom,
{
    fn with_paren(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({self})")
    }
}

trait Atom: std::fmt::Display {
    fn is_constant(&self) -> bool;
    fn is_die(&self) -> bool;
}

impl Atom for UnqualifiedAtom {
    fn is_constant(&self) -> bool {
        matches!(self, UnqualifiedAtom::Constant(_))
    }

    fn is_die(&self) -> bool {
        matches!(self, UnqualifiedAtom::Die(_))
    }
}

impl Atom for SymbolicAtom {
    fn is_constant(&self) -> bool {
        matches!(self, SymbolicAtom::Constant(_))
    }

    fn is_die(&self) -> bool {
        matches!(self, SymbolicAtom::Die(_))
    }
}

impl Atom for BindingAtom {
    fn is_constant(&self) -> bool {
        matches!(self, BindingAtom::Constant(_))
    }

    fn is_die(&self) -> bool {
        matches!(self, BindingAtom::Die(_))
    }
}

impl<AtomT> std::fmt::Display for Expression<AtomT>
where
    AtomT: Atom,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO: Use alternate format specifier, e.g. '{:.}',
        // to switch up spaces, multiplication signs, etc.

        match self {
            Expression::Atom(n) => write!(f, "{n}"),
            Expression::Repeated {
                count,
                value,
                ranker,
            } => {
                if matches!(&**count, Expression::Atom(a) if a.is_constant()) {
                    count.fmt(f)?
                } else {
                    count.with_paren(f)?
                };
                if matches!(&**value, Expression::Atom(a) if a.is_die()) {
                    value.fmt(f)?
                } else {
                    value.with_paren(f)?
                };
                write!(f, "{ranker}")
            }
            Expression::Negated(expression) => {
                if matches!(
                    &**expression,
                    Expression::Atom(_) | Expression::Repeated { .. }
                ) {
                    expression.fmt(f)
                } else {
                    expression.with_paren(f)
                }
            }
            Expression::Product(a, b) => {
                if matches!(
                    &**a,
                    Expression::Atom(_) | Expression::Repeated { .. } | Expression::Negated(_)
                ) {
                    a.fmt(f)?
                } else {
                    a.with_paren(f)?
                };

                write!(f, " * ")?;

                if matches!(
                    &**b,
                    Expression::Atom(_)
                        | Expression::Repeated { .. }
                        | Expression::Negated(_)
                        | Expression::Product(_, _)
                        | Expression::Floor(_, _)
                ) {
                    b.fmt(f)
                } else {
                    b.with_paren(f)
                }
            }
            Expression::Floor(a, b) => {
                if matches!(
                    &**a,
                    Expression::Atom(_) | Expression::Repeated { .. } | Expression::Negated(_)
                ) {
                    a.fmt(f)?
                } else {
                    a.with_paren(f)?
                };

                write!(f, " /_ ")?;

                if matches!(
                    &**b,
                    Expression::Atom(_)
                        | Expression::Repeated { .. }
                        | Expression::Negated(_)
                        | Expression::Product(_, _)
                        | Expression::Floor(_, _)
                ) {
                    b.fmt(f)
                } else {
                    b.with_paren(f)
                }
            }
            Expression::Sum(es) => {
                fn write_element<AtomT: Atom>(
                    e: &Expression<AtomT>,
                    f: &mut std::fmt::Formatter<'_>,
                ) -> Result<(), std::fmt::Error> {
                    let e = match e {
                        Expression::Negated(inner) => inner,
                        _ => e,
                    };
                    match e {
                        Expression::Atom(_)
                        | Expression::Repeated { .. }
                        | Expression::Floor(_, _)
                        | Expression::Product(_, _) => e.fmt(f),
                        _ => e.with_paren(f),
                    }
                }
                for (i, e) in es.iter().enumerate() {
                    if i != 0 {
                        let c = if let Expression::Negated(_) = e {
                            '-'
                        } else {
                            '+'
                        };
                        write!(f, " {c} ")?;
                    }
                    write_element(e, f)?;
                }

                Ok(())
            }
            Expression::Comparison { a, b, op } => {
                write!(f, "({a} {op} {b})")
            }
        }
    }
}
