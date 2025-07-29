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

use crate::Error;
use std::str::FromStr;

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

/// Representing some portion of the expression.
/// Restricted to capital letters, A-Z.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(String);

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl FromStr for Symbol {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Some(c) = s.chars().find(|c| !c.is_ascii_uppercase()) {
            Err(Error::InvalidSymbolCharacter(c))
        } else {
            Ok(Symbol(s.to_owned()))
        }
    }
}

/// A ranking function: keep highest / keep lowest / keep all.
#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
#[cfg_attr(test, derive(proptest_derive::Arbitrary))]
pub enum Ranker {
    All,
    Highest(usize),
    Lowest(usize),
}

impl Ranker {
    /// The minimum count of values required by this ranker.
    pub fn min_count(&self) -> usize {
        match self {
            Ranker::All => 1,
            Ranker::Highest(n) => *n,
            Ranker::Lowest(n) => *n,
        }
    }

    /// How many to keep, out of n rolls.
    pub fn keep(&self, n: isize) -> isize {
        match self {
            Ranker::All => n,
            Ranker::Highest(m) => std::cmp::min(*m as isize, n),
            Ranker::Lowest(m) => std::cmp::min(*m as isize, n),
        }
    }
}

impl std::fmt::Display for Ranker {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (s, n) = match self {
            Ranker::All => return Ok(()),
            Ranker::Highest(n) => ("kh", *n),
            Ranker::Lowest(n) => ("kl", *n),
        };
        if n == 1 {
            write!(f, "{s}")
        } else {
            write!(f, "{s}{n}")
        }
    }
}

/// A comparison operation (or the trivial comparison, which is always True)
#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
#[cfg_attr(test, derive(proptest_derive::Arbitrary))]
pub enum ComparisonOp {
    Gt,
    Ge,
    Eq,
    Le,
    Lt,
}

impl std::fmt::Display for ComparisonOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let c = match self {
            ComparisonOp::Gt => '>',
            ComparisonOp::Ge => '≥',
            ComparisonOp::Eq => '=',
            ComparisonOp::Le => '≤',
            ComparisonOp::Lt => '<',
        };
        write!(f, "{c}")
    }
}

/// The ExpressionTree construct wraps all expressions in a tag type implementing this trait.
pub trait ExpressionWrapper: Sized {
    fn inner(&self) -> &ExpressionTree<Self>;
}

/// An expression tree.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExpressionTree<T> {
    Modifier(Constant),
    Die(Die),
    Symbol(Symbol),

    Negated(Box<T>),
    Repeated {
        count: Box<T>,
        value: Box<T>,
        ranker: Ranker,
    },
    Product(Box<T>, Box<T>),
    Sum(Vec<T>),
    Floor(Box<T>, Box<T>),
    Comparison {
        a: Box<T>,
        b: Box<T>,
        op: ComparisonOp,
    },
    Binding {
        symbol: Symbol,
        value: Box<T>,
        tail: Box<T>,
    },
}

impl<T> From<Die> for ExpressionTree<T> {
    fn from(value: Die) -> Self {
        ExpressionTree::Die(value)
    }
}

impl<T> From<Constant> for ExpressionTree<T> {
    fn from(value: Constant) -> Self {
        ExpressionTree::Modifier(value)
    }
}

impl<T> From<Symbol> for ExpressionTree<T> {
    fn from(value: Symbol) -> Self {
        Self::Symbol(value)
    }
}

impl<T> ExpressionTree<T>
where
    T: ExpressionWrapper,
{
    fn with_paren(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({self})")
    }
}

impl<T> std::fmt::Display for ExpressionTree<T>
where
    T: ExpressionWrapper,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO: Use alternate format specifier, e.g. '{:.}',
        // to switch up spaces, multiplication signs, etc.

        match self {
            ExpressionTree::Die(Die(n)) => write!(f, "d{n}"),
            ExpressionTree::Modifier(Constant(n)) => write!(f, "{n}"),
            ExpressionTree::Symbol(n) => write!(f, "{n}"),
            ExpressionTree::Repeated {
                count,
                value,
                ranker,
            } => {
                let count = count.inner();
                let value = value.inner();
                if matches!(count, ExpressionTree::Modifier(_)) {
                    count.fmt(f)?
                } else {
                    count.with_paren(f)?
                };
                if matches!(value, ExpressionTree::Die(_)) {
                    value.fmt(f)?
                } else {
                    value.with_paren(f)?
                };
                write!(f, "{ranker}")
            }
            ExpressionTree::Negated(expression) => {
                let n = expression.inner();
                if matches!(
                    n,
                    ExpressionTree::Die(_)
                        | ExpressionTree::Modifier(_)
                        | ExpressionTree::Symbol(_)
                        | ExpressionTree::Repeated { .. }
                ) {
                    write!(f, "-{n}")
                } else {
                    write!(f, "-")?;
                    n.with_paren(f)
                }
            }
            ExpressionTree::Product(a, b) => {
                let a = a.inner();
                let b = b.inner();
                if matches!(
                    a,
                    ExpressionTree::Die(_)
                        | ExpressionTree::Modifier(_)
                        | ExpressionTree::Symbol(_)
                        | ExpressionTree::Repeated { .. }
                        | ExpressionTree::Negated(_)
                ) {
                    a.fmt(f)?
                } else {
                    a.with_paren(f)?
                };

                write!(f, " * ")?;

                if matches!(
                    b,
                    ExpressionTree::Die(_)
                        | ExpressionTree::Modifier(_)
                        | ExpressionTree::Symbol(_)
                        | ExpressionTree::Repeated { .. }
                        | ExpressionTree::Negated(_)
                        | ExpressionTree::Product(_, _)
                        | ExpressionTree::Floor(_, _)
                ) {
                    b.fmt(f)
                } else {
                    b.with_paren(f)
                }
            }
            ExpressionTree::Floor(a, b) => {
                let a = a.inner();
                let b = b.inner();

                if matches!(
                    a,
                    ExpressionTree::Die(_)
                        | ExpressionTree::Modifier(_)
                        | ExpressionTree::Symbol(_)
                        | ExpressionTree::Repeated { .. }
                        | ExpressionTree::Negated(_)
                ) {
                    a.fmt(f)?
                } else {
                    a.with_paren(f)?
                };

                write!(f, " / ")?;

                if matches!(
                    b,
                    ExpressionTree::Die(_)
                        | ExpressionTree::Modifier(_)
                        | ExpressionTree::Symbol(_)
                        | ExpressionTree::Repeated { .. }
                        | ExpressionTree::Negated(_)
                        | ExpressionTree::Product(_, _)
                        | ExpressionTree::Floor(_, _)
                ) {
                    b.fmt(f)
                } else {
                    b.with_paren(f)
                }
            }
            ExpressionTree::Sum(es) => {
                for (i, e) in es.iter().enumerate() {
                    let e = e.inner();

                    // Use - instead of + if the expression is negated and not at the
                    // head of the list.
                    let (e, c) = match (e, i) {
                        (_, 0) => (e, None),
                        (ExpressionTree::Negated(inner), _) => (inner.inner(), Some('-')),
                        _ => (e, Some('+')),
                    };
                    if let Some(c) = c {
                        write!(f, "{c}")?;
                    }

                    match e {
                        ExpressionTree::Die(_)
                        | ExpressionTree::Modifier(_)
                        | ExpressionTree::Symbol(_)
                        | ExpressionTree::Repeated { .. }
                        | ExpressionTree::Floor(_, _)
                        | ExpressionTree::Product(_, _) => e.fmt(f),
                        _ => e.with_paren(f),
                    }?;
                }

                Ok(())
            }
            ExpressionTree::Comparison { a, b, op } => {
                let a = a.inner();
                let b = b.inner();
                fn write_element<T: ExpressionWrapper>(
                    e: &ExpressionTree<T>,
                    f: &mut std::fmt::Formatter<'_>,
                ) -> Result<(), std::fmt::Error> {
                    match e {
                        ExpressionTree::Binding { .. } | ExpressionTree::Comparison { .. } => {
                            e.with_paren(f)
                        }
                        _ => e.fmt(f),
                    }
                }
                write_element(a, f)?;
                write!(f, " {op} ")?;
                write_element(b, f)
            }
            ExpressionTree::Binding {
                symbol,
                value,
                tail,
            } => {
                let value = value.inner();
                let tail = tail.inner();
                write!(f, "[{symbol}: {value}] {tail}")
            }
        }
    }
}
