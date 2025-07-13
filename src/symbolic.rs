//! Distribution evaluation with symbolic expressions and conditionals.

use std::collections::HashMap;

use crate::{
    Error,
    parse::{self, Symbol},
};

mod types;
pub use types::*;

/// An expression with bindings extracted.
struct Extracted {
    symbol_expressions: HashMap<Symbol, Unconditional>,
    expression: Symbolic,
}

impl TryFrom<parse::Expression> for Extracted {
    type Error = Error;

    fn try_from(value: parse::Expression) -> Result<Self, Self::Error> {
        todo!()
    }
}

impl TryFrom<&Symbolic> for Unconditional {
    type Error = Vec<Symbol>;

    fn try_from(value: &Symbolic) -> Result<Self, Self::Error> {
        /// Combine two subexpression results.
        /// This ensures we collect all the symbols.
        fn combine(
            a: Result<Unconditional, Vec<Symbol>>,
            b: Result<Unconditional, Vec<Symbol>>,
        ) -> Result<(Unconditional, Unconditional), Vec<Symbol>> {
            match (a, b) {
                (Err(a), Err(b)) => {
                    let mut result = a;
                    for sym in b {
                        if !result.contains(&sym) {
                            result.push(sym);
                        }
                    }
                    Err(result)
                }
                (Ok(a), Ok(b)) => Ok((a, b)),
                (Ok(_), Err(e)) | (Err(e), Ok(_)) => Err(e),
            }
        }

        match value {
            Expression::Atom(a) => match a {
                SymbolicAtom::Constant(constant) => Ok((*constant).into()),
                SymbolicAtom::Die(die) => Ok((*die).into()),
                SymbolicAtom::Symbol(symbol) => Err(vec![symbol.clone()]),
            },
            Expression::Negated(expression) => {
                let e: Unconditional = expression.as_ref().try_into()?;
                Ok(Unconditional::Negated(Box::new(e)))
            }
            Expression::Repeated {
                count,
                value,
                ranker,
            } => {
                let (count, value) = combine(count.as_ref().try_into(), value.as_ref().try_into())?;
                Ok(Unconditional::Repeated {
                    count: Box::new(count),
                    value: Box::new(value),
                    ranker: *ranker,
                })
            }
            Expression::Product(a, b) => {
                let (a, b) = combine(a.as_ref().try_into(), b.as_ref().try_into())?;
                Ok(Expression::Product(Box::new(a), Box::new(b)))
            }
            Expression::Floor(a, b) => {
                let (a, b) = combine(a.as_ref().try_into(), b.as_ref().try_into())?;
                Ok(Expression::Floor(Box::new(a), Box::new(b)))
            }
            Expression::Sum(expressions) => {
                let mut unconditionals = Vec::new();
                let mut symbols = Vec::new();
                for expr in expressions
                    .iter()
                    .map(|v| -> Result<Unconditional, Vec<Symbol>> { v.try_into() })
                {
                    match expr {
                        Ok(a) => unconditionals.push(a),
                        Err(b) => {
                            for sym in b.into_iter() {
                                if !symbols.contains(&sym) {
                                    symbols.push(sym);
                                }
                            }
                        }
                    }
                }

                Ok(Expression::Sum(unconditionals))
            }

            Expression::Comparison { a, b, op } => {
                let (a, b) = combine(a.as_ref().try_into(), b.as_ref().try_into())?;
                Ok(Expression::Comparison {
                    a: Box::new(a),
                    b: Box::new(b),
                    op: *op,
                })
            }
        }
    }
}
