/// A roll of a number of dice of a given size: NdM.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(test, derive(proptest_derive::Arbitrary))]
struct Dice {
    n: usize,
    m: usize,
}

impl std::fmt::Display for Dice {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}d{}", self.n, self.m)
    }
}

/// A composite dice expression.
#[derive(Clone, PartialEq, Eq, Debug)]
enum Expression {
    Roll(Dice),
    Modifier(usize),
    Negation(Box<Expression>),
}

impl std::fmt::Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Roll(dice) => dice.fmt(f),
            Expression::Modifier(n) => n.fmt(f),
            Expression::Negation(expression) => write!(f, "- {expression}"),
        }
    }
}

peg::parser! {
    grammar dice_notation() for str {
        rule number() -> usize
          = n:$(['0'..='9']+) {? n.parse().or(Err("usize")) }

        pub(crate) rule dice() -> Dice
            = n:(number()) "d" m:(number()) { Dice{n, m} }

        rule negated() -> Expression
            = "-" " "? exp:expression() { Expression::Negation(Box::new(exp)) }

        pub(crate) rule expression() -> Expression
            =   n:negated()
            /   d:dice()    { Expression::Roll(d) }
            /   m:number()  { Expression::Modifier(m) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn formats() {
        for (want, dice) in [("1d4", Dice { n: 1, m: 4 }), ("2d20", Dice { n: 2, m: 20 })] {
            let got = dice.to_string();
            assert_eq!(&got, want);
        }
    }

    #[test]
    fn tetrahedron() {
        let d = dice_notation::dice("1d4").unwrap();
        assert_eq!(d, Dice { n: 1, m: 4 });
    }

    proptest! {
        #[test]
        fn dice_roundtrip(dice in any::<Dice>()) {
            let s = dice.to_string();
            let d = dice_notation::dice(&s).unwrap();
            assert_eq!(d, dice);
        }
    }

    /// Generate a possibly-recursive Expression.
    fn recursive_expression() -> impl Strategy<Value = Expression> {
        let leaf = proptest::prop_oneof![
            any::<Dice>().prop_map(Expression::Roll),
            any::<usize>().prop_map(Expression::Modifier),
        ];
        leaf.prop_recursive(8, 256, 3, |strat| {
            strat.prop_map(|expr| Expression::Negation(Box::new(expr)))
        })
    }

    proptest! {
        #[test]
        fn expression_roundtrip(exp in recursive_expression()) {
            let s = exp.to_string();
            let got = dice_notation::expression(&s).unwrap();
            assert_eq!(got, exp);
        }
    }

    proptest! {
        #[test]
        fn expression_without_space(exp in recursive_expression()) {
            let s = exp.to_string();
            let s : String = s.chars().filter(|c| *c != ' ').collect();
            let got = dice_notation::expression(&s).unwrap();
            assert_eq!(got, exp);
        }
    }
}
