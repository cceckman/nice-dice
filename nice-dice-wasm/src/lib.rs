#[allow(warnings)]
mod bindings;

use std::sync::Mutex;

use bindings::exports::cceckman::nice_dice::nice_dice as nice_dice_bindings;
use nice_dice::html::table_multi_dist;

struct Component;

impl nice_dice_bindings::GuestDistribution for nice_dice::Distribution {}
impl nice_dice_bindings::GuestExpression for nice_dice::Closed {}

type Evaluator = Mutex<nice_dice::Evaluator>;

impl nice_dice_bindings::GuestEvaluator for Evaluator {
    fn new() -> Self {
        Self::default()
    }

    fn render_distribution_table(
        &self,
        exprs: Vec<nice_dice_bindings::ExpressionBorrow<'_>>,
    ) -> Result<String, nice_dice_bindings::Error> {
        let distrs: Result<Vec<_>, nice_dice::Error> = exprs
            .into_iter()
            .map(|expr| {
                let expr: &nice_dice::Closed = expr.get();
                let name = expr.to_string();
                let distr = self.lock().unwrap().eval(expr)?;
                Ok((name, distr))
            })
            .collect();
        let distrs = distrs?;
        let result = table_multi_dist(&distrs);

        Ok(result.into())
    }
}

impl From<nice_dice::Error> for nice_dice_bindings::Error {
    fn from(value: nice_dice::Error) -> Self {
        use nice_dice::Error::*;
        use nice_dice_bindings::ErrorCode;
        let message = value.to_string();
        let code = match value {
            ParseError(_, _) => ErrorCode::Parse,
            NegativeCount(_) => ErrorCode::NegativeCount,
            KeepTooFew(_, _) => ErrorCode::KeepTooFew,
            DivideByZero(_) => ErrorCode::DivideByZero,
            InvalidSymbolCharacter(_) => ErrorCode::InvalidSymbol,
            UnboundSymbols(_) => ErrorCode::UnboundSymbols,
            ZeroFacedDie() => ErrorCode::ZeroFacedDie,
        };
        nice_dice_bindings::Error { code, message }
    }
}

impl nice_dice_bindings::Guest for Component {
    type Distribution = nice_dice::Distribution;

    type Expression = nice_dice::Closed;

    type Evaluator = Evaluator;

    fn parse(
        text: String,
    ) -> Result<
        bindings::exports::cceckman::nice_dice::nice_dice::Expression,
        bindings::exports::cceckman::nice_dice::nice_dice::Error,
    > {
        let closed: nice_dice::Closed = text.parse()?;
        Ok(nice_dice_bindings::Expression::new(closed))
    }
}

bindings::export!(Component with_types_in bindings);
