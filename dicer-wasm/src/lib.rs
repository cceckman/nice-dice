#[allow(warnings)]
mod bindings;

use std::sync::Mutex;

use bindings::exports::cceckman::dicer::dicer as dicer_bindings;
use dicer::html::table_multi_dist;

struct Component;

impl dicer_bindings::GuestDistribution for dicer::Distribution {}
impl dicer_bindings::GuestExpression for dicer::Closed {}

type Evaluator = Mutex<dicer::Evaluator>;

impl dicer_bindings::GuestEvaluator for Evaluator {
    fn new() -> Self {
        Self::default()
    }

    fn render_distribution_table(
        &self,
        exprs: Vec<dicer_bindings::ExpressionBorrow<'_>>,
    ) -> Result<String, dicer_bindings::Error> {
        let distrs: Result<Vec<_>, dicer::Error> = exprs
            .into_iter()
            .map(|expr| {
                let expr: &dicer::Closed = expr.get();
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

impl From<dicer::Error> for dicer_bindings::Error {
    fn from(value: dicer::Error) -> Self {
        use dicer::Error::*;
        use dicer_bindings::ErrorCode;
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
        dicer_bindings::Error { code, message }
    }
}

impl dicer_bindings::Guest for Component {
    type Distribution = dicer::Distribution;

    type Expression = dicer::Closed;

    type Evaluator = Evaluator;

    fn parse(
        text: String,
    ) -> Result<
        bindings::exports::cceckman::dicer::dicer::Expression,
        bindings::exports::cceckman::dicer::dicer::Error,
    > {
        let closed: dicer::Closed = text.parse()?;
        Ok(dicer_bindings::Expression::new(closed))
    }
}

bindings::export!(Component with_types_in bindings);
