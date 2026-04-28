//! S-expression parser, inverse of [`crate::expr::Expr::to_canonical`].
//!
//! Atoms are `v:NAME`, `c:CONSTANT`, `n:NUM[/DEN]`. Compound forms use the
//! exact prefix tokens `to_canonical` emits (`+`, `-`, `*`, `/`, `^`, `=`,
//! `!=`, `<`, `<=`, `>`, `>=`, `and`, `or`, `->`, `<->`, `cross`, `dot`,
//! `tensor`, unary names, `@`, `deriv`, `partial`, `integral`, `sum`,
//! `prod`, `limit`, `lambda`, `pi`, `let`).

use crate::expr::{BinOp, Expr, PhysConst, UnOp};
use thiserror::Error;

#[derive(Debug, Error, PartialEq)]
pub enum SexprError {
    #[error("unexpected end of input")]
    UnexpectedEof,
    #[error("unexpected token `{0}`")]
    UnexpectedToken(String),
    #[error("unknown operator `{0}`")]
    UnknownOp(String),
    #[error("unknown physical constant `{0}`")]
    UnknownConst(String),
    #[error("malformed atom `{0}`")]
    MalformedAtom(String),
    #[error("operator `{op}` expected {expected} args, got {got}")]
    Arity { op: String, expected: usize, got: usize },
    #[error("trailing tokens after expression")]
    Trailing,
    #[error("expected bare variable name")]
    ExpectedBareVar,
}

pub fn parse_sexpr(s: &str) -> Result<Expr, SexprError> {
    let tokens = tokenize(s);
    let mut it: Toks = tokens.into_iter().peekable();
    let e = parse_one(&mut it)?;
    if it.peek().is_some() {
        return Err(SexprError::Trailing);
    }
    Ok(e)
}

type Toks = std::iter::Peekable<std::vec::IntoIter<String>>;

fn tokenize(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    for c in s.chars() {
        match c {
            '(' | ')' => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
                out.push(c.to_string());
            }
            c if c.is_whitespace() => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
            }
            c => cur.push(c),
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

fn parse_one(it: &mut Toks) -> Result<Expr, SexprError> {
    let tok = it.next().ok_or(SexprError::UnexpectedEof)?;
    match tok.as_str() {
        "(" => parse_compound(it),
        ")" => Err(SexprError::UnexpectedToken(")".into())),
        _ => parse_atom(&tok),
    }
}

fn parse_atom(tok: &str) -> Result<Expr, SexprError> {
    if let Some(name) = tok.strip_prefix("v:") {
        return Ok(Expr::Var(name.to_string()));
    }
    if let Some(name) = tok.strip_prefix("c:") {
        return parse_const(name).map(Expr::Const);
    }
    if let Some(rest) = tok.strip_prefix("n:") {
        return parse_lit(rest);
    }
    Err(SexprError::MalformedAtom(tok.into()))
}

fn parse_const(name: &str) -> Result<PhysConst, SexprError> {
    Ok(match name {
        "SpeedOfLight" => PhysConst::SpeedOfLight,
        "PlanckConst" => PhysConst::PlanckConst,
        "ReducedPlanck" => PhysConst::ReducedPlanck,
        "GravConst" => PhysConst::GravConst,
        "Boltzmann" => PhysConst::Boltzmann,
        "ElectronCharge" => PhysConst::ElectronCharge,
        "ElectronMass" => PhysConst::ElectronMass,
        "ProtonMass" => PhysConst::ProtonMass,
        "VacuumPermittivity" => PhysConst::VacuumPermittivity,
        "VacuumPermeability" => PhysConst::VacuumPermeability,
        "Avogadro" => PhysConst::Avogadro,
        "Pi" => PhysConst::Pi,
        "EulersNumber" => PhysConst::EulersNumber,
        _ => return Err(SexprError::UnknownConst(name.into())),
    })
}

fn parse_lit(rest: &str) -> Result<Expr, SexprError> {
    if let Some((n_str, d_str)) = rest.split_once('/') {
        let n: i64 = n_str
            .parse()
            .map_err(|_| SexprError::MalformedAtom(format!("n:{rest}")))?;
        let d: u64 = d_str
            .parse()
            .map_err(|_| SexprError::MalformedAtom(format!("n:{rest}")))?;
        Ok(Expr::Lit(n, d))
    } else {
        let n: i64 = rest
            .parse()
            .map_err(|_| SexprError::MalformedAtom(format!("n:{rest}")))?;
        Ok(Expr::Lit(n, 1))
    }
}

fn parse_compound(it: &mut Toks) -> Result<Expr, SexprError> {
    let op = it.next().ok_or(SexprError::UnexpectedEof)?;
    if op == "(" || op == ")" {
        return Err(SexprError::UnexpectedToken(op));
    }
    match op.as_str() {
        "deriv" => {
            let var = read_bare(it)?;
            let body = parse_one(it)?;
            expect_close(it, "deriv")?;
            Ok(Expr::Deriv(Box::new(body), var))
        }
        "partial" => {
            let var = read_bare(it)?;
            let body = parse_one(it)?;
            expect_close(it, "partial")?;
            Ok(Expr::PartialDeriv(Box::new(body), var))
        }
        "integral" => {
            let var = read_bare(it)?;
            let lower = parse_optional_bound(it)?;
            let upper = parse_optional_bound(it)?;
            let body = parse_one(it)?;
            expect_close(it, "integral")?;
            Ok(Expr::Integral {
                body: Box::new(body),
                var,
                lower,
                upper,
            })
        }
        "sum" => {
            let var = read_bare(it)?;
            let lower = parse_one(it)?;
            let upper = parse_one(it)?;
            let body = parse_one(it)?;
            expect_close(it, "sum")?;
            Ok(Expr::Sum {
                body: Box::new(body),
                var,
                lower: Box::new(lower),
                upper: Box::new(upper),
            })
        }
        "prod" => {
            let var = read_bare(it)?;
            let lower = parse_one(it)?;
            let upper = parse_one(it)?;
            let body = parse_one(it)?;
            expect_close(it, "prod")?;
            Ok(Expr::Prod {
                body: Box::new(body),
                var,
                lower: Box::new(lower),
                upper: Box::new(upper),
            })
        }
        "limit" => {
            let var = read_bare(it)?;
            let approaching = parse_one(it)?;
            let body = parse_one(it)?;
            expect_close(it, "limit")?;
            Ok(Expr::Limit {
                body: Box::new(body),
                var,
                approaching: Box::new(approaching),
            })
        }
        "lambda" => {
            let var = read_bare(it)?;
            let ty = parse_one(it)?;
            let body = parse_one(it)?;
            expect_close(it, "lambda")?;
            Ok(Expr::Lam(var, Box::new(ty), Box::new(body)))
        }
        "pi" => {
            let var = read_bare(it)?;
            let a = parse_one(it)?;
            let b = parse_one(it)?;
            expect_close(it, "pi")?;
            Ok(Expr::Pi(var, Box::new(a), Box::new(b)))
        }
        "let" => {
            let var = read_bare(it)?;
            let val = parse_one(it)?;
            let body = parse_one(it)?;
            expect_close(it, "let")?;
            Ok(Expr::Let(var, Box::new(val), Box::new(body)))
        }
        _ => {
            // Generic: collect args until ')'
            let mut args = Vec::new();
            loop {
                match it.peek() {
                    Some(t) if t == ")" => {
                        it.next();
                        break;
                    }
                    Some(_) => args.push(parse_one(it)?),
                    None => return Err(SexprError::UnexpectedEof),
                }
            }
            build_generic(&op, args)
        }
    }
}

fn read_bare(it: &mut Toks) -> Result<String, SexprError> {
    let tok = it.next().ok_or(SexprError::UnexpectedEof)?;
    if tok == "(" || tok == ")" {
        return Err(SexprError::ExpectedBareVar);
    }
    Ok(tok)
}

fn parse_optional_bound(it: &mut Toks) -> Result<Option<Box<Expr>>, SexprError> {
    // The `_` atom marks an absent bound.
    if matches!(it.peek(), Some(t) if t == "_") {
        it.next();
        Ok(None)
    } else {
        Ok(Some(Box::new(parse_one(it)?)))
    }
}

fn expect_close(it: &mut Toks, ctx: &str) -> Result<(), SexprError> {
    match it.next() {
        Some(t) if t == ")" => Ok(()),
        Some(t) => Err(SexprError::UnexpectedToken(format!("{t} (in `{ctx}`)"))),
        None => Err(SexprError::UnexpectedEof),
    }
}

fn build_generic(op: &str, mut args: Vec<Expr>) -> Result<Expr, SexprError> {
    if op == "@" {
        check_arity(op, &args, 2)?;
        return Ok(Expr::App(
            Box::new(args.remove(0)),
            Box::new(args.remove(0)),
        ));
    }
    if let Some(binop) = binop_from_str(op) {
        check_arity(op, &args, 2)?;
        return Ok(Expr::BinOp(
            binop,
            Box::new(args.remove(0)),
            Box::new(args.remove(0)),
        ));
    }
    if let Some(unop) = unop_from_str(op) {
        check_arity(op, &args, 1)?;
        return Ok(Expr::UnOp(unop, Box::new(args.remove(0))));
    }
    Err(SexprError::UnknownOp(op.into()))
}

fn check_arity(op: &str, args: &[Expr], expected: usize) -> Result<(), SexprError> {
    if args.len() == expected {
        Ok(())
    } else {
        Err(SexprError::Arity {
            op: op.into(),
            expected,
            got: args.len(),
        })
    }
}

fn binop_from_str(s: &str) -> Option<BinOp> {
    Some(match s {
        "+" => BinOp::Add,
        "-" => BinOp::Sub,
        "*" => BinOp::Mul,
        "/" => BinOp::Div,
        "^" => BinOp::Pow,
        "=" => BinOp::Eq,
        "!=" => BinOp::Ne,
        "<" => BinOp::Lt,
        "<=" => BinOp::Le,
        ">" => BinOp::Gt,
        ">=" => BinOp::Ge,
        "and" => BinOp::And,
        "or" => BinOp::Or,
        "->" => BinOp::Implies,
        "<->" => BinOp::Iff,
        "cross" => BinOp::Cross,
        "dot" => BinOp::Dot,
        "tensor" => BinOp::TensorProduct,
        _ => return None,
    })
}

fn unop_from_str(s: &str) -> Option<UnOp> {
    Some(match s {
        "neg" => UnOp::Neg,
        "abs" => UnOp::Abs,
        "sqrt" => UnOp::Sqrt,
        "sin" => UnOp::Sin,
        "cos" => UnOp::Cos,
        "tan" => UnOp::Tan,
        "exp" => UnOp::Exp,
        "log" => UnOp::Log,
        "ln" => UnOp::Ln,
        "grad" => UnOp::Grad,
        "div" => UnOp::Div,
        "curl" => UnOp::Curl,
        "laplacian" => UnOp::Laplacian,
        "transpose" => UnOp::Transpose,
        "conjugate" => UnOp::Conjugate,
        "trace" => UnOp::Trace,
        "det" => UnOp::Det,
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn round_trip(e: Expr) {
        let canon = e.to_canonical();
        let parsed = parse_sexpr(&canon).expect("parse");
        assert_eq!(parsed, e, "round-trip via `{canon}` produced different Expr");
        assert_eq!(parsed.to_canonical(), canon, "to_canonical not idempotent for {e:?}");
    }

    #[test]
    fn var() {
        round_trip(Expr::Var("x".into()));
    }

    #[test]
    fn const_speed_of_light() {
        round_trip(Expr::Const(PhysConst::SpeedOfLight));
    }

    #[test]
    fn lit_integer() {
        round_trip(Expr::Lit(42, 1));
    }

    #[test]
    fn lit_rational() {
        round_trip(Expr::Lit(1, 2));
    }

    #[test]
    fn lit_negative() {
        round_trip(Expr::Lit(-3, 4));
    }

    #[test]
    fn add() {
        round_trip(Expr::BinOp(
            BinOp::Add,
            Box::new(Expr::Var("a".into())),
            Box::new(Expr::Var("b".into())),
        ));
    }

    #[test]
    fn nested_eq_emc2() {
        // E = m * c^2
        let e = Expr::BinOp(
            BinOp::Eq,
            Box::new(Expr::Var("E".into())),
            Box::new(Expr::BinOp(
                BinOp::Mul,
                Box::new(Expr::Var("m".into())),
                Box::new(Expr::BinOp(
                    BinOp::Pow,
                    Box::new(Expr::Var("c".into())),
                    Box::new(Expr::Lit(2, 1)),
                )),
            )),
        );
        round_trip(e);
    }

    #[test]
    fn unary_sin_of_var() {
        round_trip(Expr::UnOp(UnOp::Sin, Box::new(Expr::Var("x".into()))));
    }

    #[test]
    fn deriv() {
        round_trip(Expr::Deriv(Box::new(Expr::Var("f".into())), "x".into()));
    }

    #[test]
    fn partial_deriv() {
        round_trip(Expr::PartialDeriv(
            Box::new(Expr::Var("psi".into())),
            "t".into(),
        ));
    }

    #[test]
    fn integral_with_bounds() {
        round_trip(Expr::Integral {
            body: Box::new(Expr::Var("f".into())),
            var: "x".into(),
            lower: Some(Box::new(Expr::Lit(0, 1))),
            upper: Some(Box::new(Expr::Var("L".into()))),
        });
    }

    #[test]
    fn integral_indefinite() {
        round_trip(Expr::Integral {
            body: Box::new(Expr::Var("f".into())),
            var: "x".into(),
            lower: None,
            upper: None,
        });
    }

    #[test]
    fn sum_with_bounds() {
        round_trip(Expr::Sum {
            body: Box::new(Expr::Var("i".into())),
            var: "i".into(),
            lower: Box::new(Expr::Lit(0, 1)),
            upper: Box::new(Expr::Var("n".into())),
        });
    }

    #[test]
    fn prod_with_bounds() {
        round_trip(Expr::Prod {
            body: Box::new(Expr::Var("i".into())),
            var: "i".into(),
            lower: Box::new(Expr::Lit(1, 1)),
            upper: Box::new(Expr::Var("n".into())),
        });
    }

    #[test]
    fn limit() {
        round_trip(Expr::Limit {
            body: Box::new(Expr::Var("f".into())),
            var: "x".into(),
            approaching: Box::new(Expr::Lit(0, 1)),
        });
    }

    #[test]
    fn lambda_pi_let() {
        round_trip(Expr::Lam(
            "x".into(),
            Box::new(Expr::Var("T".into())),
            Box::new(Expr::Var("x".into())),
        ));
        round_trip(Expr::Pi(
            "x".into(),
            Box::new(Expr::Var("A".into())),
            Box::new(Expr::Var("B".into())),
        ));
        round_trip(Expr::Let(
            "x".into(),
            Box::new(Expr::Lit(1, 1)),
            Box::new(Expr::Var("x".into())),
        ));
    }

    #[test]
    fn app_curried() {
        // f(x)(y) == App(App(f, x), y)
        let e = Expr::App(
            Box::new(Expr::App(
                Box::new(Expr::Var("f".into())),
                Box::new(Expr::Var("x".into())),
            )),
            Box::new(Expr::Var("y".into())),
        );
        round_trip(e);
    }

    #[test]
    fn implies_iff_and_or() {
        for op in [BinOp::Implies, BinOp::Iff, BinOp::And, BinOp::Or] {
            round_trip(Expr::BinOp(
                op,
                Box::new(Expr::Var("a".into())),
                Box::new(Expr::Var("b".into())),
            ));
        }
    }

    #[test]
    fn vector_ops() {
        for op in [BinOp::Cross, BinOp::Dot, BinOp::TensorProduct] {
            round_trip(Expr::BinOp(
                op,
                Box::new(Expr::Var("a".into())),
                Box::new(Expr::Var("b".into())),
            ));
        }
    }

    #[test]
    fn unknown_op_errors() {
        assert!(matches!(
            parse_sexpr("(WAT v:a v:b)"),
            Err(SexprError::UnknownOp(_))
        ));
    }

    #[test]
    fn malformed_atom_errors() {
        assert!(matches!(
            parse_sexpr("hello"),
            Err(SexprError::MalformedAtom(_))
        ));
    }

    #[test]
    fn trailing_tokens_error() {
        assert!(matches!(parse_sexpr("v:x v:y"), Err(SexprError::Trailing)));
    }
}
