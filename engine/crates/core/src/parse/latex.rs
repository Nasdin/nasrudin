//! LaTeX subset parser focused on what physicists type when stating a
//! conjecture in the search box.
//!
//! ## Supported
//! - Identifiers: bare ASCII letters, Greek macros (`\alpha`, `\Psi`, …),
//!   physics-constant macros (`\hbar`, `\pi`).
//! - Implicit multiplication between adjacent primaries: `mc^2` parses as
//!   `m * c^2`.
//! - Numbers (integers and decimals — decimals lower to reduced rationals).
//! - Infix `+ - * / =` and `\cdot`, `\times` (cross), `<`, `>`, `\leq`,
//!   `\geq`, `\neq`.
//! - Powers: `x^2`, `x^{n+1}`.
//! - Subscripts (merge into identifier name): `p_x`, `\psi_{0}` →
//!   `Var("p_x")`, `Var("psi_0")`.
//! - `\frac{a}{b}` → `a / b`.
//! - `\sqrt{a}` and named functions `\sin{x}`, `\cos{x}`, `\tan{x}`,
//!   `\exp{x}`, `\ln{x}`, `\log{x}`.
//! - Brackets: `(...)`, `\left(...\right)`, `\left[...\right]`.
//! - Commutator: `[a, b]` and `\left[a, b\right]` desugar to `a*b - b*a`.
//! - Thin-space macros `\,`, `\;`, `\:`, `\!` skipped.
//!
//! ## Not yet supported (returns [`LatexError::Unsupported`])
//! `\sum`, `\int`, `\partial`, `\nabla`, `\langle`/`\rangle`, primed
//! identifiers (`f'`), `\sin^2 x` exponent-on-function form, matrices,
//! `\begin{...}\end{...}` environments. Add to [`MACRO_ALIASES`] and
//! tokenizer as needed.

use crate::expr::{BinOp, Expr, PhysConst, UnOp};
use thiserror::Error;

#[derive(Debug, Error, PartialEq)]
pub enum LatexError {
    #[error("unexpected end of input")]
    UnexpectedEof,
    #[error("unexpected character `{0}` at byte {1}")]
    UnexpectedChar(char, usize),
    #[error("unexpected token `{tok}` at byte {pos}")]
    UnexpectedToken { tok: String, pos: usize },
    #[error("unsupported LaTeX command `\\{0}` at byte {1}")]
    Unsupported(String, usize),
    #[error("invalid number `{0}` at byte {1}")]
    InvalidNumber(String, usize),
    #[error("expected `{0}` at byte {1}")]
    Expected(String, usize),
    #[error("trailing input at byte {0}")]
    Trailing(usize),
    #[error("commutator `[a, b]` must contain exactly two comma-separated operands")]
    BadCommutator,
}

pub fn parse_latex(s: &str) -> Result<Expr, LatexError> {
    let tokens = tokenize(s)?;
    let mut p = Parser { tokens, pos: 0 };
    let e = p.parse_expr()?;
    if let Some(t) = p.peek() {
        return Err(LatexError::Trailing(t.byte_off));
    }
    Ok(e)
}

#[derive(Clone, Debug)]
struct Tok {
    kind: Tk,
    text: String,
    byte_off: usize,
}

#[derive(Clone, Debug, PartialEq)]
enum Tk {
    Num,
    Letter,        // single ASCII letter
    Macro,         // \name (excluding \left, \right, spacing macros which are handled specially)
    LBrace,        // {
    RBrace,        // }
    LParen,
    RParen,
    LBracket,
    RBracket,
    Comma,
    Caret,
    Underscore,
    Plus,
    Minus,
    Star,
    Slash,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Cdot,
    Cross,         // \times
}

fn tokenize(s: &str) -> Result<Vec<Tok>, LatexError> {
    let bytes = s.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i] as char;
        let start = i;
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        match c {
            '{' => { out.push(t(Tk::LBrace, "{".into(), start)); i += 1; }
            '}' => { out.push(t(Tk::RBrace, "}".into(), start)); i += 1; }
            '(' => { out.push(t(Tk::LParen, "(".into(), start)); i += 1; }
            ')' => { out.push(t(Tk::RParen, ")".into(), start)); i += 1; }
            '[' => { out.push(t(Tk::LBracket, "[".into(), start)); i += 1; }
            ']' => { out.push(t(Tk::RBracket, "]".into(), start)); i += 1; }
            ',' => { out.push(t(Tk::Comma, ",".into(), start)); i += 1; }
            '^' => { out.push(t(Tk::Caret, "^".into(), start)); i += 1; }
            '_' => { out.push(t(Tk::Underscore, "_".into(), start)); i += 1; }
            '+' => { out.push(t(Tk::Plus, "+".into(), start)); i += 1; }
            '-' => { out.push(t(Tk::Minus, "-".into(), start)); i += 1; }
            '*' => { out.push(t(Tk::Star, "*".into(), start)); i += 1; }
            '/' => { out.push(t(Tk::Slash, "/".into(), start)); i += 1; }
            '=' => { out.push(t(Tk::Eq, "=".into(), start)); i += 1; }
            '<' => { out.push(t(Tk::Lt, "<".into(), start)); i += 1; }
            '>' => { out.push(t(Tk::Gt, ">".into(), start)); i += 1; }
            c if c.is_ascii_alphabetic() => {
                out.push(t(Tk::Letter, c.to_string(), start));
                i += 1;
            }
            c if c.is_ascii_digit() => {
                let mut j = i;
                while j < bytes.len() && (bytes[j].is_ascii_digit() || bytes[j] == b'.') {
                    j += 1;
                }
                let text = s[i..j].to_string();
                out.push(t(Tk::Num, text, start));
                i = j;
            }
            '\\' => {
                // Macro: \name or \,/\;/\:/\!
                let next = bytes.get(i + 1).copied();
                match next {
                    Some(b',' | b';' | b':' | b'!') => {
                        i += 2; // skip thin-space macro
                        continue;
                    }
                    Some(b) if (b as char).is_ascii_alphabetic() => {
                        let mut j = i + 1;
                        while j < bytes.len() && (bytes[j] as char).is_ascii_alphabetic() {
                            j += 1;
                        }
                        let name = &s[i + 1..j];
                        match name {
                            "left" | "right" => {
                                // Eat the macro and let the following delim be tokenized normally.
                                i = j;
                                continue;
                            }
                            "cdot" => out.push(t(Tk::Cdot, "\\cdot".into(), start)),
                            "times" => out.push(t(Tk::Cross, "\\times".into(), start)),
                            "neq" | "ne" => out.push(t(Tk::Ne, format!("\\{name}"), start)),
                            "leq" | "le" => out.push(t(Tk::Le, format!("\\{name}"), start)),
                            "geq" | "ge" => out.push(t(Tk::Ge, format!("\\{name}"), start)),
                            _ => out.push(t(Tk::Macro, name.to_string(), start)),
                        }
                        i = j;
                    }
                    _ => return Err(LatexError::UnexpectedChar('\\', start)),
                }
            }
            other => return Err(LatexError::UnexpectedChar(other, start)),
        }
    }
    Ok(out)
}

fn t(kind: Tk, text: String, byte_off: usize) -> Tok {
    Tok { kind, text, byte_off }
}

struct Parser {
    tokens: Vec<Tok>,
    pos: usize,
}

impl Parser {
    fn peek(&self) -> Option<&Tok> {
        self.tokens.get(self.pos)
    }
    fn peek_kind(&self) -> Option<&Tk> {
        self.tokens.get(self.pos).map(|t| &t.kind)
    }
    fn bump(&mut self) -> Option<Tok> {
        let t = self.tokens.get(self.pos).cloned();
        if t.is_some() {
            self.pos += 1;
        }
        t
    }
    fn eat(&mut self, kind: Tk) -> bool {
        if self.peek_kind() == Some(&kind) {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    fn expect(&mut self, kind: Tk, label: &str) -> Result<Tok, LatexError> {
        let off = self.peek().map(|t| t.byte_off).unwrap_or(0);
        match self.bump() {
            Some(t) if t.kind == kind => Ok(t),
            Some(t) => Err(LatexError::UnexpectedToken { tok: t.text, pos: t.byte_off }),
            None => Err(LatexError::Expected(label.into(), off)),
        }
    }

    fn parse_expr(&mut self) -> Result<Expr, LatexError> {
        self.parse_eq()
    }

    fn parse_eq(&mut self) -> Result<Expr, LatexError> {
        let lhs = self.parse_cmp()?;
        if let Some(op) = match self.peek_kind() {
            Some(Tk::Eq) => Some(BinOp::Eq),
            Some(Tk::Ne) => Some(BinOp::Ne),
            _ => None,
        } {
            self.bump();
            let rhs = self.parse_cmp()?;
            return Ok(bin(op, lhs, rhs));
        }
        Ok(lhs)
    }

    fn parse_cmp(&mut self) -> Result<Expr, LatexError> {
        let lhs = self.parse_add()?;
        if let Some(op) = match self.peek_kind() {
            Some(Tk::Lt) => Some(BinOp::Lt),
            Some(Tk::Le) => Some(BinOp::Le),
            Some(Tk::Gt) => Some(BinOp::Gt),
            Some(Tk::Ge) => Some(BinOp::Ge),
            _ => None,
        } {
            self.bump();
            let rhs = self.parse_add()?;
            return Ok(bin(op, lhs, rhs));
        }
        Ok(lhs)
    }

    fn parse_add(&mut self) -> Result<Expr, LatexError> {
        let mut lhs = self.parse_mul()?;
        loop {
            let op = match self.peek_kind() {
                Some(Tk::Plus) => BinOp::Add,
                Some(Tk::Minus) => BinOp::Sub,
                _ => break,
            };
            self.bump();
            let rhs = self.parse_mul()?;
            lhs = bin(op, lhs, rhs);
        }
        Ok(lhs)
    }

    fn parse_mul(&mut self) -> Result<Expr, LatexError> {
        let mut lhs = self.parse_unary()?;
        loop {
            let op = match self.peek_kind() {
                Some(Tk::Star) | Some(Tk::Cdot) => BinOp::Mul,
                Some(Tk::Slash) => BinOp::Div,
                Some(Tk::Cross) => BinOp::Cross,
                // Implicit multiplication if next token starts a primary.
                Some(k) if starts_primary(k) => BinOp::Mul,
                _ => break,
            };
            // Consume only if explicit op
            match self.peek_kind() {
                Some(Tk::Star) | Some(Tk::Cdot) | Some(Tk::Slash) | Some(Tk::Cross) => {
                    self.bump();
                }
                _ => {} // implicit; do not consume
            }
            let rhs = self.parse_unary()?;
            lhs = bin(op, lhs, rhs);
        }
        Ok(lhs)
    }

    fn parse_unary(&mut self) -> Result<Expr, LatexError> {
        if self.eat(Tk::Minus) {
            let inner = self.parse_unary()?;
            return Ok(Expr::UnOp(UnOp::Neg, Box::new(inner)));
        }
        self.parse_postfix()
    }

    /// Primary, then any chain of `^`, `_` postfix operators.
    fn parse_postfix(&mut self) -> Result<Expr, LatexError> {
        let mut base = self.parse_primary()?;
        loop {
            match self.peek_kind() {
                Some(Tk::Caret) => {
                    self.bump();
                    let exp = self.parse_braced_or_atom()?;
                    base = bin(BinOp::Pow, base, exp);
                }
                Some(Tk::Underscore) => {
                    self.bump();
                    let sub = self.parse_subscript_text()?;
                    base = merge_subscript(base, &sub);
                }
                _ => break,
            }
        }
        Ok(base)
    }

    fn parse_braced_or_atom(&mut self) -> Result<Expr, LatexError> {
        if self.eat(Tk::LBrace) {
            let inner = self.parse_expr()?;
            self.expect(Tk::RBrace, "}")?;
            Ok(inner)
        } else {
            self.parse_primary()
        }
    }

    /// Subscripts collapse into the identifier name. Only allow simple
    /// subscript content (a single letter, digit run, macro, or braced
    /// sequence of letters/digits/macros).
    fn parse_subscript_text(&mut self) -> Result<String, LatexError> {
        if self.eat(Tk::LBrace) {
            let mut buf = String::new();
            while let Some(k) = self.peek_kind() {
                if matches!(k, Tk::RBrace) {
                    break;
                }
                let tok = self.bump().unwrap();
                match tok.kind {
                    Tk::Letter | Tk::Num => buf.push_str(&tok.text),
                    Tk::Macro => buf.push_str(&tok.text),
                    Tk::Comma => buf.push(','),
                    _ => return Err(LatexError::UnexpectedToken {
                        tok: tok.text,
                        pos: tok.byte_off,
                    }),
                }
            }
            self.expect(Tk::RBrace, "}")?;
            Ok(buf)
        } else {
            let tok = self.bump().ok_or(LatexError::UnexpectedEof)?;
            match tok.kind {
                Tk::Letter | Tk::Num | Tk::Macro => Ok(tok.text),
                _ => Err(LatexError::UnexpectedToken { tok: tok.text, pos: tok.byte_off }),
            }
        }
    }

    fn parse_primary(&mut self) -> Result<Expr, LatexError> {
        let tok = self.bump().ok_or(LatexError::UnexpectedEof)?;
        match tok.kind {
            Tk::Num => parse_num(&tok.text, tok.byte_off),
            Tk::Letter => Ok(letter_to_expr(&tok.text)),
            Tk::Macro => self.handle_macro(&tok.text, tok.byte_off),
            Tk::LParen => {
                let inner = self.parse_expr()?;
                self.expect(Tk::RParen, ")")?;
                Ok(inner)
            }
            Tk::LBracket => {
                // Commutator: [a, b] → a*b - b*a
                let a = self.parse_expr()?;
                self.expect(Tk::Comma, ",").map_err(|_| LatexError::BadCommutator)?;
                let b = self.parse_expr()?;
                self.expect(Tk::RBracket, "]").map_err(|_| LatexError::BadCommutator)?;
                Ok(bin(
                    BinOp::Sub,
                    bin(BinOp::Mul, a.clone(), b.clone()),
                    bin(BinOp::Mul, b, a),
                ))
            }
            Tk::LBrace => {
                // Braced group
                let inner = self.parse_expr()?;
                self.expect(Tk::RBrace, "}")?;
                Ok(inner)
            }
            _ => Err(LatexError::UnexpectedToken { tok: tok.text, pos: tok.byte_off }),
        }
    }

    fn handle_macro(&mut self, name: &str, off: usize) -> Result<Expr, LatexError> {
        // Physics-constant alias?
        if let Some(c) = phys_const_alias(name) {
            return Ok(Expr::Const(c));
        }
        // Greek/identifier alias?
        if is_greek(name) {
            return Ok(Expr::Var(name.to_string()));
        }
        // Built-in functions
        match name {
            "frac" => {
                let num = self.parse_braced()?;
                let den = self.parse_braced()?;
                Ok(bin(BinOp::Div, num, den))
            }
            "sqrt" => {
                let inner = self.parse_braced()?;
                Ok(Expr::UnOp(UnOp::Sqrt, Box::new(inner)))
            }
            "sin" | "cos" | "tan" | "exp" | "ln" | "log" => {
                let arg = self.parse_func_arg()?;
                let op = match name {
                    "sin" => UnOp::Sin,
                    "cos" => UnOp::Cos,
                    "tan" => UnOp::Tan,
                    "exp" => UnOp::Exp,
                    "ln" => UnOp::Ln,
                    "log" => UnOp::Log,
                    _ => unreachable!(),
                };
                Ok(Expr::UnOp(op, Box::new(arg)))
            }
            "sum" | "int" | "partial" | "nabla" | "langle" | "rangle" | "prod" | "lim" => {
                Err(LatexError::Unsupported(name.into(), off))
            }
            _ => Err(LatexError::Unsupported(name.into(), off)),
        }
    }

    fn parse_braced(&mut self) -> Result<Expr, LatexError> {
        self.expect(Tk::LBrace, "{")?;
        let inner = self.parse_expr()?;
        self.expect(Tk::RBrace, "}")?;
        Ok(inner)
    }

    /// `\sin{x}` or `\sin x` — accept either a braced group or a single
    /// primary token.
    fn parse_func_arg(&mut self) -> Result<Expr, LatexError> {
        if matches!(self.peek_kind(), Some(Tk::LBrace)) {
            self.parse_braced()
        } else {
            self.parse_primary()
        }
    }
}

fn starts_primary(k: &Tk) -> bool {
    matches!(
        k,
        Tk::Num
            | Tk::Letter
            | Tk::Macro
            | Tk::LParen
            | Tk::LBracket
            | Tk::LBrace
    )
}

fn letter_to_expr(s: &str) -> Expr {
    match s {
        "c" => Expr::Const(PhysConst::SpeedOfLight),
        "G" => Expr::Const(PhysConst::GravConst),
        _ => Expr::Var(s.into()),
    }
}

fn phys_const_alias(name: &str) -> Option<PhysConst> {
    Some(match name {
        "hbar" => PhysConst::ReducedPlanck,
        _ => return None,
    })
}

const GREEK: &[&str] = &[
    "alpha", "beta", "gamma", "delta", "epsilon", "varepsilon", "zeta", "eta", "theta",
    "vartheta", "iota", "kappa", "lambda", "mu", "nu", "xi", "pi", "varpi", "rho", "varrho",
    "sigma", "varsigma", "tau", "upsilon", "phi", "varphi", "chi", "psi", "omega",
    "Gamma", "Delta", "Theta", "Lambda", "Xi", "Pi", "Sigma", "Upsilon", "Phi", "Psi", "Omega",
];

fn is_greek(name: &str) -> bool {
    GREEK.contains(&name)
}

fn merge_subscript(base: Expr, sub: &str) -> Expr {
    match base {
        Expr::Var(name) => Expr::Var(format!("{name}_{sub}")),
        // Physics constants don't take subscripts in this lowering — wrap
        // with App to indicate index, preserving the constant identity.
        other => Expr::App(Box::new(other), Box::new(Expr::Var(sub.into()))),
    }
}

fn parse_num(text: &str, off: usize) -> Result<Expr, LatexError> {
    if let Some((int_part, frac_part)) = text.split_once('.') {
        let k = frac_part.len() as u32;
        let denom = 10u64.pow(k);
        let combined = format!("{int_part}{frac_part}");
        let n: i64 = combined
            .parse()
            .map_err(|_| LatexError::InvalidNumber(text.into(), off))?;
        Ok(reduce_lit(n, denom))
    } else {
        let n: i64 = text
            .parse()
            .map_err(|_| LatexError::InvalidNumber(text.into(), off))?;
        Ok(Expr::Lit(n, 1))
    }
}

fn reduce_lit(n: i64, d: u64) -> Expr {
    if n == 0 {
        return Expr::Lit(0, 1);
    }
    let g = gcd(n.unsigned_abs(), d);
    Expr::Lit(n / g as i64, d / g)
}

fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 { a.max(1) } else { gcd(b, a % b) }
}

fn bin(op: BinOp, l: Expr, r: Expr) -> Expr {
    Expr::BinOp(op, Box::new(l), Box::new(r))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::canonical_ac::canonical_ac_hash;

    fn p(s: &str) -> Expr {
        parse_latex(s).unwrap_or_else(|e| panic!("`{s}`: {e}"))
    }

    #[test]
    fn integer() {
        assert_eq!(p("42"), Expr::Lit(42, 1));
    }

    #[test]
    fn decimal() {
        assert_eq!(p("0.5"), Expr::Lit(1, 2));
    }

    #[test]
    fn single_letter_var() {
        assert_eq!(p("x"), Expr::Var("x".into()));
    }

    #[test]
    fn c_resolves_to_speed_of_light() {
        assert_eq!(p("c"), Expr::Const(PhysConst::SpeedOfLight));
    }

    #[test]
    fn implicit_multiplication() {
        // mc^2 → m * c^2
        let e = p("mc^2");
        let expected = bin(
            BinOp::Mul,
            Expr::Var("m".into()),
            bin(BinOp::Pow, Expr::Const(PhysConst::SpeedOfLight), Expr::Lit(2, 1)),
        );
        assert_eq!(e, expected);
    }

    #[test]
    fn frac() {
        let e = p("\\frac{1}{2}");
        assert_eq!(
            e,
            bin(BinOp::Div, Expr::Lit(1, 1), Expr::Lit(2, 1))
        );
    }

    #[test]
    fn sqrt() {
        let e = p("\\sqrt{x}");
        assert_eq!(e, Expr::UnOp(UnOp::Sqrt, Box::new(Expr::Var("x".into()))));
    }

    #[test]
    fn greek_macro() {
        assert_eq!(p("\\psi"), Expr::Var("psi".into()));
        assert_eq!(p("\\Omega"), Expr::Var("Omega".into()));
    }

    #[test]
    fn hbar_macro() {
        assert_eq!(p("\\hbar"), Expr::Const(PhysConst::ReducedPlanck));
    }

    #[test]
    fn power_braced() {
        let e = p("x^{n+1}");
        let expected = bin(
            BinOp::Pow,
            Expr::Var("x".into()),
            bin(BinOp::Add, Expr::Var("n".into()), Expr::Lit(1, 1)),
        );
        assert_eq!(e, expected);
    }

    #[test]
    fn subscript_merges_into_var_name() {
        assert_eq!(p("p_x"), Expr::Var("p_x".into()));
        assert_eq!(p("\\psi_{0}"), Expr::Var("psi_0".into()));
    }

    #[test]
    fn cdot_is_mul() {
        let e = p("a \\cdot b");
        assert_eq!(e, bin(BinOp::Mul, Expr::Var("a".into()), Expr::Var("b".into())));
    }

    #[test]
    fn times_is_cross() {
        let e = p("a \\times b");
        assert_eq!(
            e,
            bin(BinOp::Cross, Expr::Var("a".into()), Expr::Var("b".into()))
        );
    }

    #[test]
    fn comparisons() {
        assert_eq!(
            p("a \\leq b"),
            bin(BinOp::Le, Expr::Var("a".into()), Expr::Var("b".into()))
        );
        assert_eq!(
            p("a \\neq b"),
            bin(BinOp::Ne, Expr::Var("a".into()), Expr::Var("b".into()))
        );
    }

    #[test]
    fn left_right_brackets() {
        let e = p("\\left( a + b \\right)");
        assert_eq!(
            e,
            bin(BinOp::Add, Expr::Var("a".into()), Expr::Var("b".into()))
        );
    }

    #[test]
    fn commutator_xp_eq_i_hbar_via_latex() {
        let conjecture = p("[x, p] = i \\hbar");
        let reference = p("xp - px = i \\hbar");
        assert_eq!(
            canonical_ac_hash(&conjecture),
            canonical_ac_hash(&reference)
        );
    }

    #[test]
    fn emc2_full() {
        let e = p("E = mc^2");
        let expected = bin(
            BinOp::Eq,
            Expr::Var("E".into()),
            bin(
                BinOp::Mul,
                Expr::Var("m".into()),
                bin(BinOp::Pow, Expr::Const(PhysConst::SpeedOfLight), Expr::Lit(2, 1)),
            ),
        );
        assert_eq!(e, expected);
    }

    #[test]
    fn energy_momentum_relation() {
        // E^2 = (pc)^2 + (mc^2)^2
        let lhs = p("E^2");
        let rhs = p("(pc)^2 + (mc^2)^2");
        let full = bin(BinOp::Eq, lhs.clone(), rhs.clone());
        // AC-hash should be stable under term reordering on RHS
        let reordered = bin(BinOp::Eq, lhs, p("(mc^2)^2 + (pc)^2"));
        assert_eq!(canonical_ac_hash(&full), canonical_ac_hash(&reordered));
    }

    #[test]
    fn unsupported_sum_errors() {
        match parse_latex("\\sum x") {
            Err(LatexError::Unsupported(name, _)) => assert_eq!(name, "sum"),
            other => panic!("expected Unsupported, got {other:?}"),
        }
    }

    #[test]
    fn unknown_macro_errors_as_unsupported() {
        match parse_latex("\\foo") {
            Err(LatexError::Unsupported(name, _)) => assert_eq!(name, "foo"),
            other => panic!("expected Unsupported, got {other:?}"),
        }
    }

    #[test]
    fn thin_space_is_skipped() {
        assert_eq!(p("a \\, b"), bin(BinOp::Mul, Expr::Var("a".into()), Expr::Var("b".into())));
    }

    #[test]
    fn sin_with_braces_and_without() {
        assert_eq!(
            p("\\sin{x}"),
            Expr::UnOp(UnOp::Sin, Box::new(Expr::Var("x".into())))
        );
        assert_eq!(
            p("\\sin x"),
            Expr::UnOp(UnOp::Sin, Box::new(Expr::Var("x".into())))
        );
    }
}
