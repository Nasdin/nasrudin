//! Simple math parser: infix arithmetic + comparisons + booleans, function
//! calls, subscripted identifiers, physics-constant aliases, and commutator
//! brackets.
//!
//! Grammar (lowest → highest precedence):
//!   `or > and > eq/ne > comparisons > add/sub > mul/div > pow > unary > primary`
//!
//! Sugar:
//!   * `[a, b]` — commutator, expands to `a*b - b*a`.
//!   * `f(x)` — when `f` matches a built-in unary (`sin`, `cos`, `tan`, `exp`,
//!     `log`, `ln`, `sqrt`, `abs`) it lowers to [`UnOp`]. Otherwise to
//!     curried [`Expr::App`].
//!   * Identifier-as-physics-constant: `hbar`, `pi`, `c`, `G`, `k_B`, `N_A`,
//!     `eps0`, `mu0`, `m_e`, `m_p` resolve to the corresponding [`PhysConst`].

use crate::expr::{BinOp, Expr, PhysConst, UnOp};
use thiserror::Error;

#[derive(Debug, Error, PartialEq)]
pub enum SimpleError {
    #[error("unexpected end of input")]
    UnexpectedEof,
    #[error("unexpected character `{0}` at byte {1}")]
    UnexpectedChar(char, usize),
    #[error("unexpected token `{tok}` at byte {pos}")]
    UnexpectedToken { tok: String, pos: usize },
    #[error("invalid number `{0}` at byte {1}")]
    InvalidNumber(String, usize),
    #[error("expected `{expected}` at byte {pos}")]
    Expected { expected: String, pos: usize },
    #[error("trailing input at byte {0}")]
    Trailing(usize),
    #[error("commutator `[a, b]` must contain exactly two comma-separated operands")]
    BadCommutator,
}

pub fn parse_simple(s: &str) -> Result<Expr, SimpleError> {
    let tokens = tokenize(s)?;
    let mut p = Parser { tokens, pos: 0 };
    let e = p.parse_expr()?;
    if let Some(t) = p.peek() {
        return Err(SimpleError::Trailing(t.byte_off));
    }
    Ok(e)
}

#[derive(Clone, Debug)]
struct Token {
    kind: Tk,
    text: String,
    byte_off: usize,
}

#[derive(Clone, Debug, PartialEq)]
enum Tk {
    Num,
    Ident,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Comma,
    Plus,
    Minus,
    Star,
    Slash,
    Caret,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    AndKw,
    OrKw,
}

fn tokenize(s: &str) -> Result<Vec<Token>, SimpleError> {
    let bytes = s.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i] as char;
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        let start = i;
        let push = |out: &mut Vec<Token>, kind: Tk, text: String, off: usize| {
            out.push(Token { kind, text, byte_off: off })
        };
        match c {
            '(' => { push(&mut out, Tk::LParen, "(".into(), start); i += 1; }
            ')' => { push(&mut out, Tk::RParen, ")".into(), start); i += 1; }
            '[' => { push(&mut out, Tk::LBracket, "[".into(), start); i += 1; }
            ']' => { push(&mut out, Tk::RBracket, "]".into(), start); i += 1; }
            ',' => { push(&mut out, Tk::Comma, ",".into(), start); i += 1; }
            '+' => { push(&mut out, Tk::Plus, "+".into(), start); i += 1; }
            '-' => { push(&mut out, Tk::Minus, "-".into(), start); i += 1; }
            '*' => { push(&mut out, Tk::Star, "*".into(), start); i += 1; }
            '/' => { push(&mut out, Tk::Slash, "/".into(), start); i += 1; }
            '^' => { push(&mut out, Tk::Caret, "^".into(), start); i += 1; }
            '=' => { push(&mut out, Tk::Eq, "=".into(), start); i += 1; }
            '!' => {
                if bytes.get(i + 1) == Some(&b'=') {
                    push(&mut out, Tk::Ne, "!=".into(), start);
                    i += 2;
                } else {
                    return Err(SimpleError::UnexpectedChar('!', start));
                }
            }
            '<' => {
                if bytes.get(i + 1) == Some(&b'=') {
                    push(&mut out, Tk::Le, "<=".into(), start);
                    i += 2;
                } else {
                    push(&mut out, Tk::Lt, "<".into(), start);
                    i += 1;
                }
            }
            '>' => {
                if bytes.get(i + 1) == Some(&b'=') {
                    push(&mut out, Tk::Ge, ">=".into(), start);
                    i += 2;
                } else {
                    push(&mut out, Tk::Gt, ">".into(), start);
                    i += 1;
                }
            }
            c if c.is_ascii_digit() => {
                let mut j = i;
                while j < bytes.len() && (bytes[j].is_ascii_digit() || bytes[j] == b'.') {
                    j += 1;
                }
                let text = s[i..j].to_string();
                push(&mut out, Tk::Num, text, start);
                i = j;
            }
            c if is_ident_start(c) => {
                let mut j = i;
                while j < bytes.len() && is_ident_cont(bytes[j] as char) {
                    j += 1;
                }
                let text = s[i..j].to_string();
                let kind = match text.as_str() {
                    "and" => Tk::AndKw,
                    "or" => Tk::OrKw,
                    _ => Tk::Ident,
                };
                push(&mut out, kind, text, start);
                i = j;
            }
            other => return Err(SimpleError::UnexpectedChar(other, start)),
        }
    }
    Ok(out)
}

fn is_ident_start(c: char) -> bool {
    c == '_' || c.is_ascii_alphabetic()
}

fn is_ident_cont(c: char) -> bool {
    c == '_' || c.is_ascii_alphanumeric()
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }
    fn bump(&mut self) -> Option<Token> {
        let t = self.tokens.get(self.pos).cloned();
        if t.is_some() {
            self.pos += 1;
        }
        t
    }
    fn eat(&mut self, kind: Tk) -> bool {
        if self.peek().map(|t| &t.kind) == Some(&kind) {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    fn expect(&mut self, kind: Tk, label: &str) -> Result<Token, SimpleError> {
        let off = self.peek().map(|t| t.byte_off).unwrap_or(0);
        match self.bump() {
            Some(t) if t.kind == kind => Ok(t),
            Some(t) => Err(SimpleError::UnexpectedToken { tok: t.text, pos: t.byte_off }),
            None => Err(SimpleError::Expected { expected: label.into(), pos: off }),
        }
    }

    fn parse_expr(&mut self) -> Result<Expr, SimpleError> {
        self.parse_or()
    }

    fn parse_or(&mut self) -> Result<Expr, SimpleError> {
        let mut lhs = self.parse_and()?;
        while self.eat(Tk::OrKw) {
            let rhs = self.parse_and()?;
            lhs = bin(BinOp::Or, lhs, rhs);
        }
        Ok(lhs)
    }

    fn parse_and(&mut self) -> Result<Expr, SimpleError> {
        let mut lhs = self.parse_eq()?;
        while self.eat(Tk::AndKw) {
            let rhs = self.parse_eq()?;
            lhs = bin(BinOp::And, lhs, rhs);
        }
        Ok(lhs)
    }

    fn parse_eq(&mut self) -> Result<Expr, SimpleError> {
        let lhs = self.parse_cmp()?;
        if let Some(t) = self.peek() {
            let op = match t.kind {
                Tk::Eq => Some(BinOp::Eq),
                Tk::Ne => Some(BinOp::Ne),
                _ => None,
            };
            if let Some(op) = op {
                self.bump();
                let rhs = self.parse_cmp()?;
                return Ok(bin(op, lhs, rhs));
            }
        }
        Ok(lhs)
    }

    fn parse_cmp(&mut self) -> Result<Expr, SimpleError> {
        let lhs = self.parse_add()?;
        if let Some(t) = self.peek() {
            let op = match t.kind {
                Tk::Lt => Some(BinOp::Lt),
                Tk::Le => Some(BinOp::Le),
                Tk::Gt => Some(BinOp::Gt),
                Tk::Ge => Some(BinOp::Ge),
                _ => None,
            };
            if let Some(op) = op {
                self.bump();
                let rhs = self.parse_add()?;
                return Ok(bin(op, lhs, rhs));
            }
        }
        Ok(lhs)
    }

    fn parse_add(&mut self) -> Result<Expr, SimpleError> {
        let mut lhs = self.parse_mul()?;
        loop {
            let op = match self.peek().map(|t| &t.kind) {
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

    fn parse_mul(&mut self) -> Result<Expr, SimpleError> {
        let mut lhs = self.parse_pow()?;
        loop {
            let op = match self.peek().map(|t| &t.kind) {
                Some(Tk::Star) => BinOp::Mul,
                Some(Tk::Slash) => BinOp::Div,
                _ => break,
            };
            self.bump();
            let rhs = self.parse_pow()?;
            lhs = bin(op, lhs, rhs);
        }
        Ok(lhs)
    }

    fn parse_pow(&mut self) -> Result<Expr, SimpleError> {
        let lhs = self.parse_unary()?;
        if self.eat(Tk::Caret) {
            // right-associative
            let rhs = self.parse_pow()?;
            return Ok(bin(BinOp::Pow, lhs, rhs));
        }
        Ok(lhs)
    }

    fn parse_unary(&mut self) -> Result<Expr, SimpleError> {
        if self.eat(Tk::Minus) {
            let inner = self.parse_unary()?;
            return Ok(Expr::UnOp(UnOp::Neg, Box::new(inner)));
        }
        self.parse_primary()
    }

    fn parse_primary(&mut self) -> Result<Expr, SimpleError> {
        let off = self.peek().map(|t| t.byte_off).unwrap_or(0);
        let t = self.bump().ok_or(SimpleError::UnexpectedEof)?;
        match t.kind {
            Tk::Num => parse_num(&t.text, t.byte_off),
            Tk::Ident => self.finish_ident(t.text),
            Tk::LParen => {
                let inner = self.parse_expr()?;
                self.expect(Tk::RParen, ")")?;
                Ok(inner)
            }
            Tk::LBracket => {
                // Commutator: [a, b] → a*b - b*a
                let a = self.parse_expr()?;
                self.expect(Tk::Comma, ",").map_err(|_| SimpleError::BadCommutator)?;
                let b = self.parse_expr()?;
                self.expect(Tk::RBracket, "]").map_err(|_| SimpleError::BadCommutator)?;
                Ok(bin(
                    BinOp::Sub,
                    bin(BinOp::Mul, a.clone(), b.clone()),
                    bin(BinOp::Mul, b, a),
                ))
            }
            _ => Err(SimpleError::UnexpectedToken { tok: t.text, pos: off }),
        }
    }

    fn finish_ident(&mut self, name: String) -> Result<Expr, SimpleError> {
        // Function-call form: ident '(' arg ')'
        if self.eat(Tk::LParen) {
            let arg = self.parse_expr()?;
            self.expect(Tk::RParen, ")")?;
            return Ok(unary_or_app(&name, arg));
        }
        Ok(ident_to_expr(&name))
    }
}

fn ident_to_expr(name: &str) -> Expr {
    if let Some(c) = phys_const_alias(name) {
        Expr::Const(c)
    } else {
        Expr::Var(name.into())
    }
}

fn phys_const_alias(name: &str) -> Option<PhysConst> {
    Some(match name {
        "hbar" => PhysConst::ReducedPlanck,
        "h_planck" => PhysConst::PlanckConst,
        "pi" => PhysConst::Pi,
        "c" => PhysConst::SpeedOfLight,
        "G" => PhysConst::GravConst,
        "k_B" => PhysConst::Boltzmann,
        "N_A" => PhysConst::Avogadro,
        "eps0" => PhysConst::VacuumPermittivity,
        "mu0" => PhysConst::VacuumPermeability,
        "m_e" => PhysConst::ElectronMass,
        "m_p" => PhysConst::ProtonMass,
        _ => return None,
    })
}

fn unary_or_app(name: &str, arg: Expr) -> Expr {
    let unop = match name {
        "sin" => Some(UnOp::Sin),
        "cos" => Some(UnOp::Cos),
        "tan" => Some(UnOp::Tan),
        "exp" => Some(UnOp::Exp),
        "log" => Some(UnOp::Log),
        "ln" => Some(UnOp::Ln),
        "sqrt" => Some(UnOp::Sqrt),
        "abs" => Some(UnOp::Abs),
        _ => None,
    };
    if let Some(op) = unop {
        Expr::UnOp(op, Box::new(arg))
    } else {
        Expr::App(Box::new(Expr::Var(name.into())), Box::new(arg))
    }
}

fn parse_num(text: &str, off: usize) -> Result<Expr, SimpleError> {
    if let Some((int_part, frac_part)) = text.split_once('.') {
        // Decimal: a.bcd → (a*10^k + bcd) / 10^k
        let k = frac_part.len() as u32;
        let denom = 10u64.pow(k);
        let combined = format!("{int_part}{frac_part}");
        let n: i64 = combined
            .parse()
            .map_err(|_| SimpleError::InvalidNumber(text.into(), off))?;
        Ok(reduce_lit(n, denom))
    } else {
        let n: i64 = text
            .parse()
            .map_err(|_| SimpleError::InvalidNumber(text.into(), off))?;
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
        parse_simple(s).expect(s)
    }

    #[test]
    fn integer() {
        assert_eq!(p("42"), Expr::Lit(42, 1));
    }

    #[test]
    fn decimal_to_rational() {
        assert_eq!(p("0.5"), Expr::Lit(1, 2));
        assert_eq!(p("0.25"), Expr::Lit(1, 4));
    }

    #[test]
    fn add_left_assoc() {
        // 1 + 2 + 3 → ((1 + 2) + 3)
        let e = p("1 + 2 + 3");
        let expected = bin(
            BinOp::Add,
            bin(BinOp::Add, Expr::Lit(1, 1), Expr::Lit(2, 1)),
            Expr::Lit(3, 1),
        );
        assert_eq!(e, expected);
    }

    #[test]
    fn mul_higher_precedence_than_add() {
        // 1 + 2 * 3 → 1 + (2 * 3)
        let e = p("1 + 2 * 3");
        let expected = bin(
            BinOp::Add,
            Expr::Lit(1, 1),
            bin(BinOp::Mul, Expr::Lit(2, 1), Expr::Lit(3, 1)),
        );
        assert_eq!(e, expected);
    }

    #[test]
    fn pow_right_assoc() {
        // a^b^z → a^(b^z); avoid `c` which is reserved for SpeedOfLight.
        let e = p("a^b^z");
        let expected = bin(
            BinOp::Pow,
            Expr::Var("a".into()),
            bin(BinOp::Pow, Expr::Var("b".into()), Expr::Var("z".into())),
        );
        assert_eq!(e, expected);
    }

    #[test]
    fn parens_override() {
        let e = p("(1 + 2) * 3");
        let expected = bin(
            BinOp::Mul,
            bin(BinOp::Add, Expr::Lit(1, 1), Expr::Lit(2, 1)),
            Expr::Lit(3, 1),
        );
        assert_eq!(e, expected);
    }

    #[test]
    fn unary_minus() {
        let e = p("-x");
        assert_eq!(e, Expr::UnOp(UnOp::Neg, Box::new(Expr::Var("x".into()))));
    }

    #[test]
    fn comparison() {
        let e = p("a < b");
        assert_eq!(e, bin(BinOp::Lt, Expr::Var("a".into()), Expr::Var("b".into())));
    }

    #[test]
    fn equality() {
        let e = p("E = m * c^2");
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
    fn physics_constants_resolve() {
        assert_eq!(p("hbar"), Expr::Const(PhysConst::ReducedPlanck));
        assert_eq!(p("pi"), Expr::Const(PhysConst::Pi));
        assert_eq!(p("c"), Expr::Const(PhysConst::SpeedOfLight));
        assert_eq!(p("k_B"), Expr::Const(PhysConst::Boltzmann));
    }

    #[test]
    fn subscripted_identifier_is_one_var() {
        // psi_0 is a single Var, not a function call or subscript op.
        assert_eq!(p("psi_0"), Expr::Var("psi_0".into()));
    }

    #[test]
    fn known_unary_function() {
        let e = p("sin(x)");
        assert_eq!(e, Expr::UnOp(UnOp::Sin, Box::new(Expr::Var("x".into()))));
    }

    #[test]
    fn unknown_function_becomes_app() {
        let e = p("f(x)");
        assert_eq!(
            e,
            Expr::App(Box::new(Expr::Var("f".into())), Box::new(Expr::Var("x".into())))
        );
    }

    #[test]
    fn commutator_canonical_qm() {
        // [x, p] = i * hbar
        let conjecture = p("[x, p] = i * hbar");
        // Reference form: x*p - p*x = i*hbar
        let reference = p("x*p - p*x = i*hbar");
        assert_eq!(
            canonical_ac_hash(&conjecture),
            canonical_ac_hash(&reference)
        );
    }

    #[test]
    fn boolean_keywords() {
        let e = p("a and b or z");
        // Precedence: and > or → (a and b) or z; `c` reserved as SpeedOfLight.
        let expected = bin(
            BinOp::Or,
            bin(BinOp::And, Expr::Var("a".into()), Expr::Var("b".into())),
            Expr::Var("z".into()),
        );
        assert_eq!(e, expected);
    }

    #[test]
    fn whitespace_irrelevant() {
        assert_eq!(p("  1   +  2 "), p("1+2"));
    }

    #[test]
    fn trailing_input_errors() {
        assert!(matches!(parse_simple("1 + 2 oops"), Err(_)));
    }

    #[test]
    fn empty_input_errors() {
        assert!(matches!(parse_simple(""), Err(SimpleError::UnexpectedEof)));
    }

    #[test]
    fn ac_match_against_reordered_sum() {
        // a + b + c parses left-assoc; AC-canonical hash matches reorder.
        let a = p("a + b + c");
        let b = p("c + a + b");
        assert_eq!(canonical_ac_hash(&a), canonical_ac_hash(&b));
    }
}
