use serde::{Deserialize, Serialize};

/// Unique symbol identifier
pub type Symbol = String;

/// Physical constant identifiers
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PhysConst {
    SpeedOfLight,
    PlanckConst,
    ReducedPlanck,
    GravConst,
    Boltzmann,
    ElectronCharge,
    ElectronMass,
    ProtonMass,
    VacuumPermittivity,
    VacuumPermeability,
    Avogadro,
    Pi,
    EulersNumber,
}

/// Binary operators
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    Implies,
    Iff,
    Cross,
    Dot,
    TensorProduct,
}

/// Unary operators
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum UnOp {
    Neg,
    Abs,
    Sqrt,
    Sin,
    Cos,
    Tan,
    Exp,
    Log,
    Ln,
    Grad,
    Div,
    Curl,
    Laplacian,
    Transpose,
    Conjugate,
    Trace,
    Det,
}

/// Mathematical expression AST
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Expr {
    /// Variable: x, y, m, c, E
    Var(Symbol),
    /// Physical constant
    Const(PhysConst),
    /// Rational literal (numerator, denominator)
    Lit(i64, u64),
    /// Function application: f(x)
    App(Box<Expr>, Box<Expr>),
    /// Lambda: lambda(x : T). body
    Lam(Symbol, Box<Expr>, Box<Expr>),
    /// Dependent function type: Pi(x : A). B
    Pi(Symbol, Box<Expr>, Box<Expr>),
    /// Binary operation
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    /// Unary operation
    UnOp(UnOp, Box<Expr>),
    /// Derivative: d/dx f
    Deriv(Box<Expr>, Symbol),
    /// Partial derivative: partial/partial_x f
    PartialDeriv(Box<Expr>, Symbol),
    /// Integral: integral_a^b f dx
    Integral {
        body: Box<Expr>,
        var: Symbol,
        lower: Option<Box<Expr>>,
        upper: Option<Box<Expr>>,
    },
    /// Sum: Sigma_{i=a}^{b} f(i)
    Sum {
        body: Box<Expr>,
        var: Symbol,
        lower: Box<Expr>,
        upper: Box<Expr>,
    },
    /// Product: Pi_{i=a}^{b} f(i)
    Prod {
        body: Box<Expr>,
        var: Symbol,
        lower: Box<Expr>,
        upper: Box<Expr>,
    },
    /// Limit: lim_{x -> a} f(x)
    Limit {
        body: Box<Expr>,
        var: Symbol,
        approaching: Box<Expr>,
    },
    /// Let binding: let x = e1 in e2
    Let(Symbol, Box<Expr>, Box<Expr>),
}

impl Expr {
    /// Count AST nodes (complexity measure)
    pub fn node_count(&self) -> usize {
        match self {
            Expr::Var(_) | Expr::Const(_) | Expr::Lit(_, _) => 1,
            Expr::App(f, x) => 1 + f.node_count() + x.node_count(),
            Expr::Lam(_, ty, body) | Expr::Pi(_, ty, body) => {
                1 + ty.node_count() + body.node_count()
            }
            Expr::BinOp(_, l, r) => 1 + l.node_count() + r.node_count(),
            Expr::UnOp(_, e) | Expr::Deriv(e, _) | Expr::PartialDeriv(e, _) => {
                1 + e.node_count()
            }
            Expr::Integral {
                body,
                lower,
                upper,
                ..
            } => {
                1 + body.node_count()
                    + lower.as_ref().map_or(0, |e| e.node_count())
                    + upper.as_ref().map_or(0, |e| e.node_count())
            }
            Expr::Sum {
                body,
                lower,
                upper,
                ..
            }
            | Expr::Prod {
                body,
                lower,
                upper,
                ..
            } => 1 + body.node_count() + lower.node_count() + upper.node_count(),
            Expr::Limit {
                body, approaching, ..
            } => 1 + body.node_count() + approaching.node_count(),
            Expr::Let(_, val, body) => 1 + val.node_count() + body.node_count(),
        }
    }

    /// Convert to canonical prefix notation string
    pub fn to_canonical(&self) -> String {
        match self {
            Expr::Var(s) => format!("v:{s}"),
            Expr::Const(c) => format!("c:{c:?}"),
            Expr::Lit(n, d) => {
                if *d == 1 {
                    format!("n:{n}")
                } else {
                    format!("n:{n}/{d}")
                }
            }
            Expr::App(f, x) => format!("(@ {} {})", f.to_canonical(), x.to_canonical()),
            Expr::BinOp(op, l, r) => {
                let op_str = match op {
                    BinOp::Add => "+",
                    BinOp::Sub => "-",
                    BinOp::Mul => "*",
                    BinOp::Div => "/",
                    BinOp::Pow => "^",
                    BinOp::Eq => "=",
                    BinOp::Ne => "!=",
                    BinOp::Lt => "<",
                    BinOp::Le => "<=",
                    BinOp::Gt => ">",
                    BinOp::Ge => ">=",
                    BinOp::And => "and",
                    BinOp::Or => "or",
                    BinOp::Implies => "->",
                    BinOp::Iff => "<->",
                    BinOp::Cross => "cross",
                    BinOp::Dot => "dot",
                    BinOp::TensorProduct => "tensor",
                };
                format!("({op_str} {} {})", l.to_canonical(), r.to_canonical())
            }
            Expr::UnOp(op, e) => {
                let op_str = match op {
                    UnOp::Neg => "neg",
                    UnOp::Abs => "abs",
                    UnOp::Sqrt => "sqrt",
                    UnOp::Sin => "sin",
                    UnOp::Cos => "cos",
                    UnOp::Tan => "tan",
                    UnOp::Exp => "exp",
                    UnOp::Log => "log",
                    UnOp::Ln => "ln",
                    UnOp::Grad => "grad",
                    UnOp::Div => "div",
                    UnOp::Curl => "curl",
                    UnOp::Laplacian => "laplacian",
                    UnOp::Transpose => "transpose",
                    UnOp::Conjugate => "conjugate",
                    UnOp::Trace => "trace",
                    UnOp::Det => "det",
                };
                format!("({op_str} {})", e.to_canonical())
            }
            Expr::Deriv(e, var) => format!("(deriv {var} {})", e.to_canonical()),
            Expr::PartialDeriv(e, var) => format!("(partial {var} {})", e.to_canonical()),
            Expr::Integral {
                body,
                var,
                lower,
                upper,
            } => {
                let lo = lower
                    .as_ref()
                    .map_or("_".to_string(), |e| e.to_canonical());
                let hi = upper
                    .as_ref()
                    .map_or("_".to_string(), |e| e.to_canonical());
                format!("(integral {var} {lo} {hi} {})", body.to_canonical())
            }
            Expr::Sum {
                body,
                var,
                lower,
                upper,
            } => {
                format!(
                    "(sum {var} {} {} {})",
                    lower.to_canonical(),
                    upper.to_canonical(),
                    body.to_canonical()
                )
            }
            Expr::Prod {
                body,
                var,
                lower,
                upper,
            } => {
                format!(
                    "(prod {var} {} {} {})",
                    lower.to_canonical(),
                    upper.to_canonical(),
                    body.to_canonical()
                )
            }
            Expr::Limit {
                body,
                var,
                approaching,
            } => {
                format!(
                    "(limit {var} {} {})",
                    approaching.to_canonical(),
                    body.to_canonical()
                )
            }
            Expr::Lam(var, ty, body) => {
                format!(
                    "(lambda {var} {} {})",
                    ty.to_canonical(),
                    body.to_canonical()
                )
            }
            Expr::Pi(var, a, b) => {
                format!("(pi {var} {} {})", a.to_canonical(), b.to_canonical())
            }
            Expr::Let(var, val, body) => {
                format!(
                    "(let {var} {} {})",
                    val.to_canonical(),
                    body.to_canonical()
                )
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_prod() -> Expr {
        Expr::Prod {
            body: Box::new(Expr::Var("i".into())),
            var: "i".into(),
            lower: Box::new(Expr::Lit(1, 1)),
            upper: Box::new(Expr::Var("n".into())),
        }
    }

    #[test]
    fn prod_node_count() {
        let prod = make_prod();
        // 1 (Prod) + 1 (body: Var) + 1 (lower: Lit) + 1 (upper: Var) = 4
        assert_eq!(prod.node_count(), 4);
    }

    #[test]
    fn prod_to_canonical() {
        let prod = make_prod();
        assert_eq!(prod.to_canonical(), "(prod i n:1 v:n v:i)");
    }

    #[test]
    fn sum_node_count() {
        let sum = Expr::Sum {
            body: Box::new(Expr::Var("i".into())),
            var: "i".into(),
            lower: Box::new(Expr::Lit(0, 1)),
            upper: Box::new(Expr::Var("n".into())),
        };
        assert_eq!(sum.node_count(), 4);
    }

    #[test]
    fn sum_to_canonical() {
        let sum = Expr::Sum {
            body: Box::new(Expr::Var("i".into())),
            var: "i".into(),
            lower: Box::new(Expr::Lit(0, 1)),
            upper: Box::new(Expr::Var("n".into())),
        };
        assert_eq!(sum.to_canonical(), "(sum i n:0 v:n v:i)");
    }
}
