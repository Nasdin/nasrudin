use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub struct Dimension {
    pub length: i8,
    pub mass: i8,
    pub time: i8,
    pub current: i8,
    pub temperature: i8,
    pub amount: i8,
    pub luminosity: i8,
}

impl Dimension {
    pub const DIMENSIONLESS: Self = Self::new(0, 0, 0, 0, 0, 0, 0);
    pub const LENGTH: Self = Self::new(1, 0, 0, 0, 0, 0, 0);
    pub const MASS: Self = Self::new(0, 1, 0, 0, 0, 0, 0);
    pub const TIME: Self = Self::new(0, 0, 1, 0, 0, 0, 0);
    pub const VELOCITY: Self = Self::new(1, 0, -1, 0, 0, 0, 0);
    pub const ACCELERATION: Self = Self::new(1, 0, -2, 0, 0, 0, 0);
    pub const FORCE: Self = Self::new(1, 1, -2, 0, 0, 0, 0);
    pub const ENERGY: Self = Self::new(2, 1, -2, 0, 0, 0, 0);
    pub const POWER: Self = Self::new(2, 1, -3, 0, 0, 0, 0);
    pub const MOMENTUM: Self = Self::new(1, 1, -1, 0, 0, 0, 0);
    pub const PRESSURE: Self = Self::new(-1, 1, -2, 0, 0, 0, 0);
    pub const CHARGE: Self = Self::new(0, 0, 1, 1, 0, 0, 0);
    pub const VOLTAGE: Self = Self::new(2, 1, -3, -1, 0, 0, 0);
    pub const ENTROPY: Self = Self::new(2, 1, -2, 0, -1, 0, 0);
    pub const ACTION: Self = Self::new(2, 1, -1, 0, 0, 0, 0);

    pub const fn new(
        length: i8,
        mass: i8,
        time: i8,
        current: i8,
        temperature: i8,
        amount: i8,
        luminosity: i8,
    ) -> Self {
        Self {
            length,
            mass,
            time,
            current,
            temperature,
            amount,
            luminosity,
        }
    }

    pub fn multiply(self, other: Self) -> Self {
        Self {
            length: self.length + other.length,
            mass: self.mass + other.mass,
            time: self.time + other.time,
            current: self.current + other.current,
            temperature: self.temperature + other.temperature,
            amount: self.amount + other.amount,
            luminosity: self.luminosity + other.luminosity,
        }
    }

    pub fn divide(self, other: Self) -> Self {
        Self {
            length: self.length - other.length,
            mass: self.mass - other.mass,
            time: self.time - other.time,
            current: self.current - other.current,
            temperature: self.temperature - other.temperature,
            amount: self.amount - other.amount,
            luminosity: self.luminosity - other.luminosity,
        }
    }

    pub fn power(self, n: i8) -> Self {
        Self {
            length: self.length * n,
            mass: self.mass * n,
            time: self.time * n,
            current: self.current * n,
            temperature: self.temperature * n,
            amount: self.amount * n,
            luminosity: self.luminosity * n,
        }
    }

    pub fn is_dimensionless(self) -> bool {
        self == Self::DIMENSIONLESS
    }

    pub fn is_compatible(self, other: Self) -> bool {
        self == other
    }
}

impl std::ops::Mul for Dimension {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        self.multiply(rhs)
    }
}

impl std::ops::Div for Dimension {
    type Output = Self;
    fn div(self, rhs: Self) -> Self {
        self.divide(rhs)
    }
}

impl std::fmt::Display for Dimension {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut parts = Vec::new();
        if self.length != 0 {
            parts.push(format!("L^{}", self.length));
        }
        if self.mass != 0 {
            parts.push(format!("M^{}", self.mass));
        }
        if self.time != 0 {
            parts.push(format!("T^{}", self.time));
        }
        if self.current != 0 {
            parts.push(format!("I^{}", self.current));
        }
        if self.temperature != 0 {
            parts.push(format!("Th^{}", self.temperature));
        }
        if self.amount != 0 {
            parts.push(format!("N^{}", self.amount));
        }
        if self.luminosity != 0 {
            parts.push(format!("J^{}", self.luminosity));
        }
        if parts.is_empty() {
            write!(f, "dimensionless")
        } else {
            write!(f, "{}", parts.join(" "))
        }
    }
}
