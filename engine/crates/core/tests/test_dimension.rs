use physics_core::dimension::Dimension;

#[test]
fn test_dimensionless() {
    let d = Dimension::DIMENSIONLESS;
    assert!(d.is_dimensionless());
    assert_eq!(d.to_string(), "dimensionless");
}

#[test]
fn test_named_dimensions() {
    assert_eq!(Dimension::LENGTH, Dimension::new(1, 0, 0, 0, 0, 0, 0));
    assert_eq!(Dimension::MASS, Dimension::new(0, 1, 0, 0, 0, 0, 0));
    assert_eq!(Dimension::TIME, Dimension::new(0, 0, 1, 0, 0, 0, 0));
    assert_eq!(Dimension::VELOCITY, Dimension::new(1, 0, -1, 0, 0, 0, 0));
    assert_eq!(Dimension::ACCELERATION, Dimension::new(1, 0, -2, 0, 0, 0, 0));
    assert_eq!(Dimension::FORCE, Dimension::new(1, 1, -2, 0, 0, 0, 0));
    assert_eq!(Dimension::ENERGY, Dimension::new(2, 1, -2, 0, 0, 0, 0));
    assert_eq!(Dimension::POWER, Dimension::new(2, 1, -3, 0, 0, 0, 0));
    assert_eq!(Dimension::MOMENTUM, Dimension::new(1, 1, -1, 0, 0, 0, 0));
    assert_eq!(Dimension::PRESSURE, Dimension::new(-1, 1, -2, 0, 0, 0, 0));
    assert_eq!(Dimension::CHARGE, Dimension::new(0, 0, 1, 1, 0, 0, 0));
    assert_eq!(Dimension::VOLTAGE, Dimension::new(2, 1, -3, -1, 0, 0, 0));
    assert_eq!(Dimension::ENTROPY, Dimension::new(2, 1, -2, 0, -1, 0, 0));
    assert_eq!(Dimension::ACTION, Dimension::new(2, 1, -1, 0, 0, 0, 0));
}

#[test]
fn test_multiply_dimensions() {
    // Force = Mass * Acceleration: M*L*T^-2
    let result = Dimension::MASS.multiply(Dimension::ACCELERATION);
    assert_eq!(result, Dimension::FORCE);
}

#[test]
fn test_multiply_operator() {
    let result = Dimension::MASS * Dimension::ACCELERATION;
    assert_eq!(result, Dimension::FORCE);
}

#[test]
fn test_divide_dimensions() {
    // Velocity = Length / Time: L*T^-1
    let result = Dimension::LENGTH.divide(Dimension::TIME);
    assert_eq!(result, Dimension::VELOCITY);
}

#[test]
fn test_divide_operator() {
    let result = Dimension::LENGTH / Dimension::TIME;
    assert_eq!(result, Dimension::VELOCITY);
}

#[test]
fn test_power_dimension() {
    // Length^2 => L^2
    let area = Dimension::LENGTH.power(2);
    assert_eq!(area, Dimension::new(2, 0, 0, 0, 0, 0, 0));
}

#[test]
fn test_power_zero() {
    let result = Dimension::ENERGY.power(0);
    assert!(result.is_dimensionless());
}

#[test]
fn test_is_compatible() {
    assert!(Dimension::ENERGY.is_compatible(Dimension::ENERGY));
    assert!(!Dimension::ENERGY.is_compatible(Dimension::FORCE));
}

#[test]
fn test_energy_is_force_times_length() {
    // E = F * L => (L*M*T^-2) * L = L^2*M*T^-2
    let result = Dimension::FORCE * Dimension::LENGTH;
    assert_eq!(result, Dimension::ENERGY);
}

#[test]
fn test_momentum_is_mass_times_velocity() {
    let result = Dimension::MASS * Dimension::VELOCITY;
    assert_eq!(result, Dimension::MOMENTUM);
}

#[test]
fn test_power_is_energy_over_time() {
    let result = Dimension::ENERGY / Dimension::TIME;
    assert_eq!(result, Dimension::POWER);
}

#[test]
fn test_pressure_is_force_over_area() {
    // Pressure = Force / Length^2 => (L*M*T^-2) / (L^2) = L^-1*M*T^-2
    let area = Dimension::LENGTH.power(2);
    let result = Dimension::FORCE / area;
    assert_eq!(result, Dimension::PRESSURE);
}

#[test]
fn test_display_energy() {
    let d = Dimension::ENERGY;
    let s = d.to_string();
    assert!(s.contains("L^2"));
    assert!(s.contains("M^1"));
    assert!(s.contains("T^-2"));
}

#[test]
fn test_display_dimensionless() {
    assert_eq!(Dimension::DIMENSIONLESS.to_string(), "dimensionless");
}

#[test]
fn test_default_is_dimensionless() {
    let d = Dimension::default();
    assert!(d.is_dimensionless());
}

#[test]
fn test_serde_roundtrip() {
    let original = Dimension::ENERGY;
    let json = serde_json::to_string(&original).unwrap();
    let restored: Dimension = serde_json::from_str(&json).unwrap();
    assert_eq!(original, restored);
}
