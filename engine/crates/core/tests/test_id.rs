use nasrudin_core::id::*;

#[test]
fn test_compute_theorem_id_deterministic() {
    let canonical = "(= v:E (* v:m (^ c:SpeedOfLight n:2)))";
    let id1 = compute_theorem_id(canonical);
    let id2 = compute_theorem_id(canonical);
    assert_eq!(id1, id2);
}

#[test]
fn test_different_canonicals_different_ids() {
    let id1 = compute_theorem_id("(+ v:x v:y)");
    let id2 = compute_theorem_id("(* v:x v:y)");
    assert_ne!(id1, id2);
}

#[test]
fn test_theorem_id_is_8_bytes() {
    let id = compute_theorem_id("test");
    assert_eq!(id.len(), 8);
}

#[test]
fn test_hex_roundtrip() {
    let id = compute_theorem_id("(= v:E (* v:m (^ c:SpeedOfLight n:2)))");
    let hex_str = theorem_id_to_hex(&id);
    assert_eq!(hex_str.len(), 16); // 8 bytes = 16 hex chars
    let restored = hex_to_theorem_id(&hex_str).unwrap();
    assert_eq!(id, restored);
}

#[test]
fn test_hex_format() {
    let id = compute_theorem_id("test");
    let hex_str = theorem_id_to_hex(&id);
    // Should be valid hex (lowercase)
    assert!(hex_str.chars().all(|c| c.is_ascii_hexdigit()));
}

#[test]
fn test_invalid_hex_returns_error() {
    let result = hex_to_theorem_id("not_hex!");
    assert!(result.is_err());
}
