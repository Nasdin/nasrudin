use physics_api::lake_builder::preflight_axiom_or_sorry;

#[test]
fn rejects_top_level_axiom() {
    let src = "import Foo\n\naxiom evil : True := by trivial";
    assert!(preflight_axiom_or_sorry(src).is_err());
}

#[test]
fn rejects_sorry_in_proof() {
    let src = "theorem t : 1=1 := by sorry";
    assert!(preflight_axiom_or_sorry(src).is_err());
}

#[test]
fn rejects_sorry_with_punctuation() {
    let src = "theorem t : 1=1 := by exact (sorry)";
    assert!(preflight_axiom_or_sorry(src).is_err());
}

#[test]
fn allows_clean_proof() {
    let src = "import PhysicsGenerator.Axioms\n\ntheorem rest_energy : E = m*c^2 := by nlinarith";
    assert!(preflight_axiom_or_sorry(src).is_ok());
}

#[test]
fn allows_axiom_in_line_comment() {
    let src = "-- this is not a real axiom\ntheorem t : 1=1 := rfl";
    assert!(preflight_axiom_or_sorry(src).is_ok());
}

#[test]
fn allows_axiom_in_block_comment() {
    let src = "/- This proof avoids the axiom of choice -/\ntheorem t : 1=1 := rfl";
    assert!(preflight_axiom_or_sorry(src).is_ok());
}

#[test]
fn allows_sorry_in_block_comment() {
    let src = "/- TODO sorry remove this -/\ntheorem t : 1=1 := rfl";
    assert!(preflight_axiom_or_sorry(src).is_ok());
}

#[test]
fn rejects_axiom_with_leading_whitespace() {
    let src = "namespace Foo\n  axiom bar : Nat\nend Foo";
    assert!(preflight_axiom_or_sorry(src).is_err());
}

#[test]
fn allows_axiom_substring_in_identifier() {
    // 'axioms_of_choice' starts with 'axiom' but is an identifier, not a declaration
    let src = "theorem axioms_of_choice : True := trivial";
    assert!(preflight_axiom_or_sorry(src).is_ok());
}

#[test]
fn allows_sorry_substring_in_identifier() {
    let src = "theorem sorrytactic : True := trivial";
    assert!(preflight_axiom_or_sorry(src).is_ok());
}

#[test]
fn rejects_unterminated_block_comment() {
    let src = "/- never closes\naxiom evil : True := sorry\n";
    assert_eq!(
        preflight_axiom_or_sorry(src),
        Err("preflight_unterminated_comment")
    );
}
