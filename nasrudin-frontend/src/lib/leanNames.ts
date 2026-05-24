// Display helpers for Lean-qualified theorem names like
// `PhysLean.Electromagnetism.ElectromagneticPotential.vectorPotential_differentiable_time`.
//
// Naïvely showing the last `.` segment collapses every auto-generated
// `eq_1`, `def_1`, `lemma_2`, etc. into the same string, even though
// each comes from a different parent. We disambiguate by pulling
// extra segments forward whenever the tail is a generic boilerplate
// name.

const GENERIC_TAIL = /^(eq|def|lemma|theorem|prop|propositional|cor|axiom|inst|inst_\d+|congr|spec|aux|sigma)_(\d+|\w+)$/i;

/**
 * Last `.`-segment of a qualifier, but when the tail looks generic
 * (`eq_1`, `def_2`, `lemma_aux_3`, …) include the previous segment
 * so the user can tell two `eq_1`s apart.
 *
 * Examples:
 *   `Foo.Bar.eq_1`           → `Bar.eq_1`
 *   `Lorentz.boost.eq_2`     → `boost.eq_2`
 *   `Foo.vectorPotential_diff_time` → `vectorPotential_diff_time`
 *   `eq_1`                   → `eq_1` (no parent)
 */
export function displayLeanName(qualified: string): string {
  const parts = qualified.split('.').filter(Boolean);
  if (parts.length === 0) return qualified;
  const last = parts[parts.length - 1] ?? qualified;
  if (parts.length >= 2 && GENERIC_TAIL.test(last)) {
    const parent = parts[parts.length - 2];
    if (parent) return `${parent}.${last}`;
  }
  return last;
}
