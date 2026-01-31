import Mathlib
import PhysicsGenerator.Basic

/-!
# SpecialRelativity (Generated from PhysLean)

Auto-generated from PhysLean catalog (version: v4.26.0).
These axioms correspond to proven theorems in PhysLean.
Re-axiomatized here for Lean 4.27 compatibility.

DO NOT EDIT — regenerate with `just generate-axioms`.
-/

namespace PhysicsGenerator.SpecialRelativity

open PhysicsGenerator

-- ══════════════════════════════════════════════════════════════
-- Types (from PhysLean)
-- ══════════════════════════════════════════════════════════════

-- Source: PhysLean (Lorentz.CoMod)
/-- The module for covariant (up-index) complex Lorentz vectors.  -/
axiom CoMod : Type

-- Source: PhysLean (Lorentz.ContrℂModule)
/-- The module for contravariant (up-index) complex Lorentz vectors.  -/
axiom ContrℂModule : Type

-- Source: PhysLean (Lorentz.CoℂModule)
/-- The module for covariant (up-index) complex Lorentz vectors.  -/
axiom CoℂModule : Type

-- Source: PhysLean (realLorentzTensor.Color)
/-- The colors associated with complex representations of SL(2, ℂ) of interest to physics.  -/
axiom Color : Type

-- Source: PhysLean (Lorentz.Vector.CausalCharacter)
/-- Classification of lorentz vectors based on their causal character.  -/
axiom CausalCharacter : Type

-- [skipped duplicate: Color from complexLorentzTensor.Color]

-- Source: PhysLean (Lorentz.ContrMod)
/-- The module for contravariant (up-index) real Lorentz vectors.  -/
axiom ContrMod : Type

-- ══════════════════════════════════════════════════════════════
-- Helper Definitions (for derivation proofs)
-- ══════════════════════════════════════════════════════════════

/-- A four-momentum vector in special relativity -/
structure FourMomentum where
  energy : ℝ
  px : ℝ
  py : ℝ
  pz : ℝ

/-- Squared magnitude of 3-momentum: |p⃗|² = px² + py² + pz² -/
noncomputable def FourMomentum.three_momentum_sq (p : FourMomentum) : ℝ :=
  p.px ^ 2 + p.py ^ 2 + p.pz ^ 2

/-- Minkowski invariant (energy scale): E² − |p⃗|²c² -/
noncomputable def FourMomentum.invariant_mass_energy (p : FourMomentum) : ℝ :=
  p.energy ^ 2 - p.three_momentum_sq * c ^ 2

/-- Mass-shell condition: E² − |p⃗|²c² = (mc²)² -/
def OnMassShell (p : FourMomentum) (m : ℝ) : Prop :=
  p.invariant_mass_energy = (m * c ^ 2) ^ 2

/-- A particle is at rest when its 3-momentum vanishes -/
def AtRest (p : FourMomentum) : Prop :=
  p.three_momentum_sq = 0

-- ══════════════════════════════════════════════════════════════
-- Theorems (from PhysLean — re-axiomatized)
-- ══════════════════════════════════════════════════════════════

-- Source: PhysLean (Lorentz.CoMod.instAddCommGroup)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_instaddcommgroup : {d : Nat} → AddCommGroup (Lorentz.CoMod d)

-- Source: PhysLean (Lorentz.Vector.minkowskiProduct)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproduct : {d : Nat} →
--   ContinuousLinearMap (RingHom.id Real) (Lorentz.Vector d)
--     (ContinuousLinearMap (RingHom.id Real) (Lorentz.Vector d) Real)

-- Source: PhysLean (Lorentz.Vector.basis_repr_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_basis_repr_apply : ∀ {d : Nat} (p : Lorentz.Vector d) (μ : Sum (Fin 1) (Fin d)),
--   Eq (Finsupp.instFunLike.coe (EquivLike.toFunLike.coe Lorentz.Vector.basis.repr p) μ) (p μ)

-- Source: PhysLean (LorentzGroup.subtype_mul_inv)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_subtype_mul_inv : ∀ {d : Nat} {Λ : (LorentzGroup d).Elem},
--   Eq (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul Λ.val (Matrix.inv.inv Λ.val)) 1

-- Source: PhysLean (Lorentz.CoℂModule.SL2CRep)
-- [complex signature, not re-axiomatized]
-- lorentz_coℂmodule_sl2crep : Representation Complex (Matrix.SpecialLinearGroup (Fin 2) Complex) Lorentz.CoℂModule

-- Source: PhysLean (Lorentz.Vector.continuous_of_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_continuous_of_apply : ∀ {d : Nat} {α : Type u_1} [inst : TopologicalSpace α] (f : α → Lorentz.Vector d),
--   (∀ (i : Sum (Fin 1) (Fin d)), Continuous fun x => f x i) → Continuous f

-- Source: PhysLean (Lorentz.Vector.neg_causalCharacter_eq_self)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_neg_causalcharacter_eq_self : ∀ {d : Nat} (p : Lorentz.Vector d),
--   Eq (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg p).causalCharacter p.causalCharacter

-- Source: PhysLean (LorentzGroup.generalizedBoost_apply)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_generalizedboost_apply : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem) (x : Lorentz.Vector d),
--   Eq (instHSMul.hSMul (LorentzGroup.generalizedBoost u v) x)
--     (instHAdd.hAdd (instHAdd.hAdd x (LinearMap.instFunLike.coe (LorentzGroup.genBoostAux₁ u v) x))
--       (LinearMap.instFunLike.coe (LorentzGroup.genBoostAux₂ u v) x))

-- Source: PhysLean (SpaceTime.deriv)
-- [complex signature, not re-axiomatized]
-- spacetime_deriv : {M : Type} →
--   [inst : AddCommGroup M] →
--     [Module Real M] → [TopologicalSpace M] → {d : Nat} → Sum (Fin 1) (Fin d) → (SpaceTime d → M) → SpaceTime d → M

-- Source: PhysLean (LorentzGroup.toComplex.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_tocomplex_eq_1 : ∀ {d : Nat},
--   Eq LorentzGroup.toComplex
--     { toFun := fun Λ => Λ.val.map (RingHom.instFunLike.coe Complex.ofRealHom), map_one' := ⋯, map_mul' := ⋯ }

-- Source: PhysLean (minkowskiMatrix.as_block)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_as_block : ∀ {d : Nat}, Eq minkowskiMatrix (Matrix.fromBlocks 1 0 0 (-1))

-- Source: PhysLean (Lorentz.SL2C.toSelfAdjointMap_apply_det)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_toselfadjointmap_apply_det : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex)
--   (A : Subtype fun x => SetLike.instMembership.mem (selfAdjoint (Matrix (Fin 2) (Fin 2) Complex)) x),
--   Eq (LinearMap.instFunLike.coe (Lorentz.SL2C.toSelfAdjointMap M) A).val.det A.val.det

-- Source: PhysLean (LorentzGroup.det_eq_one_or_neg_one)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_det_eq_one_or_neg_one : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem), Or (Eq Λ.val.det 1) (Eq Λ.val.det (-1))

-- Source: PhysLean (Lorentz.Vector.apply_sum)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_apply_sum : ∀ {d : Nat} {ι : Type} [inst : Fintype ι] (f : ι → Lorentz.Vector d) (i : Sum (Fin 1) (Fin d)),
--   Eq (Finset.univ.sum (fun j => f j) i) (Finset.univ.sum fun j => f j i)

-- Source: PhysLean (SpaceTime.deriv_sum_inr)
-- [complex signature, not re-axiomatized]
-- spacetime_deriv_sum_inr : ∀ {d : Nat} {M : Type} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] (c : SpeedOfLight)
--   (f : SpaceTime d → M),
--   Differentiable Real f →
--     ∀ (x : SpaceTime d) (i : Fin d),
--       Eq (SpaceTime.deriv (Sum.inr i) f x)
--         (Space.deriv i
--           (fun y =>
--             f
--               (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c).symm
--                 { fst := (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c) x).fst, snd := y }))
--           (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c) x).snd)

-- Source: PhysLean (complexLorentzTensor.Color.ctorIdx)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_color_ctoridx : complexLorentzTensor.Color → Nat

-- Source: PhysLean (Lorentz.complexCoBasis_toFin13ℂ)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcobasis_tofin13ℂ : ∀ (i : Sum (Fin 1) (Fin 3)),
--   Eq (Lorentz.CoℂModule.toFin13ℂ (Module.Basis.instFunLike.coe Lorentz.complexCoBasis i)) (Pi.single i 1)

-- Source: PhysLean (Lorentz.coMetricVal_expand_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_cometricval_expand_tmul : Eq Lorentz.coMetricVal
--   (instHSub.hSub
--     (instHSub.hSub
--       (instHSub.hSub
--         (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inl 0))
--           (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inl 0)))
--         (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 0))
--           (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 0))))
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 1))
--         (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 1))))
--     (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 2))
--       (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 2))))

-- Source: PhysLean (Lorentz.Vector.toTensor_symm_pure)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_totensor_symm_pure : ∀ {d : Nat}
--   (p : TensorSpecies.Tensor.Pure (realLorentzTensor d) (Matrix.vecCons realLorentzTensor.Color.up Matrix.vecEmpty))
--   (i : Sum (Fin 1) (Fin d)),
--   Eq (EquivLike.toFunLike.coe Lorentz.Vector.tensorial.toTensor.symm p.toTensor i)
--     (Finsupp.instFunLike.coe (EquivLike.toFunLike.coe (Lorentz.contrBasisFin d).repr (p 0))
--       (EquivLike.toFunLike.coe Lorentz.Vector.indexEquiv.symm i 0))

-- Source: PhysLean (Lorentz.contrContrToMatrixRe_ρ)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrtomatrixre_ρ : ∀ {d : Nat} (v : (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Contr d)).V.carrier)
--   (M : (LorentzGroup d).Elem),
--   Eq
--     (EquivLike.toFunLike.coe Lorentz.contrContrToMatrixRe
--       (LinearMap.instFunLike.coe
--         (TensorProduct.map (MonoidHom.instFunLike.coe (Lorentz.Contr d).ρ M)
--           (MonoidHom.instFunLike.coe (Lorentz.Contr d).ρ M))
--         v))
--     (instHMul.hMul
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul M.val (EquivLike.toFunLike.coe Lorentz.contrContrToMatrixRe v))
--       M.val.transpose)

-- Source: PhysLean (Lorentz.Vector.zero_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_zero_apply : ∀ {d : Nat} (i : Sum (Fin 1) (Fin d)), Eq (0 i) 0

-- Source: PhysLean (Lorentz.Vector.temporalCLM_basis_sum_inr)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_temporalclm_basis_sum_inr : ∀ {d : Nat} (i : Fin d),
--   Eq
--     (ContinuousLinearMap.funLike.coe (Lorentz.Vector.temporalCLM d)
--       (Module.Basis.instFunLike.coe Lorentz.Vector.basis (Sum.inr i)))
--     0

-- Source: PhysLean (SpaceTime.timeSpaceBasisEquiv.eq_1)
-- [complex signature, not re-axiomatized]
-- spacetime_timespacebasisequiv_eq_1 : ∀ {d : Nat} (c : SpeedOfLight),
--   Eq (SpaceTime.timeSpaceBasisEquiv c)
--     {
--       toFun := fun x μ =>
--         SpaceTime.timeSpaceBasisEquiv.match_1 (fun μ => Real) μ (fun _ => instHMul.hMul c.val (x (Sum.inl 0))) fun i =>
--           x (Sum.inr i),
--       map_add' := ⋯, map_smul' := ⋯,
--       invFun := fun x μ =>
--         SpaceTime.timeSpaceBasisEquiv.match_1 (fun μ => Real) μ
--           (fun _ => instHMul.hMul (instHDiv.hDiv 1 c.val) (x (Sum.inl 0))) fun i => x (Sum.inr i),
--       left_inv := ⋯, right_inv := ⋯, continuous_toFun := ⋯, continuous_invFun := ⋯ }

-- Source: PhysLean (LorentzGroup.one_le_abs_timeComponent)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_one_le_abs_timecomponent : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem), Real.instLE.le 1 (abs (Λ.val (Sum.inl 0) (Sum.inl 0)))

-- Source: PhysLean (LorentzGroup.mem_mul)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_mem_mul : ∀ {d : Nat} {Λ Λ' : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real},
--   Set.instMembership.mem (LorentzGroup d) Λ →
--     Set.instMembership.mem (LorentzGroup d) Λ' →
--       Set.instMembership.mem (LorentzGroup d) (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul Λ Λ')

-- Source: PhysLean (LorentzGroup.genBoostAux₁_basis_minkowskiProduct)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_genboostaux₁_basis_minkowskiproduct : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem) (μ ν : Sum (Fin 1) (Fin d)),
--   Eq
--     (ContinuousLinearMap.funLike.coe
--       (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct
--         (LinearMap.instFunLike.coe (LorentzGroup.genBoostAux₁ u v)
--           (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ)))
--       (LinearMap.instFunLike.coe (LorentzGroup.genBoostAux₁ u v) (Module.Basis.instFunLike.coe Lorentz.Vector.basis ν)))
--     (instHMul.hMul
--       (instHMul.hMul (instHMul.hMul (instHMul.hMul 4 (minkowskiMatrix μ μ)) (minkowskiMatrix ν ν)) (u.val μ)) (u.val ν))

-- Source: PhysLean (Lorentz.Vector.temporalCLM.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_temporalclm_eq_1 : ∀ (d : Nat),
--   Eq (Lorentz.Vector.temporalCLM d)
--     (EquivLike.toFunLike.coe LinearMap.toContinuousLinearMap
--       { toFun := fun v => v (Sum.inl 0), map_add' := ⋯, map_smul' := ⋯ })

-- Source: PhysLean (Lorentz.Vector.causalCharacter)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causalcharacter : {d : Nat} → Lorentz.Vector d → Lorentz.Vector.CausalCharacter

-- Source: PhysLean (SpaceTime.distDeriv_apply)
-- [complex signature, not re-axiomatized]
-- spacetime_distderiv_apply : ∀ {M : Type} {d : Nat} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] (μ : Sum (Fin 1) (Fin d))
--   (f : Distribution Real (SpaceTime d) M) (ε : SchwartzMap (SpaceTime d) Real),
--   Eq (ContinuousLinearMap.funLike.coe (LinearMap.instFunLike.coe (SpaceTime.distDeriv μ) f) ε)
--     (ContinuousLinearMap.funLike.coe
--       (ContinuousLinearMap.funLike.coe (LinearMap.instFunLike.coe (Distribution.fderivD Real) f) ε)
--       (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ))

-- Source: PhysLean (Lorentz.contrBasisFin)
-- [complex signature, not re-axiomatized]
-- lorentz_contrbasisfin : (d : optParam Nat 3) → Module.Basis (Fin (instHAdd.hAdd 1 d)) Real (Lorentz.Contr d).V.carrier

-- Source: PhysLean (Lorentz.Vector.minkowskiProduct_self_eq_timeComponent_spatialPart)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproduct_self_eq_timecomponent_spatialpart : ∀ {d : Nat} (p : Lorentz.Vector d),
--   Eq (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct p) p)
--     (instHSub.hSub (instHPow.hPow (Real.norm.norm p.timeComponent) 2)
--       (instHPow.hPow ((PiLp.instNorm 2 fun x => Real).norm p.spatialPart) 2))

-- Source: PhysLean (Lorentz.contrContrToMatrix)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrtomatrix : LinearEquiv (RingHom.id Complex)
--   (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexContr).V.carrier
--   (Matrix (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3)) Complex)

-- Source: PhysLean (LorentzGroup.subtype_inv_mul)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_subtype_inv_mul : ∀ {d : Nat} {Λ : (LorentzGroup d).Elem},
--   Eq (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.inv.inv Λ.val) Λ.val) 1

-- Source: PhysLean (Lorentz.Vector.instAddCommMonoid)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_instaddcommmonoid : {d : Nat} → AddCommMonoid (Lorentz.Vector d)

-- Source: PhysLean (Lorentz.Vector.contDiff_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_contdiff_apply : ∀ {n : WithTop ENat} {d : Nat} {α : Type u_1} [inst : NormedAddCommGroup α] [inst_1 : NormedSpace Real α]
--   (f : α → Lorentz.Vector d), Iff (∀ (i : Sum (Fin 1) (Fin d)), ContDiff Real n fun x => f x i) (ContDiff Real n f)

-- Source: PhysLean (minkowskiMatrix.dual_id)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_dual_id : ∀ {d : Nat}, Eq (minkowskiMatrix.dual 1) 1

-- Source: PhysLean (LorentzGroup.toVector_timeComponent)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_tovector_timecomponent : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem), Eq (LorentzGroup.toVector Λ).timeComponent (Λ.val (Sum.inl 0) (Sum.inl 0))

-- Source: PhysLean (Lorentz.Vector.causallyPrecedes)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causallyprecedes : {d : Nat} → Lorentz.Vector d → Lorentz.Vector d → Prop

-- Source: PhysLean (CliffordAlgebra.equivOfIsometry_symm)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_equivofisometry_symm : ∀ {R : Type u_1} [inst : CommRing R] {M₁ : Type u_4} {M₂ : Type u_5} [inst_1 : AddCommGroup M₁]
--   [inst_2 : AddCommGroup M₂] [inst_3 : Module R M₁] [inst_4 : Module R M₂] {Q₁ : QuadraticForm R M₁}
--   {Q₂ : QuadraticForm R M₂} (e : QuadraticMap.IsometryEquiv Q₁ Q₂),
--   Eq (CliffordAlgebra.equivOfIsometry e).symm (CliffordAlgebra.equivOfIsometry e.symm)

-- Source: PhysLean (SpaceTime.coord_apply)
-- [complex signature, not re-axiomatized]
-- spacetime_coord_apply : ∀ {d : Nat} (μ : Fin (instHAdd.hAdd 1 d)) (y : SpaceTime d),
--   Eq (LinearMap.instFunLike.coe (SpaceTime.coord μ) y) (y (EquivLike.toFunLike.coe finSumFinEquiv.symm μ))

-- Source: PhysLean (Lorentz.ContrMod.rep)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_rep : {d : Nat} → Representation Real (LorentzGroup d).Elem (Lorentz.ContrMod d)

-- Source: PhysLean (SpaceTime.timeSliceLinearEquiv_apply)
-- [complex signature, not re-axiomatized]
-- spacetime_timeslicelinearequiv_apply : ∀ {d : Nat} {M : Type} [inst : AddCommGroup M] [inst_1 : Module Real M] (c : SpeedOfLight) (f : SpaceTime d → M),
--   Eq (EquivLike.toFunLike.coe (SpaceTime.timeSliceLinearEquiv c) f) (EquivLike.toFunLike.coe (SpaceTime.timeSlice c) f)

-- Source: PhysLean (complexLorentzTensor.altRightMetric_eq_fromPairT)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altrightmetric_eq_frompairt : Eq complexLorentzTensor.altRightMetric
--   (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT Fermion.altRightMetricVal)

-- Source: PhysLean (SpaceTime.timeSlice_contDiff)
-- [complex signature, not re-axiomatized]
-- spacetime_timeslice_contdiff : ∀ {d : Nat} {M : Type} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] {n : WithTop ENat} (c : SpeedOfLight)
--   (f : SpaceTime d → M),
--   ContDiff Real n f →
--     ContDiff Real n (Function.hasUncurryInduction.uncurry (EquivLike.toFunLike.coe (SpaceTime.timeSlice c) f))

-- Source: PhysLean (SpaceTime.«term∂_»)
-- [complex signature, not re-axiomatized]
-- spacetime_«term∂_» : Lean.ParserDescr

-- Source: PhysLean (Lorentz.Vector.equivEuclid)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_equiveuclid : (d : Nat) → LinearEquiv (RingHom.id Real) (Lorentz.Vector d) (EuclideanSpace Real (Sum (Fin 1) (Fin d)))

-- Source: PhysLean (LorentzGroup.generalizedBoost.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_generalizedboost_eq_1 : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem),
--   Eq (LorentzGroup.generalizedBoost u v)
--     ⟨EquivLike.toFunLike.coe (LinearMap.toMatrix Lorentz.Vector.basis Lorentz.Vector.basis)
--         (instHAdd.hAdd (instHAdd.hAdd LinearMap.id (LorentzGroup.genBoostAux₁ u v)) (LorentzGroup.genBoostAux₂ u v)),
--       ⋯⟩

-- Source: PhysLean (Lorentz.coContrContraction_basis)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrcontraction_basis : ∀ (i j : Fin 4),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.coContrContraction.hom)
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasisFin4 i)
--         (Module.Basis.instFunLike.coe Lorentz.complexContrBasisFin4 j)))
--     (ite (Eq i.val j.val) 1 0)

-- Source: PhysLean (SpaceTime.spaceTime_integral_eq_time_integral_space_integral)
-- [complex signature, not re-axiomatized]
-- spacetime_spacetime_integral_eq_time_integral_space_integral : ∀ {M : Type u_1} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] {d : Nat} (c : SpeedOfLight)
--   (f : SpaceTime d → M),
--   MeasureTheory.Integrable f SpaceTime.instMeasureSpace.volume →
--     Eq (MeasureTheory.integral SpaceTime.instMeasureSpace.volume fun x => f x)
--       (instHSMul.hSMul c.val
--         (MeasureTheory.integral measureSpaceOfInnerProductSpace.volume fun t =>
--           MeasureTheory.integral measureSpaceOfInnerProductSpace.volume fun x =>
--             f (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c).symm { fst := t, snd := x })))

-- Source: PhysLean (realLorentzTensor.contrMetric_eq_fromPairT)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_contrmetric_eq_frompairt : ∀ {d : Nat},
--   Eq (realLorentzTensor.contrMetric d)
--     (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT (Lorentz.preContrMetricVal d))

-- Source: PhysLean (SpaceTime.timeSliceLinearEquiv)
-- [complex signature, not re-axiomatized]
-- spacetime_timeslicelinearequiv : {d : Nat} →
--   {M : Type} →
--     [inst : AddCommGroup M] →
--       [inst_1 : Module Real M] →
--         optParam SpeedOfLight 1 → LinearEquiv (RingHom.id Real) (SpaceTime d → M) (Time → Space d → M)

-- Source: PhysLean (Lorentz.preContrCoUnit)
-- [complex signature, not re-axiomatized]
-- lorentz_precontrcounit : (d : optParam Nat 3) →
--   Action.instCategory.Hom (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem))
--     (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d))

-- Source: PhysLean (LorentzGroup.boost_transpose_matrix_eq_self)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_transpose_matrix_eq_self : ∀ {d : Nat} (i : Fin d) {β : Real} (hβ : Real.instLT.lt (abs β) 1),
--   Eq (LorentzGroup.boost i β hβ).val.transpose (LorentzGroup.boost i β hβ).val

-- Source: PhysLean (Lorentz.contrContrToMatrixRe)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrtomatrixre : {d : Nat} →
--   LinearEquiv (RingHom.id Real) (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Contr d)).V.carrier
--     (Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real)

-- Source: PhysLean (Lorentz.Vector.self_mem_lightConeBoundary)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_self_mem_lightconeboundary : ∀ {d : Nat} (p : Lorentz.Vector d), Set.instMembership.mem p.lightConeBoundary p

-- Source: PhysLean (Lorentz.contrCoToMatrixRe_ρ)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcotomatrixre_ρ : ∀ {d : Nat} (v : (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)).V.carrier)
--   (M : (LorentzGroup d).Elem),
--   Eq
--     (EquivLike.toFunLike.coe Lorentz.contrCoToMatrixRe
--       (LinearMap.instFunLike.coe
--         (TensorProduct.map (MonoidHom.instFunLike.coe (Lorentz.Contr d).ρ M)
--           (MonoidHom.instFunLike.coe (Lorentz.Co d).ρ M))
--         v))
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul M.val (EquivLike.toFunLike.coe Lorentz.contrCoToMatrixRe v))
--       (Matrix.inv.inv M.val))

-- Source: PhysLean (SpaceTime.timeSpaceBasis_eq_map_basis)
-- [complex signature, not re-axiomatized]
-- spacetime_timespacebasis_eq_map_basis : ∀ {d : Nat} (c : SpeedOfLight),
--   Eq (SpaceTime.timeSpaceBasis c) (Lorentz.Vector.basis.map (SpaceTime.timeSpaceBasisEquiv c).toLinearEquiv)

-- Source: PhysLean (Lorentz.preContrMetric)
-- [complex signature, not re-axiomatized]
-- lorentz_precontrmetric : (d : optParam Nat 3) →
--   Action.instCategory.Hom (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem))
--     (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Contr d))

-- Source: PhysLean (Lorentz.CoVector.norm_eq_equivEuclid)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_norm_eq_equiveuclid : ∀ (d : Nat) (v : Lorentz.CoVector d),
--   Eq ((Lorentz.CoVector.instNorm d).norm v)
--     ((PiLp.instNorm 2 fun x => Real).norm (EquivLike.toFunLike.coe (Lorentz.CoVector.equivEuclid d) v))

-- Source: PhysLean (complexLorentzTensor.Color.upR.elim)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_color_upr_elim : {motive : complexLorentzTensor.Color → Sort u} →
--   (t : complexLorentzTensor.Color) → Eq t.ctorIdx 2 → motive complexLorentzTensor.Color.upR → motive t

-- Source: PhysLean (LorentzGroup.toVector.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_tovector_eq_1 : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Eq (LorentzGroup.toVector Λ) (instHSMul.hSMul Λ (Module.Basis.instFunLike.coe Lorentz.Vector.basis (Sum.inl 0)))

-- Source: PhysLean (SpaceTime.boost_zero_apply_time_space)
-- [complex signature, not re-axiomatized]
-- spacetime_boost_zero_apply_time_space : ∀ {d : Nat} {β : Real} (hβ : Real.instLT.lt (abs β) 1) (c : SpeedOfLight) (t : Time) (x : Space d.succ),
--   Eq
--     (instHSMul.hSMul (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv (LorentzGroup.boost 0 β hβ))
--       (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c).symm { fst := t, snd := x }))
--     (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c).symm
--       {
--         fst :=
--           {
--             val :=
--               instHMul.hMul (LorentzGroup.γ β)
--                 (instHAdd.hAdd t.val (instHMul.hMul (instHDiv.hDiv β c.val) (x.val 0))) },
--         snd :=
--           {
--             val := fun x_1 =>
--               SpaceTime.boost_zero_apply_time_space.match_1 (fun x => Real) x_1
--                 (fun _ =>
--                   instHMul.hMul (LorentzGroup.γ β)
--                     (instHAdd.hAdd (x.val 0) (instHMul.hMul (instHMul.hMul c.val β) t.val)))
--                 fun n ih => x.val ⟨n.succ, ih⟩ } })

-- Source: PhysLean (SpaceTime.deriv_eq)
-- [complex signature, not re-axiomatized]
-- spacetime_deriv_eq : ∀ {M : Type} [inst : AddCommGroup M] [inst_1 : Module Real M] [inst_2 : TopologicalSpace M] {d : Nat}
--   (μ : Sum (Fin 1) (Fin d)) (f : SpaceTime d → M) (y : SpaceTime d),
--   Eq (SpaceTime.deriv μ f y)
--     (ContinuousLinearMap.funLike.coe (fderiv Real f y) (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ))

-- Source: PhysLean (complexLorentzTensor.actionT_rightAltRightUnit)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_actiont_rightaltrightunit : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (instHSMul.hSMul g complexLorentzTensor.rightAltRightUnit) complexLorentzTensor.rightAltRightUnit

-- Source: PhysLean (CliffordAlgebra.map_surjective)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_map_surjective : ∀ {R : Type u_1} [inst : CommRing R] {M₁ : Type u_4} {M₂ : Type u_5} [inst_1 : AddCommGroup M₁]
--   [inst_2 : AddCommGroup M₂] [inst_3 : Module R M₁] [inst_4 : Module R M₂] {Q₁ : QuadraticForm R M₁}
--   {Q₂ : QuadraticForm R M₂} (f : QuadraticMap.Isometry Q₁ Q₂),
--   Function.Surjective (QuadraticMap.Isometry.instFunLike.coe f) →
--     Function.Surjective (AlgHom.funLike.coe (CliffordAlgebra.map f))

-- Source: PhysLean (complexLorentzTensor.rightMetric_eq_rightBasis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_rightmetric_eq_rightbasis : Eq complexLorentzTensor.rightMetric
--   (instHAdd.hAdd
--     (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg
--       (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--         (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.rightBasis 0)
--           (Module.Basis.instFunLike.coe Fermion.rightBasis 1))))
--     (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.rightBasis 1)
--         (Module.Basis.instFunLike.coe Fermion.rightBasis 0))))

-- Source: PhysLean (complexLorentzTensor.basis_eq_ofRat)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_basis_eq_ofrat : ∀ {n : Nat} {c : Fin n → complexLorentzTensor.Color} (b : TensorSpecies.Tensor.ComponentIdx c),
--   Eq (Module.Basis.instFunLike.coe (TensorSpecies.Tensor.basis c) b)
--     (LinearMap.instFunLike.coe complexLorentzTensor.ofRat fun b' =>
--       ite (Eq b b') { fst := 1, snd := 0 } { fst := 0, snd := 0 })

-- Source: PhysLean (LorentzGroup.orthchroMap_not_IsOrthochronous)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_orthchromap_not_isorthochronous : ∀ {d : Nat} {Λ : (LorentzGroup d).Elem},
--   Not (LorentzGroup.IsOrthochronous Λ) →
--     Eq (ContinuousMap.instFunLike.coe LorentzGroup.orthchroMap Λ) (EquivLike.toFunLike.coe Additive.toMul 1)

-- Source: PhysLean (realLorentzTensor.termη)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_termη : Lean.ParserDescr

-- Source: PhysLean (complexLorentzTensor.coMetric_eq_fromPairT)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cometric_eq_frompairt : Eq complexLorentzTensor.coMetric (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT Lorentz.coMetricVal)

-- Source: PhysLean (CliffordAlgebra.instAlgebra')
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_instalgebra' : {R : Type u_3} →
--   {A : Type u_4} →
--     {M : Type u_5} →
--       [inst : CommSemiring R] →
--         [inst_1 : AddCommGroup M] →
--           [inst_2 : CommRing A] →
--             [inst_3 : Algebra R A] →
--               [inst_4 : Module R M] →
--                 [inst_5 : Module A M] → (Q : QuadraticForm A M) → [IsScalarTower R A M] → Algebra R (CliffordAlgebra Q)

-- Source: PhysLean (Lorentz.coMetric)
-- [complex signature, not re-axiomatized]
-- lorentz_cometric : Action.instCategory.Hom
--   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--   (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexCo)

-- Source: PhysLean (CliffordAlgebra.equivOfIsometry_trans)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_equivofisometry_trans : ∀ {R : Type u_1} [inst : CommRing R] {M₁ : Type u_4} {M₂ : Type u_5} {M₃ : Type u_6} [inst_1 : AddCommGroup M₁]
--   [inst_2 : AddCommGroup M₂] [inst_3 : AddCommGroup M₃] [inst_4 : Module R M₁] [inst_5 : Module R M₂]
--   [inst_6 : Module R M₃] {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q₃ : QuadraticForm R M₃}
--   (e₁₂ : QuadraticMap.IsometryEquiv Q₁ Q₂) (e₂₃ : QuadraticMap.IsometryEquiv Q₂ Q₃),
--   Eq ((CliffordAlgebra.equivOfIsometry e₁₂).trans (CliffordAlgebra.equivOfIsometry e₂₃))
--     (CliffordAlgebra.equivOfIsometry (e₁₂.trans e₂₃))

-- Source: PhysLean (Lorentz.Vector.coordCLM_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_coordclm_apply : ∀ {d : Nat} (i : Sum (Fin 1) (Fin d)) (v : Lorentz.Vector d),
--   Eq (ContinuousLinearMap.funLike.coe (Lorentz.Vector.coordCLM i) v) (v i)

-- Source: PhysLean (Lorentz.complexContr)
/-- The representation of `SL(2, ℂ)` on complex vectors corresponding to contravariant
Lorentz vectors. In index notation these have an up index `ψⁱ`.  -/
axiom lorentz_complexcontr :
  Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)

-- Source: PhysLean (LorentzGroup.boost_inr_other_inl_0)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_inr_other_inl_0 : ∀ {d : Nat} {i j : Fin d} {β : Real} (hβ : Real.instLT.lt (abs β) 1),
--   Ne j i → Eq ((LorentzGroup.boost i β hβ).val (Sum.inr j) (Sum.inl 0)) 0

-- Source: PhysLean (realLorentzTensor.derivative_repr)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_derivative_repr : ∀ {d n m : Nat} {cm : Fin m → realLorentzTensor.Color} {cn : Fin n → realLorentzTensor.Color}
--   (f : (realLorentzTensor d).Tensor cm → (realLorentzTensor d).Tensor cn) (y : (realLorentzTensor d).Tensor cm)
--   (b :
--     (j : Fin (instHAdd.hAdd m n)) →
--       Fin ((realLorentzTensor d).repDim (Fin.append (fun i => (realLorentzTensor d).τ (cm i)) cn j))),
--   DifferentiableAt Real (realLorentzTensor.mapToBasis f)
--       (EquivLike.toFunLike.coe Finsupp.equivFunOnFinite
--         (EquivLike.toFunLike.coe (TensorSpecies.Tensor.basis cm).repr y)) →
--     Eq
--       (Finsupp.instFunLike.coe
--         (EquivLike.toFunLike.coe
--           (TensorSpecies.Tensor.basis (Fin.append (fun i => (realLorentzTensor d).τ (cm i)) cn)).repr
--           (realLorentzTensor.derivative f y))
--         b)
--       (ContinuousLinearMap.funLike.coe
--         (fderiv Real
--           (fun y =>
--             realLorentzTensor.mapToBasis f y
--               (EquivLike.toFunLike.coe TensorSpecies.Tensor.ComponentIdx.prodEquiv b).snd)
--           (Finsupp.instFunLike.coe (EquivLike.toFunLike.coe (TensorSpecies.Tensor.basis cm).repr y)))
--         (Finsupp.instFunLike.coe
--           (Finsupp.single
--             (fun i => Fin.cast ⋯ ((EquivLike.toFunLike.coe TensorSpecies.Tensor.ComponentIdx.prodEquiv b).fst i)) 1)))

-- Source: PhysLean (realLorentzTensor.actionT_contrMetric)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_actiont_contrmetric : ∀ {d : Nat} (g : (LorentzGroup d).Elem),
--   Eq (instHSMul.hSMul g (realLorentzTensor.contrMetric d)) (realLorentzTensor.contrMetric d)

-- Source: PhysLean (Lorentz.Velocity.norm_spatialPart_le_timeComponent)
-- [complex signature, not re-axiomatized]
-- lorentz_velocity_norm_spatialpart_le_timecomponent : ∀ {d : Nat} (v : (Lorentz.Velocity d).Elem),
--   Real.instLE.le ((PiLp.instNorm 2 fun x => Real).norm v.val.spatialPart) (Real.norm.norm v.val.timeComponent)

-- Source: PhysLean (Lorentz.Vector.isFutureDirected)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_isfuturedirected : {d : Nat} → Lorentz.Vector d → Prop

-- Source: PhysLean (SpaceTime.distTensorDeriv.eq_1)
-- [complex signature, not re-axiomatized]
-- spacetime_disttensorderiv_eq_1 : ∀ {M : Type} {d : Nat} [inst : NormedAddCommGroup M] [inst_1 : InnerProductSpace Real M]
--   [inst_2 : FiniteDimensional Real M],
--   Eq SpaceTime.distTensorDeriv
--     {
--       toFun := fun f =>
--         {
--           toFun := fun ε =>
--             Finset.univ.sum fun μ =>
--               TensorProduct.tmul Real (Module.Basis.instFunLike.coe Lorentz.CoVector.basis μ)
--                 (ContinuousLinearMap.funLike.coe (LinearMap.instFunLike.coe (SpaceTime.distDeriv μ) f) ε),
--           map_add' := ⋯, map_smul' := ⋯, cont := ⋯ },
--       map_add' := ⋯, map_smul' := ⋯ }

-- Source: PhysLean (complexLorentzTensor.coContrUnit_symm)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cocontrunit_symm : Eq
--   (EquivLike.toFunLike.coe
--     (TensorSpecies.Tensorial.self complexLorentzTensor
--         (Matrix.vecCons complexLorentzTensor.Color.down
--           (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty))).toTensor
--     complexLorentzTensor.coContrUnit)
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT (Matrix.vecCons 1 (Matrix.vecCons 0 Matrix.vecEmpty)) ⋯)
--     (EquivLike.toFunLike.coe
--       (TensorSpecies.Tensorial.self complexLorentzTensor
--           (Matrix.vecCons complexLorentzTensor.Color.up
--             (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty))).toTensor
--       complexLorentzTensor.contrCoUnit))

-- Source: PhysLean (Lorentz.Vector.timelike_neg_time_component_product)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_timelike_neg_time_component_product : ∀ {d : Nat} (v w : Lorentz.Vector d),
--   Real.instLT.lt (v (Sum.inl 0)) 0 →
--     Real.instLT.lt (w (Sum.inl 0)) 0 → GT.gt (instHMul.hMul (v (Sum.inl 0)) (w (Sum.inl 0))) 0

-- Source: PhysLean (realLorentzTensor.contrMetric_repr_apply_eq_minkowskiMatrix)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_contrmetric_repr_apply_eq_minkowskimatrix : ∀ {d : Nat}
--   (b :
--     TensorSpecies.Tensor.ComponentIdx
--       (Matrix.vecCons realLorentzTensor.Color.up (Matrix.vecCons realLorentzTensor.Color.up Matrix.vecEmpty))),
--   Eq
--     (Finsupp.instFunLike.coe
--       (EquivLike.toFunLike.coe
--         (TensorSpecies.Tensor.basis
--             (Matrix.vecCons realLorentzTensor.Color.up
--               (Matrix.vecCons realLorentzTensor.Color.up Matrix.vecEmpty))).repr
--         (realLorentzTensor.contrMetric d))
--       b)
--     (minkowskiMatrix (EquivLike.toFunLike.coe finSumFinEquiv.symm (b 0))
--       (EquivLike.toFunLike.coe finSumFinEquiv.symm (b 1)))

-- Source: PhysLean (complexLorentzTensor.leftAltLeftUnit_eq_fromConstPair)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_leftaltleftunit_eq_fromconstpair : Eq complexLorentzTensor.leftAltLeftUnit (TensorSpecies.Tensor.fromConstPair Fermion.leftAltLeftUnit)

-- Source: PhysLean (SpaceTime.deriv_apply_eq)
-- [complex signature, not re-axiomatized]
-- spacetime_deriv_apply_eq : ∀ {d : Nat} (μ ν : Sum (Fin 1) (Fin d)) (f : SpaceTime d → Lorentz.Vector d),
--   Differentiable Real f →
--     ∀ (y : SpaceTime d),
--       Eq (SpaceTime.deriv μ f y ν)
--         (ContinuousLinearMap.funLike.coe (fderiv Real (fun x => f x ν) y)
--           (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ))

-- Source: PhysLean (Lorentz.Vector.basis)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_basis : {d : Nat} → Module.Basis (Sum (Fin 1) (Fin d)) Real (Lorentz.Vector d)

-- Source: PhysLean (Lorentz.Vector.causallyRelated)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causallyrelated : {d : Nat} → Lorentz.Vector d → Lorentz.Vector d → Prop

-- Source: PhysLean (Lorentz.preCoContrUnitVal)
-- [complex signature, not re-axiomatized]
-- lorentz_precocontrunitval : (d : optParam Nat 3) → (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)).V.carrier

-- Source: PhysLean (LorentzGroup.boost_inr_other_inr_self)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_inr_other_inr_self : ∀ {d : Nat} {i j : Fin d} {β : Real} (hβ : Real.instLT.lt (abs β) 1),
--   Ne j i → Eq ((LorentzGroup.boost i β hβ).val (Sum.inr j) (Sum.inr i)) 0

-- Source: PhysLean (realLorentzTensor.contrT_toComplex)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_contrt_tocomplex : InformalLemma

-- Source: PhysLean (Lorentz.coMetric_apply_one)
-- [complex signature, not re-axiomatized]
-- lorentz_cometric_apply_one : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexCo).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.coMetric.hom) 1)
--   Lorentz.coMetricVal

-- Source: PhysLean (Lorentz.Vector.causallyPrecedes_refl)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causallyprecedes_refl : ∀ {d : Nat} (p : Lorentz.Vector d), p.causallyPrecedes p

-- Source: PhysLean (Lorentz.CoℂModule.toFin13ℂEquiv_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_coℂmodule_tofin13ℂequiv_apply : ∀ (a : Lorentz.CoℂModule) (a_1 : Sum (Fin 1) (Fin 3)),
--   Eq (EquivLike.toFunLike.coe Lorentz.CoℂModule.toFin13ℂEquiv a a_1)
--     (EquivLike.toFunLike.coe Lorentz.CoℂModule.toFin13ℂFun a a_1)

-- Source: PhysLean (Lorentz.Vector.«term⟪_,_⟫ₘ»)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_«term⟪_,_⟫ₘ» : Lean.ParserDescr

-- Source: PhysLean (SpaceTime.coordCLM)
-- [complex signature, not re-axiomatized]
-- spacetime_coordclm : {d : Nat} → Sum (Fin 1) (Fin d) → ContinuousLinearMap (RingHom.id Real) (SpaceTime d) Real

-- Source: PhysLean (Lorentz.coContrToMatrix_symm_expand_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrtomatrix_symm_expand_tmul : ∀ (M : Matrix (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3)) Complex),
--   Eq (EquivLike.toFunLike.coe Lorentz.coContrToMatrix.symm M)
--     (Finset.univ.sum fun i =>
--       Finset.univ.sum fun j =>
--         instHSMul.hSMul (M i j)
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasis i)
--             (Module.Basis.instFunLike.coe Lorentz.complexContrBasis j)))

-- Source: PhysLean (Lorentz.coCoContract_hom_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_cococontract_hom_tmul : ∀ {d : Nat} (φ ψ : (Lorentz.Co d).V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Co d)).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom Lorentz.coCoContract.hom)
--       (TensorProduct.tmul Real φ ψ))
--     (dotProduct (Lorentz.CoMod.toFin1dℝ φ) (minkowskiMatrix.mulVec (Lorentz.CoMod.toFin1dℝ ψ)))

-- Source: PhysLean (complexLorentzTensor.altRightRightUnit)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altrightrightunit : complexLorentzTensor.Tensor
--   (Matrix.vecCons complexLorentzTensor.Color.downR (Matrix.vecCons complexLorentzTensor.Color.upR Matrix.vecEmpty))

-- Source: PhysLean (Lorentz.coCoContract)
-- [complex signature, not re-axiomatized]
-- lorentz_cococontract : {d : Nat} →
--   Action.instCategory.Hom (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Co d))
--     (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem))

-- Source: PhysLean (complexLorentzTensor.altRightMetric_eq_altRightBasis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altrightmetric_eq_altrightbasis : Eq complexLorentzTensor.altRightMetric
--   (instHSub.hSub
--     (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altRightBasis 0)
--         (Module.Basis.instFunLike.coe Fermion.altRightBasis 1)))
--     (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altRightBasis 1)
--         (Module.Basis.instFunLike.coe Fermion.altRightBasis 0))))

-- Source: PhysLean (Lorentz.contr_coContrUnit)
-- [complex signature, not re-axiomatized]
-- lorentz_contr_cocontrunit : ∀ (x : Lorentz.complexContr.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj
--               (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--               Lorentz.complexContr).V
--           Lorentz.complexContr.V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--         (Action.instMonoidalCategory.leftUnitor Lorentz.complexContr).hom.hom)
--       (((fun X Y => LinearMap.instFunLike)
--             (Action.instMonoidalCategory.tensorObj
--                 (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo) Lorentz.complexContr).V
--             (Action.instMonoidalCategory.tensorObj
--                 (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--                 Lorentz.complexContr).V).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--           (Action.instMonoidalCategory.whiskerRight Lorentz.contrCoContraction Lorentz.complexContr).hom)
--         (((fun X Y => LinearMap.instFunLike)
--               (Action.instMonoidalCategory.tensorObj Lorentz.complexContr
--                   (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr)).V
--               (Action.instMonoidalCategory.tensorObj
--                   (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo)
--                   Lorentz.complexContr).V).coe
--           ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--             (Action.instMonoidalCategory.associator Lorentz.complexContr Lorentz.complexCo
--                   Lorentz.complexContr).inv.hom)
--           (TensorProduct.tmul Complex x
--             (((fun X Y => LinearMap.instFunLike)
--                   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                   (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr).V).coe
--               ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.coContrUnit.hom) 1)))))
--     x

-- Source: PhysLean (LorentzGroup.isProper_on_connected_component)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_isproper_on_connected_component : ∀ {d : Nat} {Λ Λ' : (LorentzGroup d).Elem},
--   Set.instMembership.mem (connectedComponent Λ) Λ' → Iff (LorentzGroup.IsProper Λ) (LorentzGroup.IsProper Λ')

-- Source: PhysLean (complexLorentzTensor.contrCoUnit_symm)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrcounit_symm : Eq
--   (EquivLike.toFunLike.coe
--     (TensorSpecies.Tensorial.self complexLorentzTensor
--         (Matrix.vecCons complexLorentzTensor.Color.up
--           (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty))).toTensor
--     complexLorentzTensor.contrCoUnit)
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT (Matrix.vecCons 1 (Matrix.vecCons 0 Matrix.vecEmpty)) ⋯)
--     (EquivLike.toFunLike.coe
--       (TensorSpecies.Tensorial.self complexLorentzTensor
--           (Matrix.vecCons complexLorentzTensor.Color.down
--             (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty))).toTensor
--       complexLorentzTensor.coContrUnit))

-- Source: PhysLean (LorentzGroup.mem_iff_norm)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_mem_iff_norm : ∀ {d : Nat} {Λ : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real},
--   Iff (Set.instMembership.mem (LorentzGroup d) Λ)
--     (∀ (w : (Lorentz.Contr d).V.carrier),
--       Eq
--         (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--           (TensorProduct.tmul Real (Lorentz.ContrMod.mulVec Λ w) (Lorentz.ContrMod.mulVec Λ w)))
--         (LinearMap.instFunLike.coe Lorentz.contrContrContractField (TensorProduct.tmul Real w w)))

-- Source: PhysLean (Lorentz.contrContrContractField.le_inl_sq)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_le_inl_sq : ∀ {d : Nat} (v : (Lorentz.Contr d).V.carrier),
--   Real.instLE.le (LinearMap.instFunLike.coe Lorentz.contrContrContractField (TensorProduct.tmul Real v v))
--     (instHPow.hPow (v.val (Sum.inl 0)) 2)

-- Source: PhysLean (Lorentz.Vector.tensor_basis_repr_toTensor_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_tensor_basis_repr_totensor_apply : ∀ {d : Nat} (p : Lorentz.Vector d)
--   (μ : TensorSpecies.Tensor.ComponentIdx (Matrix.vecCons realLorentzTensor.Color.up Matrix.vecEmpty)),
--   Eq
--     (Finsupp.instFunLike.coe
--       (EquivLike.toFunLike.coe
--         (TensorSpecies.Tensor.basis (Matrix.vecCons realLorentzTensor.Color.up Matrix.vecEmpty)).repr
--         (EquivLike.toFunLike.coe Lorentz.Vector.tensorial.toTensor p))
--       μ)
--     (p (EquivLike.toFunLike.coe Lorentz.Vector.indexEquiv μ))

-- Source: PhysLean (Lorentz.ContrMod.toSelfAdjoint)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_toselfadjoint : LinearEquiv (RingHom.id Real) (Lorentz.ContrMod 3)
--   (Subtype fun x => SetLike.instMembership.mem (selfAdjoint (Matrix (Fin 2) (Fin 2) Complex)) x)

-- Source: PhysLean (Lorentz.Velocity.one_add_minkowskiProduct_neq_zero)
-- [complex signature, not re-axiomatized]
-- lorentz_velocity_one_add_minkowskiproduct_neq_zero : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem),
--   Ne
--     (instHAdd.hAdd 1
--       (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct u.val) v.val))
--     0

-- Source: PhysLean (LorentzGroup.boost_zero_inr_succ_inl_0)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_zero_inr_succ_inl_0 : ∀ {d : Nat} {β : Real} (hβ : Real.instLT.lt (abs β) 1) (i : Fin d),
--   Eq ((LorentzGroup.boost 0 β hβ).val (Sum.inr i.succ) (Sum.inl 0)) 0

-- Source: PhysLean (Lorentz.contrCoUnit)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcounit : Action.instCategory.Hom
--   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--   (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo)

-- Source: PhysLean (Lorentz.CoVector.instAddCommMonoid)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_instaddcommmonoid : {d : Nat} → AddCommMonoid (Lorentz.CoVector d)

-- Source: PhysLean (realLorentzTensor.Color.ctorIdx)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_color_ctoridx : realLorentzTensor.Color → Nat

-- Source: PhysLean (Lorentz.Vector.instNorm)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_instnorm : (d : Nat) → Norm (Lorentz.Vector d)

-- Source: PhysLean (LorentzGroup.orthochronoustoVelocity)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_orthochronoustovelocity : {d : Nat} → {Λ : (LorentzGroup d).Elem} → LorentzGroup.IsOrthochronous Λ → (Lorentz.Velocity d).Elem

-- Source: PhysLean (LorentzGroup.restricted.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_restricted_eq_1 : ∀ (d : Nat),
--   Eq (LorentzGroup.restricted d)
--     { carrier := setOf fun Λ => And (LorentzGroup.IsProper Λ) (LorentzGroup.IsOrthochronous Λ), mul_mem' := ⋯,
--       one_mem' := ⋯, inv_mem' := ⋯ }

-- Source: PhysLean (Lorentz.Vector.equivPi_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_equivpi_apply : ∀ {d : Nat} (v : Lorentz.Vector d) (i : Sum (Fin 1) (Fin d)),
--   Eq (EquivLike.toFunLike.coe (Lorentz.Vector.equivPi d) v i) (v i)

-- Source: PhysLean (LorentzGroup.orthchroMapReal_minus_one_or_one)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_orthchromapreal_minus_one_or_one : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Or (Eq (ContinuousMap.instFunLike.coe LorentzGroup.orthchroMapReal Λ) (-1))
--     (Eq (ContinuousMap.instFunLike.coe LorentzGroup.orthchroMapReal Λ) 1)

-- Source: PhysLean (realLorentzTensor.realLorentzTensorSyntax)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_reallorentztensorsyntax : Lean.ParserDescr

-- Source: PhysLean (LorentzGroup.IsOrthochronous.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_isorthochronous_eq_1 : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Eq (LorentzGroup.IsOrthochronous Λ) (Real.instLE.le 0 (Λ.val (Sum.inl 0) (Sum.inl 0)))

-- Source: PhysLean (Lorentz.coContrContract)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrcontract : {d : Nat} →
--   Action.instCategory.Hom (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d))
--     (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem))

-- Source: PhysLean (LorentzGroup.instIsTopologicalGroupMultiplicativeZModOfNatNat)
/-- The instance of a topological group on `ℤ₂` defined via the discrete topology.  -/
axiom lorentzgroup_instistopologicalgroupmultiplicativezmodofnatnat :
  IsTopologicalGroup (Multiplicative (ZMod 2))

-- Source: PhysLean (Lorentz.CoVector.instNorm)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_instnorm : (d : Nat) → Norm (Lorentz.CoVector d)

-- Source: PhysLean (LorentzGroup.toComplex_mul_minkowskiMatrix_mul_transpose)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_tocomplex_mul_minkowskimatrix_mul_transpose : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Eq
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--       (instHMul.hMul (MonoidHom.instFunLike.coe LorentzGroup.toComplex Λ)
--         (minkowskiMatrix.map (RingHom.instFunLike.coe Complex.ofRealHom)))
--       (MonoidHom.instFunLike.coe LorentzGroup.toComplex Λ).transpose)
--     (minkowskiMatrix.map (RingHom.instFunLike.coe Complex.ofRealHom))

-- Source: PhysLean (LorentzGroup.generalizedBoost_continuous_fst)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_generalizedboost_continuous_fst : ∀ {d : Nat} (u : (Lorentz.Velocity d).Elem), Continuous fun x => LorentzGroup.generalizedBoost x u

-- Source: PhysLean (CliffordAlgebra.lift)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_lift : {R : Type u_1} →
--   [inst : CommRing R] →
--     {M : Type u_2} →
--       [inst_1 : AddCommGroup M] →
--         [inst_2 : Module R M] →
--           (Q : QuadraticForm R M) →
--             {A : Type u_3} →
--               [inst_3 : Semiring A] →
--                 [inst_4 : Algebra R A] →
--                   Equiv
--                     (Subtype fun f =>
--                       ∀ (m : M),
--                         Eq (instHMul.hMul (LinearMap.instFunLike.coe f m) (LinearMap.instFunLike.coe f m))
--                           (RingHom.instFunLike.coe (algebraMap R A) (QuadraticMap.instFunLike.coe Q m)))
--                     (AlgHom R (CliffordAlgebra Q) A)

-- Source: PhysLean (LorentzGroup.genearlizedBoost_apply_basis)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_genearlizedboost_apply_basis : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem) (μ : Sum (Fin 1) (Fin d)),
--   Eq (instHSMul.hSMul (LorentzGroup.generalizedBoost u v) (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ))
--     (instHSub.hSub
--       (instHAdd.hAdd (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ)
--         (instHSMul.hSMul (instHMul.hMul (instHMul.hMul 2 (minkowskiMatrix μ μ)) (u.val μ)) v.val))
--       (instHSMul.hSMul
--         (instHDiv.hDiv (instHMul.hMul (minkowskiMatrix μ μ) (instHAdd.hAdd (u.val μ) (v.val μ)))
--           (instHAdd.hAdd 1
--             (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct u.val)
--               v.val)))
--         (instHAdd.hAdd u.val v.val)))

-- Source: PhysLean (complexLorentzTensor.contrMetric_contr_coMetric)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrmetric_contr_cometric : Eq
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.contrT 2 1 2 ⋯)
--     (LinearMap.instFunLike.coe
--       (LinearMap.instFunLike.coe TensorSpecies.Tensor.prodT
--         (EquivLike.toFunLike.coe
--           (TensorSpecies.Tensorial.self complexLorentzTensor
--               (Matrix.vecCons complexLorentzTensor.Color.up
--                 (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty))).toTensor
--           complexLorentzTensor.contrMetric))
--       (EquivLike.toFunLike.coe
--         (TensorSpecies.Tensorial.self complexLorentzTensor
--             (Matrix.vecCons complexLorentzTensor.Color.down
--               (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty))).toTensor
--         complexLorentzTensor.coMetric)))
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT (Matrix.vecCons 0 (Matrix.vecCons 1 Matrix.vecEmpty)) ⋯)
--     (EquivLike.toFunLike.coe
--       (TensorSpecies.Tensorial.self complexLorentzTensor
--           (Matrix.vecCons complexLorentzTensor.Color.up
--             (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty))).toTensor
--       complexLorentzTensor.contrCoUnit))

-- Source: PhysLean (CliffordAlgebra.mul_add_swap_eq_polar_of_forall_mul_self_eq)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_mul_add_swap_eq_polar_of_forall_mul_self_eq : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   {Q : QuadraticForm R M} {A : Type u_4} [inst_3 : Ring A] [inst_4 : Algebra R A] (f : LinearMap (RingHom.id R) M A),
--   (∀ (x : M),
--       Eq (instHMul.hMul (LinearMap.instFunLike.coe f x) (LinearMap.instFunLike.coe f x))
--         (RingHom.instFunLike.coe (algebraMap R A) (QuadraticMap.instFunLike.coe Q x))) →
--     ∀ (a b : M),
--       Eq
--         (instHAdd.hAdd (instHMul.hMul (LinearMap.instFunLike.coe f a) (LinearMap.instFunLike.coe f b))
--           (instHMul.hMul (LinearMap.instFunLike.coe f b) (LinearMap.instFunLike.coe f a)))
--         (RingHom.instFunLike.coe (algebraMap R A) (QuadraticMap.polar (QuadraticMap.instFunLike.coe Q) a b))

-- Source: PhysLean (Lorentz.CoVector.instChartedSpace)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_instchartedspace : {d : Nat} → ChartedSpace (Lorentz.CoVector d) (Lorentz.CoVector d)

-- Source: PhysLean (complexLorentzTensor.contrMetric_symm)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrmetric_symm : Eq
--   (EquivLike.toFunLike.coe
--     (TensorSpecies.Tensorial.self complexLorentzTensor
--         (Matrix.vecCons complexLorentzTensor.Color.up
--           (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty))).toTensor
--     complexLorentzTensor.contrMetric)
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT (Matrix.vecCons 1 (Matrix.vecCons 0 Matrix.vecEmpty)) ⋯)
--     (EquivLike.toFunLike.coe
--       (TensorSpecies.Tensorial.self complexLorentzTensor
--           (Matrix.vecCons complexLorentzTensor.Color.up
--             (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty))).toTensor
--       complexLorentzTensor.contrMetric))

-- Source: PhysLean (Lorentz.contrCoContrBi)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcocontrbi : LinearMap (RingHom.id Complex) Lorentz.complexContr.V.carrier
--   (LinearMap (RingHom.id Complex) Lorentz.complexCo.V.carrier Complex)

-- Source: PhysLean (Lorentz.ContrMod.toSelfAdjoint_symm_basis)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_toselfadjoint_symm_basis : ∀ (i : Sum (Fin 1) (Fin 3)),
--   Eq
--     (EquivLike.toFunLike.coe Lorentz.ContrMod.toSelfAdjoint.symm
--       (Module.Basis.instFunLike.coe PauliMatrix.pauliBasis' i))
--     (Module.Basis.instFunLike.coe Lorentz.ContrMod.stdBasis i)

-- Source: PhysLean (Lorentz.contrIsoCo)
-- [complex signature, not re-axiomatized]
-- lorentz_contrisoco : (d : Nat) → CategoryTheory.Iso (Lorentz.Contr d) (Lorentz.Co d)

-- Source: PhysLean (LorentzGroup.toVector_minkowskiProduct_self)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_tovector_minkowskiproduct_self : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Eq
--     (ContinuousLinearMap.funLike.coe
--       (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct (LorentzGroup.toVector Λ))
--       (LorentzGroup.toVector Λ))
--     1

-- Source: PhysLean (LorentzGroup.boost_inl_0_inr_self)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_inl_0_inr_self : ∀ {d : Nat} (i : Fin d) {β : Real} (hβ : Real.instLT.lt (abs β) 1),
--   Eq ((LorentzGroup.boost i β hβ).val (Sum.inl 0) (Sum.inr i)) (instHMul.hMul (Real.instNeg.neg (LorentzGroup.γ β)) β)

-- Source: PhysLean (complexLorentzTensor.altLeftMetric_eq_fromPairT)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altleftmetric_eq_frompairt : Eq complexLorentzTensor.altLeftMetric
--   (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT Fermion.altLeftMetricVal)

-- Source: PhysLean (Lorentz.Vector.timeLike_iff_time_lt_space)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_timelike_iff_time_lt_space : ∀ {d : Nat} {v : Lorentz.Vector d},
--   Iff (Eq v.causalCharacter Lorentz.Vector.CausalCharacter.timeLike)
--     (Real.instLT.lt ((PiLp.innerProductSpace fun x => Real).inner Real v.spatialPart v.spatialPart)
--       (instHMul.hMul (v (Sum.inl 0)) (v (Sum.inl 0))))

-- Source: PhysLean (SpaceTime.properTime_zero_ofLightLike)
-- [complex signature, not re-axiomatized]
-- spacetime_propertime_zero_oflightlike : ∀ {d : Nat} (q p : SpaceTime d),
--   Eq (Lorentz.Vector.causalCharacter (instHSub.hSub p q)) Lorentz.Vector.CausalCharacter.lightLike →
--     Eq (q.properTime p) 0

-- Source: PhysLean (Lorentz.Vector.smul_neg)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_smul_neg : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem) (p : Lorentz.Vector d),
--   Eq (instHSMul.hSMul Λ (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg p))
--     (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg (instHSMul.hSMul Λ p))

-- Source: PhysLean (Lorentz.Vector.isLorentz_iff_toMatrix_mem_lorentzGroup)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_islorentz_iff_tomatrix_mem_lorentzgroup : ∀ {d : Nat} (f : LinearMap (RingHom.id Real) (Lorentz.Vector d) (Lorentz.Vector d)),
--   Iff (Lorentz.Vector.IsLorentz f)
--     (Set.instMembership.mem (LorentzGroup d)
--       (EquivLike.toFunLike.coe (LinearMap.toMatrix Lorentz.Vector.basis Lorentz.Vector.basis) f))

-- Source: PhysLean (complexLorentzTensor.altRightRightUnit_eq_fromPairT)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altrightrightunit_eq_frompairt : Eq complexLorentzTensor.altRightRightUnit
--   (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT Fermion.altRightRightUnitVal)

-- Source: PhysLean (Lorentz.Vector.isLorentz_iff)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_islorentz_iff : ∀ {d : Nat} (f : LinearMap (RingHom.id Real) (Lorentz.Vector d) (Lorentz.Vector d)),
--   Iff (Lorentz.Vector.IsLorentz f)
--     (∀ (p q : Lorentz.Vector d),
--       Eq
--         (ContinuousLinearMap.funLike.coe
--           (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct (LinearMap.instFunLike.coe f p))
--           (LinearMap.instFunLike.coe f q))
--         (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct p) q))

-- Source: PhysLean (Lorentz.SL2C.toSelfAdjointMap_mul)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_toselfadjointmap_mul : ∀ (M N : Matrix (Fin 2) (Fin 2) Complex),
--   Eq (Lorentz.SL2C.toSelfAdjointMap' (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul M N))
--     ((Lorentz.SL2C.toSelfAdjointMap' M).comp (Lorentz.SL2C.toSelfAdjointMap' N))

-- Source: PhysLean (Lorentz.Vector.isNormedAddCommGroup)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_isnormedaddcommgroup : (d : Nat) → NormedAddCommGroup (Lorentz.Vector d)

-- Source: PhysLean (SpaceTime.schwartzAction_surjective)
-- [complex signature, not re-axiomatized]
-- spacetime_schwartzaction_surjective : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Function.Surjective (ContinuousLinearMap.funLike.coe (MonoidHom.instFunLike.coe SpaceTime.schwartzAction Λ))

-- Source: PhysLean (CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_ι_mul_ι_add_swap_of_isortho : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   {Q : QuadraticForm R M} {a b : M},
--   QuadraticMap.IsOrtho Q a b →
--     Eq
--       (instHAdd.hAdd
--         (instHMul.hMul (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) a)
--           (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) b))
--         (instHMul.hMul (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) b)
--           (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) a)))
--       0

-- Source: PhysLean (complexLorentzTensor.leftAltLeftUnit_eq_fromPairT)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_leftaltleftunit_eq_frompairt : Eq complexLorentzTensor.leftAltLeftUnit
--   (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT Fermion.leftAltLeftUnitVal)

-- Source: PhysLean (Lorentz.contrBasisFin.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_contrbasisfin_eq_1 : ∀ (d : Nat), Eq (Lorentz.contrBasisFin d) ((Lorentz.contrBasis d).reindex finSumFinEquiv)

-- Source: PhysLean (LorentzGroup.genBoostAux₁.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_genboostaux₁_eq_1 : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem),
--   Eq (LorentzGroup.genBoostAux₁ u v)
--     {
--       toFun := fun x =>
--         instHSMul.hSMul
--           (instHMul.hMul 2
--             (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct x) u.val))
--           v.val,
--       map_add' := ⋯, map_smul' := ⋯ }

-- Source: PhysLean (LorentzGroup.transpose_one)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_transpose_one : ∀ {d : Nat}, Eq (LorentzGroup.transpose 1) 1

-- Source: PhysLean (Lorentz.CoMod.stdBasis_repr_apply_support_val)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_stdbasis_repr_apply_support_val : ∀ {d : Nat} (a : Lorentz.CoMod d),
--   Eq (EquivLike.toFunLike.coe Lorentz.CoMod.stdBasis.repr a).support.val (Multiset.map Subtype.val Finset.univ.val)

-- Source: PhysLean (realLorentzTensor.toComplex_eq_sum_basis)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_tocomplex_eq_sum_basis : ∀ {n : Nat} (c : Fin n → realLorentzTensor.Color) (v : realLorentzTensor.Tensor c),
--   Eq (LinearMap.instFunLike.coe realLorentzTensor.toComplex v)
--     (Finset.univ.sum fun i =>
--       instHSMul.hSMul
--         (Finsupp.instFunLike.coe (EquivLike.toFunLike.coe (TensorSpecies.Tensor.basis c).repr v)
--           (EquivLike.toFunLike.coe TensorSpecies.Tensor.ComponentIdx.complexify.symm i))
--         (Module.Basis.instFunLike.coe (TensorSpecies.Tensor.basis (Function.comp realLorentzTensor.colorToComplex c))
--           i))

-- Source: PhysLean (LorentzGroup.mem_iff_invariant)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_mem_iff_invariant : ∀ {d : Nat} {Λ : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real},
--   Iff (Set.instMembership.mem (LorentzGroup d) Λ)
--     (∀ (w v : (Lorentz.Contr d).V.carrier),
--       Eq
--         (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--           (TensorProduct.tmul Real (Lorentz.ContrMod.mulVec Λ v) (Lorentz.ContrMod.mulVec Λ w)))
--         (LinearMap.instFunLike.coe Lorentz.contrContrContractField (TensorProduct.tmul Real v w)))

-- Source: PhysLean (complexLorentzTensor.Color.ctorElimType)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_color_ctorelimtype : {motive : complexLorentzTensor.Color → Sort u} → Nat → Sort (max 1 u)

-- Source: PhysLean (LorentzGroup.isProper_id)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_isproper_id : ∀ {d : Nat}, LorentzGroup.IsProper 1

-- Source: PhysLean (complexLorentzTensor.Color.down.elim)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_color_down_elim : {motive : complexLorentzTensor.Color → Sort u} →
--   (t : complexLorentzTensor.Color) → Eq t.ctorIdx 5 → motive complexLorentzTensor.Color.down → motive t

-- Source: PhysLean (Lorentz.SL2C.toLorentzGroup_eq_pauliBasis')
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_tolorentzgroup_eq_paulibasis' : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M).val
--     (EquivLike.toFunLike.coe (LinearMap.toMatrix PauliMatrix.pauliBasis' PauliMatrix.pauliBasis')
--       (Lorentz.SL2C.toSelfAdjointMap M))

-- Source: PhysLean (Lorentz.complexContrBasis_ρ_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcontrbasis_ρ_apply : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex) (i j : Sum (Fin 1) (Fin 3)),
--   Eq
--     (EquivLike.toFunLike.coe (LinearMap.toMatrix Lorentz.complexContrBasis Lorentz.complexContrBasis)
--       (MonoidHom.instFunLike.coe Lorentz.complexContr.ρ M) i j)
--     (MonoidHom.instFunLike.coe LorentzGroup.toComplex (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M) i j)

-- Source: PhysLean (Lorentz.CoVector.instInnerReal)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_instinnerreal : (d : Nat) → Inner Real (Lorentz.CoVector d)

-- Source: PhysLean (Lorentz.contrBasisFin_repr_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_contrbasisfin_repr_apply : ∀ {d : Nat} (p : (Lorentz.Contr d).V.carrier) (i : Fin (instHAdd.hAdd 1 d)),
--   Eq (Finsupp.instFunLike.coe (EquivLike.toFunLike.coe (Lorentz.contrBasisFin d).repr p) i)
--     (p.val (EquivLike.toFunLike.coe finSumFinEquiv.symm i))

-- Source: PhysLean (Lorentz.ContrMod.toSelfAdjoint_apply_coe)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_toselfadjoint_apply_coe : ∀ (x : Lorentz.ContrMod 3),
--   Eq (EquivLike.toFunLike.coe Lorentz.ContrMod.toSelfAdjoint x).val
--     (instHSub.hSub
--       (instHSub.hSub
--         (instHSub.hSub (instHSMul.hSMul (x.toFin1dℝ (Sum.inl 0)) (PauliMatrix.pauliMatrix (Sum.inl 0)))
--           (instHSMul.hSMul (x.toFin1dℝ (Sum.inr 0)) (PauliMatrix.pauliMatrix (Sum.inr 0))))
--         (instHSMul.hSMul (x.toFin1dℝ (Sum.inr 1)) (PauliMatrix.pauliMatrix (Sum.inr 1))))
--       (instHSMul.hSMul (x.toFin1dℝ (Sum.inr 2)) (PauliMatrix.pauliMatrix (Sum.inr 2))))

-- Source: PhysLean (Lorentz.ContrℂModule.val_add)
-- [complex signature, not re-axiomatized]
-- lorentz_contrℂmodule_val_add : ∀ (ψ ψ' : Lorentz.ContrℂModule), Eq (instHAdd.hAdd ψ ψ').val (instHAdd.hAdd ψ.val ψ'.val)

-- Source: PhysLean (complexLorentzTensor.altLeftLeftUnit_eq_altLeftBasis_leftBasis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altleftleftunit_eq_altleftbasis_leftbasis : Eq complexLorentzTensor.altLeftLeftUnit
--   (Finset.univ.sum fun i =>
--     LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altLeftBasis i)
--         (Module.Basis.instFunLike.coe Fermion.leftBasis i)))

-- Source: PhysLean (Lorentz.ContrMod.toSpace.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_tospace_eq_1 : ∀ {d : Nat} (v : Lorentz.ContrMod d), Eq v.toSpace { ofLp := Function.comp v.val Sum.inr }

-- Source: PhysLean (complexLorentzTensor.coMetric)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cometric : complexLorentzTensor.Tensor
--   (Matrix.vecCons complexLorentzTensor.Color.down (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty))

-- Source: PhysLean (SpaceTime.distTimeSlice_symm_apply)
-- [complex signature, not re-axiomatized]
-- spacetime_disttimeslice_symm_apply : ∀ {M : Type} {d : Nat} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] (c : SpeedOfLight)
--   (f : Distribution Real (Prod Time (Space d)) M) (κ : SchwartzMap (SpaceTime d) Real),
--   Eq (ContinuousLinearMap.funLike.coe (EquivLike.toFunLike.coe (SpaceTime.distTimeSlice c).symm f) κ)
--     (ContinuousLinearMap.funLike.coe f
--       (ContinuousLinearMap.funLike.coe
--         (SchwartzMap.compCLMOfContinuousLinearEquiv Real (SpaceTime.toTimeAndSpace c).symm) κ))

-- Source: PhysLean (Lorentz.Vector.CausalCharacter.timeLike.elim)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causalcharacter_timelike_elim : {motive : Lorentz.Vector.CausalCharacter → Sort u} →
--   (t : Lorentz.Vector.CausalCharacter) → Eq t.ctorIdx 0 → motive Lorentz.Vector.CausalCharacter.timeLike → motive t

-- Source: PhysLean (complexLorentzTensor.coMetric_symm)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cometric_symm : Eq
--   (EquivLike.toFunLike.coe
--     (TensorSpecies.Tensorial.self complexLorentzTensor
--         (Matrix.vecCons complexLorentzTensor.Color.down
--           (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty))).toTensor
--     complexLorentzTensor.coMetric)
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT (Matrix.vecCons 1 (Matrix.vecCons 0 Matrix.vecEmpty)) ⋯)
--     (EquivLike.toFunLike.coe
--       (TensorSpecies.Tensorial.self complexLorentzTensor
--           (Matrix.vecCons complexLorentzTensor.Color.down
--             (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty))).toTensor
--       complexLorentzTensor.coMetric))

-- Source: PhysLean (LorentzGroup.toGL_injective)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_togl_injective : ∀ {d : Nat}, Function.Injective (MonoidHom.instFunLike.coe LorentzGroup.toGL)

-- Source: PhysLean (LorentzGroup.boost_inr_self_inr_other)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_inr_self_inr_other : ∀ {d : Nat} {i j : Fin d} {β : Real} (hβ : Real.instLT.lt (abs β) 1),
--   Ne j i → Eq ((LorentzGroup.boost i β hβ).val (Sum.inr i) (Sum.inr j)) 0

-- Source: PhysLean (Lorentz.Vector.boost_inr_other_eq)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_boost_inr_other_eq : ∀ {d : Nat} (i j : Fin d),
--   Ne j i →
--     ∀ (β : Real) (hβ : Real.instLT.lt (abs β) 1) (p : Lorentz.Vector d),
--       Eq (instHSMul.hSMul (LorentzGroup.boost i β hβ) p (Sum.inr j)) (p (Sum.inr j))

-- Source: PhysLean (realLorentzTensor.contrT_basis_repr_apply_eq_dropPairSection)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_contrt_basis_repr_apply_eq_droppairsection : ∀ {n d : Nat} {c : Fin (instHAdd.hAdd (instHAdd.hAdd n 1) 1) → realLorentzTensor.Color}
--   {i j : Fin (instHAdd.hAdd (instHAdd.hAdd n 1) 1)} (h : And (Ne i j) (Eq ((realLorentzTensor d).τ (c i)) (c j)))
--   (t : (realLorentzTensor d).Tensor c)
--   (b : TensorSpecies.Tensor.ComponentIdx (Function.comp c (TensorSpecies.Tensor.Pure.dropPairEmb i j))),
--   Eq
--     (Finsupp.instFunLike.coe
--       (EquivLike.toFunLike.coe
--         (TensorSpecies.Tensor.basis (Function.comp c (TensorSpecies.Tensor.Pure.dropPairEmb i j))).repr
--         (LinearMap.instFunLike.coe (TensorSpecies.Tensor.contrT n i j h) t))
--       b)
--     (Finset.univ.sum fun x =>
--       instHMul.hMul (Finsupp.instFunLike.coe (EquivLike.toFunLike.coe (TensorSpecies.Tensor.basis c).repr t) x.val)
--         (ite (Eq (x.val i).val (x.val j).val) 1 0))

-- Source: PhysLean (Lorentz.Vector.map_minkowskiProduct_eq_adjoint)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_map_minkowskiproduct_eq_adjoint : ∀ {d : Nat} (f : LinearMap (RingHom.id Real) (Lorentz.Vector d) (Lorentz.Vector d)) (p q : Lorentz.Vector d),
--   Eq
--     (ContinuousLinearMap.funLike.coe
--       (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct (LinearMap.instFunLike.coe f p)) q)
--     (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct p)
--       (LinearMap.instFunLike.coe (Lorentz.Vector.adjoint f) q))

-- Source: PhysLean (LorentzGroup.instTopologicalSpaceMultiplicativeZModOfNatNat)
/-- The instance of a topological space on `ℤ₂` corresponding to the discrete topology.  -/
axiom lorentzgroup_insttopologicalspacemultiplicativezmodofnatnat :
  TopologicalSpace (Multiplicative (ZMod 2))

-- Source: PhysLean (complexLorentzTensor.leftMetric_eq_fromPairT)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_leftmetric_eq_frompairt : Eq complexLorentzTensor.leftMetric (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT Fermion.leftMetricVal)

-- Source: PhysLean (Lorentz.Vector.smul_eq_mulVec)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_smul_eq_mulvec : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem) (p : Lorentz.Vector d), Eq (instHSMul.hSMul Λ p) (Λ.val.mulVec p)

-- Source: PhysLean (Lorentz.coContrUnitVal.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrunitval_eq_1 : Eq Lorentz.coContrUnitVal (EquivLike.toFunLike.coe Lorentz.coContrToMatrix.symm 1)

-- Source: PhysLean (Lorentz.ContrMod.toSpace)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_tospace : {d : Nat} → Lorentz.ContrMod d → EuclideanSpace Real (Fin d)

-- Source: PhysLean (complexLorentzTensor.coMetric_contr_contrMetric)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cometric_contr_contrmetric : Eq
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.contrT 2 1 2 ⋯)
--     (LinearMap.instFunLike.coe
--       (LinearMap.instFunLike.coe TensorSpecies.Tensor.prodT
--         (EquivLike.toFunLike.coe
--           (TensorSpecies.Tensorial.self complexLorentzTensor
--               (Matrix.vecCons complexLorentzTensor.Color.down
--                 (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty))).toTensor
--           complexLorentzTensor.coMetric))
--       (EquivLike.toFunLike.coe
--         (TensorSpecies.Tensorial.self complexLorentzTensor
--             (Matrix.vecCons complexLorentzTensor.Color.up
--               (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty))).toTensor
--         complexLorentzTensor.contrMetric)))
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT (Matrix.vecCons 0 (Matrix.vecCons 1 Matrix.vecEmpty)) ⋯)
--     (EquivLike.toFunLike.coe
--       (TensorSpecies.Tensorial.self complexLorentzTensor
--           (Matrix.vecCons complexLorentzTensor.Color.down
--             (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty))).toTensor
--       complexLorentzTensor.coContrUnit))

-- Source: PhysLean (Lorentz.CoMod.stdBasis_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_stdbasis_apply : ∀ {d : Nat} (μ ν : Sum (Fin 1) (Fin d)),
--   Eq ((Module.Basis.instFunLike.coe Lorentz.CoMod.stdBasis μ).val ν) (ite (Eq μ ν) 1 0)

-- Source: PhysLean (minkowskiMatrix.eq_1)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_eq_1 : ∀ {d : Nat}, Eq minkowskiMatrix (LieAlgebra.Orthogonal.indefiniteDiagonal (Fin 1) (Fin d) Real)

-- Source: PhysLean (minkowskiMatrix.dual_transpose)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_dual_transpose : ∀ {d : Nat} (Λ : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real),
--   Eq (minkowskiMatrix.dual Λ.transpose) (minkowskiMatrix.dual Λ).transpose

-- Source: PhysLean (CliffordAlgebra.lift_ι_apply)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_lift_ι_apply : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   {Q : QuadraticForm R M} {A : Type u_3} [inst_3 : Semiring A] [inst_4 : Algebra R A] (f : LinearMap (RingHom.id R) M A)
--   (cond :
--     ∀ (m : M),
--       Eq (instHMul.hMul (LinearMap.instFunLike.coe f m) (LinearMap.instFunLike.coe f m))
--         (RingHom.instFunLike.coe (algebraMap R A) (QuadraticMap.instFunLike.coe Q m)))
--   (x : M),
--   Eq
--     (AlgHom.funLike.coe (EquivLike.toFunLike.coe (CliffordAlgebra.lift Q) ⟨f, cond⟩)
--       (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) x))
--     (LinearMap.instFunLike.coe f x)

-- Source: PhysLean (realLorentzTensor.toComplex)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_tocomplex : {n : Nat} →
--   {c : Fin n → realLorentzTensor.Color} →
--     LinearMap Complex.ofRealHom (realLorentzTensor.Tensor c)
--       (complexLorentzTensor.Tensor (Function.comp realLorentzTensor.colorToComplex c))

-- Source: PhysLean (Lorentz.contrBasisFin_toFin1dℝ)
-- [complex signature, not re-axiomatized]
-- lorentz_contrbasisfin_tofin1dℝ : ∀ {d : Nat} (i : Fin (instHAdd.hAdd 1 d)),
--   Eq (Lorentz.ContrMod.toFin1dℝ (Module.Basis.instFunLike.coe (Lorentz.contrBasisFin d) i))
--     (Pi.single (EquivLike.toFunLike.coe finSumFinEquiv.symm i) 1)

-- Source: PhysLean (Lorentz.Vector.minkowskiProductMap_toCoord)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproductmap_tocoord : ∀ {d : Nat} (p q : Lorentz.Vector d),
--   Eq (p.minkowskiProductMap q)
--     (instHSub.hSub (instHMul.hMul (p (Sum.inl 0)) (q (Sum.inl 0)))
--       (Finset.univ.sum fun i => instHMul.hMul (p (Sum.inr i)) (q (Sum.inr i))))

-- Source: PhysLean (Lorentz.Vector.coord_differentiable)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_coord_differentiable : ∀ {d : Nat} (i : Sum (Fin 1) (Fin d)), Differentiable Real fun v => v i

-- Source: PhysLean (complexLorentzTensor.altLeftMetric_antisymm)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altleftmetric_antisymm : Eq
--   (EquivLike.toFunLike.coe
--     (TensorSpecies.Tensorial.self complexLorentzTensor
--         (Matrix.vecCons complexLorentzTensor.Color.downL
--           (Matrix.vecCons complexLorentzTensor.Color.downL Matrix.vecEmpty))).toTensor
--     complexLorentzTensor.altLeftMetric)
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT (Matrix.vecCons 1 (Matrix.vecCons 0 Matrix.vecEmpty)) ⋯)
--     (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg
--       (EquivLike.toFunLike.coe
--         (TensorSpecies.Tensorial.self complexLorentzTensor
--             (Matrix.vecCons complexLorentzTensor.Color.downL
--               (Matrix.vecCons complexLorentzTensor.Color.downL Matrix.vecEmpty))).toTensor
--         complexLorentzTensor.altLeftMetric)))

-- Source: PhysLean (Lorentz.SL2C.toSelfAdjointMap_det_one')
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_toselfadjointmap_det_one' : ∀ {M : Matrix (Fin 2) (Fin 2) Complex},
--   M.IsUpperTriangular → Eq M.det 1 → Eq (MonoidHom.instFunLike.coe LinearMap.det (Lorentz.SL2C.toSelfAdjointMap' M)) 1

-- Source: PhysLean (LorentzGroup.toProd)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_toprod : {d : Nat} →
--   MonoidHom (LorentzGroup d).Elem
--     (Prod (Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real)
--       (MulOpposite (Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real)))

-- Source: PhysLean (realLorentzTensor.permT_toComplex)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_permt_tocomplex : InformalLemma

-- Source: PhysLean (complexLorentzTensor.leftAltLeftUnit.eq_1)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_leftaltleftunit_eq_1 : Eq complexLorentzTensor.leftAltLeftUnit (TensorSpecies.unitTensor complexLorentzTensor.Color.downL)

-- Source: PhysLean (Lorentz.coModContrModBi)
-- [complex signature, not re-axiomatized]
-- lorentz_comodcontrmodbi : (d : Nat) → LinearMap (RingHom.id Real) (Lorentz.CoMod d) (LinearMap (RingHom.id Real) (Lorentz.ContrMod d) Real)

-- Source: PhysLean (complexLorentzTensor.Color.toCtorIdx)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_color_toctoridx : complexLorentzTensor.Color → Nat

-- Source: PhysLean (Lorentz.complexContrBasis_toFin13ℂ)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcontrbasis_tofin13ℂ : ∀ (i : Sum (Fin 1) (Fin 3)),
--   Eq (Lorentz.ContrℂModule.toFin13ℂ (Module.Basis.instFunLike.coe Lorentz.complexContrBasis i)) (Pi.single i 1)

-- Source: PhysLean (SpaceTime.space_toCoord_symm)
-- [complex signature, not re-axiomatized]
-- spacetime_space_tocoord_symm : ∀ {d : Nat} (f : Sum (Fin 1) (Fin d) → Real),
--   Eq (ContinuousLinearMap.funLike.coe SpaceTime.space f).val fun i => f (Sum.inr i)

-- Source: PhysLean (LorentzGroup.toComplex)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_tocomplex : {d : Nat} → MonoidHom (LorentzGroup d).Elem (Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Complex)

-- Source: PhysLean (Lorentz.Vector.minkowskiProduct_invariant)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproduct_invariant : ∀ {d : Nat} (p q : Lorentz.Vector d) (Λ : (LorentzGroup d).Elem),
--   Eq
--     (ContinuousLinearMap.funLike.coe
--       (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct (instHSMul.hSMul Λ p)) (instHSMul.hSMul Λ q))
--     (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct p) q)

-- Source: PhysLean (Lorentz.SL2C.transpose_coe)
axiom lorentz_sl2c_transpose_coe :
  ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex), Eq M.val.transpose M.transpose.val

-- Source: PhysLean (realLorentzTensor.derivative)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_derivative : {d n m : Nat} →
--   {cm : Fin m → realLorentzTensor.Color} →
--     {cn : Fin n → realLorentzTensor.Color} →
--       ((realLorentzTensor d).Tensor cm → (realLorentzTensor d).Tensor cn) →
--         (realLorentzTensor d).Tensor cm →
--           (realLorentzTensor d).Tensor (Fin.append (fun i => (realLorentzTensor d).τ (cm i)) cn)

-- Source: PhysLean (CliffordAlgebra.lift_symm_apply)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_lift_symm_apply : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   (Q : QuadraticForm R M) {A : Type u_3} [inst_3 : Semiring A] [inst_4 : Algebra R A]
--   (F : AlgHom R (CliffordAlgebra Q) A),
--   Eq (EquivLike.toFunLike.coe (CliffordAlgebra.lift Q).symm F) ⟨F.toLinearMap.comp (CliffordAlgebra.ι Q), ⋯⟩

-- Source: PhysLean (Lorentz.coContrToMatrixRe)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrtomatrixre : {d : Nat} →
--   LinearEquiv (RingHom.id Real) (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)).V.carrier
--     (Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real)

-- Source: PhysLean (Lorentz.CoMod.stdBasis)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_stdbasis : {d : Nat} → Module.Basis (Sum (Fin 1) (Fin d)) Real (Lorentz.CoMod d)

-- Source: PhysLean (Lorentz.Vector)
-- [complex signature, not re-axiomatized]
-- lorentz_vector : optParam Nat 3 → Type

-- Source: PhysLean (Lorentz.CoMod.mulVec_toFin1dℝ)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_mulvec_tofin1dℝ : ∀ {d : Nat} (M : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real) (v : Lorentz.CoMod d),
--   Eq (Lorentz.CoMod.mulVec M v).toFin1dℝ (M.mulVec v.toFin1dℝ)

-- Source: PhysLean (CliffordAlgebra.instSMulCommClass)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_instsmulcommclass : ∀ {R : Type u_3} {S : Type u_4} {A : Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]
--   [inst_2 : AddCommGroup M] [inst_3 : CommRing A] [inst_4 : Algebra R A] [inst_5 : Algebra S A] [inst_6 : Module R M]
--   [inst_7 : Module S M] [inst_8 : Module A M] (Q : QuadraticForm A M) [inst_9 : IsScalarTower R A M]
--   [inst_10 : IsScalarTower S A M], SMulCommClass R S (CliffordAlgebra Q)

-- Source: PhysLean (Lorentz.contrCoUnit_symm)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcounit_symm : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.contrCoUnit.hom) 1)
--   (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo).V
--         (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--       (Action.instMonoidalCategory.whiskerLeft Lorentz.complexContr (Action.instCategory.id Lorentz.complexCo)).hom)
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr).V
--           (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--         ((Action.instBraidedCategory (ModuleCat Complex) (Matrix.SpecialLinearGroup (Fin 2) Complex)).braiding
--               Lorentz.complexCo Lorentz.complexContr).hom.hom)
--       (((fun X Y => LinearMap.instFunLike)
--             (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--             (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr).V).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.coContrUnit.hom) 1)))

-- Source: PhysLean (Lorentz.contrContrContractField.basis_left)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_basis_left : ∀ {d : Nat} {v : (Lorentz.Contr d).V.carrier} (μ : Sum (Fin 1) (Fin d)),
--   Eq
--     (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--       (TensorProduct.tmul Real (Module.Basis.instFunLike.coe Lorentz.ContrMod.stdBasis μ) v))
--     (instHMul.hMul (minkowskiMatrix μ μ) (Lorentz.ContrMod.toFin1dℝ v μ))

-- Source: PhysLean (CliffordAlgebra.adjoin_range_ι)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_adjoin_range_ι : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   {Q : QuadraticForm R M},
--   Eq (Algebra.adjoin R (Set.range (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q))))
--     Algebra.instCompleteLatticeSubalgebra.top

-- Source: PhysLean (LorentzGroup.generalizedBoost_apply_snd)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_generalizedboost_apply_snd : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem),
--   Eq (instHSMul.hSMul (LorentzGroup.generalizedBoost u v) v.val)
--     (instHSub.hSub
--       (instHSMul.hSMul
--         (instHMul.hMul 2
--           (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct u.val)
--             v.val))
--         v.val)
--       u.val)

-- Source: PhysLean (LorentzGroup.boost_zero_inl_0_inr_succ)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_zero_inl_0_inr_succ : ∀ {d : Nat} {β : Real} (hβ : Real.instLT.lt (abs β) 1) (i : Fin d),
--   Eq ((LorentzGroup.boost 0 β hβ).val (Sum.inl 0) (Sum.inr i.succ)) 0

-- Source: PhysLean (Lorentz.Vector.spaceLike_iff_norm_sq_neg)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_spacelike_iff_norm_sq_neg : ∀ {d : Nat} (p : Lorentz.Vector d),
--   Iff (Eq p.causalCharacter Lorentz.Vector.CausalCharacter.spaceLike)
--     (Real.instLT.lt
--       (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct p) p) 0)

-- Source: PhysLean (Lorentz.CoMod.stdBasis.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_stdbasis_eq_1 : ∀ {d : Nat}, Eq Lorentz.CoMod.stdBasis (Module.Basis.ofEquivFun Lorentz.CoMod.toFin1dℝEquiv)

-- Source: PhysLean (LorentzGroup.γ_sq)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_γ_sq : ∀ (β : Real),
--   Real.instLT.lt (abs β) 1 →
--     Eq (instHPow.hPow (LorentzGroup.γ β) 2) (instHDiv.hDiv 1 (instHSub.hSub 1 (instHPow.hPow β 2)))

-- Source: PhysLean (complexLorentzTensor.termεR)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_termεr : Lean.ParserDescr

-- Source: PhysLean (complexLorentzTensor.altLeftMetric_eq_altLeftBasis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altleftmetric_eq_altleftbasis : Eq complexLorentzTensor.altLeftMetric
--   (instHSub.hSub
--     (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altLeftBasis 0)
--         (Module.Basis.instFunLike.coe Fermion.altLeftBasis 1)))
--     (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altLeftBasis 1)
--         (Module.Basis.instFunLike.coe Fermion.altLeftBasis 0))))

-- Source: PhysLean (Lorentz.CoVector.apply_add)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_apply_add : ∀ {d : Nat} (v w : Lorentz.CoVector d) (i : Sum (Fin 1) (Fin d)), Eq (instHAdd.hAdd v w i) (instHAdd.hAdd (v i) (w i))

-- Source: PhysLean (SpaceTime.time.eq_1)
-- [complex signature, not re-axiomatized]
-- spacetime_time_eq_1 : ∀ {d : Nat} (c : SpeedOfLight),
--   Eq (SpaceTime.time c)
--     { toFun := fun x => { val := instHDiv.hDiv (Lorentz.Vector.timeComponent x) c.val }, map_add' := ⋯, map_smul' := ⋯ }

-- Source: PhysLean (Lorentz.ContrMod.val_smul)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_val_smul : ∀ {d : Nat} (r : Real) (ψ : Lorentz.ContrMod d), Eq (instHSMul.hSMul r ψ).val (instHSMul.hSMul r ψ.val)

-- Source: PhysLean (complexLorentzTensor.basis_upL_eq)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_basis_upl_eq : ∀ {i : Fin 2},
--   Eq (Module.Basis.instFunLike.coe (complexLorentzTensor.basis complexLorentzTensor.Color.upL) i)
--     (Module.Basis.instFunLike.coe Fermion.leftBasis i)

-- Source: PhysLean (Lorentz.contrCoContraction_basis')
-- [complex signature, not re-axiomatized]
-- lorentz_contrcocontraction_basis' : ∀ (i j : Sum (Fin 1) (Fin 3)),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.contrCoContraction.hom)
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasis i)
--         (Module.Basis.instFunLike.coe Lorentz.complexCoBasis j)))
--     (ite (Eq i j) 1 0)

-- Source: PhysLean (LorentzGroup.IsProper)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_isproper : {d : Nat} → (LorentzGroup d).Elem → Prop

-- Source: PhysLean (minkowskiMatrix.mul_η_diag_eq_iff)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_mul_η_diag_eq_iff : ∀ {d : Nat} {μ : Sum (Fin 1) (Fin d)} {x y : Real},
--   Iff (Eq (instHMul.hMul (minkowskiMatrix μ μ) x) (instHMul.hMul (minkowskiMatrix μ μ) y)) (Eq x y)

-- Source: PhysLean (Lorentz.Velocity.norm_spatialPart_sq_eq)
-- [complex signature, not re-axiomatized]
-- lorentz_velocity_norm_spatialpart_sq_eq : ∀ {d : Nat} (v : (Lorentz.Velocity d).Elem),
--   Eq (instHPow.hPow ((PiLp.instNorm 2 fun x => Real).norm v.val.spatialPart) 2)
--     (instHSub.hSub (instHPow.hPow (v.val (Sum.inl 0)) 2) 1)

-- Source: PhysLean (Lorentz.Vector.spatialPart_basis_sum_inr)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_spatialpart_basis_sum_inr : ∀ {d : Nat} (i j : Fin d),
--   Eq ((Module.Basis.instFunLike.coe Lorentz.Vector.basis (Sum.inr i)).spatialPart.ofLp j)
--     (Finsupp.instFunLike.coe (Finsupp.single (Sum.inr i) 1) (Sum.inr j))

-- Source: PhysLean (complexLorentzTensor.Color.downR.elim)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_color_downr_elim : {motive : complexLorentzTensor.Color → Sort u} →
--   (t : complexLorentzTensor.Color) → Eq t.ctorIdx 3 → motive complexLorentzTensor.Color.downR → motive t

-- Source: PhysLean (Lorentz.Velocity.minkowskiProduct_self_eq_one)
-- [complex signature, not re-axiomatized]
-- lorentz_velocity_minkowskiproduct_self_eq_one : ∀ {d : Nat} (v : (Lorentz.Velocity d).Elem),
--   Eq (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct v.val) v.val) 1

-- Source: PhysLean (LorentzGroup.instNegElemMatrixSumFinOfNatNatReal)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_instnegelemmatrixsumfinofnatnatreal : {d : Nat} → Neg (LorentzGroup d).Elem

-- Source: PhysLean (Lorentz.complexContrBasis.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcontrbasis_eq_1 : Eq Lorentz.complexContrBasis (Module.Basis.ofEquivFun Lorentz.ContrℂModule.toFin13ℂEquiv)

-- Source: PhysLean (realLorentzTensor.contrMetric)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_contrmetric : (d : optParam Nat 3) →
--   (realLorentzTensor d).Tensor
--     (Matrix.vecCons realLorentzTensor.Color.up (Matrix.vecCons realLorentzTensor.Color.up Matrix.vecEmpty))

-- Source: PhysLean (minkowskiMatrix.dual_mul)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_dual_mul : ∀ {d : Nat} (Λ Λ' : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real),
--   Eq (minkowskiMatrix.dual (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul Λ Λ'))
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (minkowskiMatrix.dual Λ') (minkowskiMatrix.dual Λ))

-- Source: PhysLean (Lorentz.contrCoToMatrixRe_symm_expand_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcotomatrixre_symm_expand_tmul : ∀ {d : Nat} (M : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real),
--   Eq (EquivLike.toFunLike.coe Lorentz.contrCoToMatrixRe.symm M)
--     (Finset.univ.sum fun i =>
--       Finset.univ.sum fun j =>
--         instHSMul.hSMul (M i j)
--           (TensorProduct.tmul Real (Module.Basis.instFunLike.coe (Lorentz.contrBasis d) i)
--             (Module.Basis.instFunLike.coe (Lorentz.coBasis d) j)))

-- Source: PhysLean (Lorentz.Vector.lightlike_spatial_parallel_implies_proportional)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_lightlike_spatial_parallel_implies_proportional : ∀ {d : Nat} {v w : Lorentz.Vector d},
--   Eq v.causalCharacter Lorentz.Vector.CausalCharacter.lightLike →
--     Eq w.causalCharacter Lorentz.Vector.CausalCharacter.lightLike →
--       (Exists fun r => Eq v (instHSMul.hSMul r w)) →
--         Exists fun r => Eq (abs (v (Sum.inl 0))) (instHMul.hMul (abs r) (abs (w (Sum.inl 0))))

-- Source: PhysLean (LorentzGroup.det_of_joined)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_det_of_joined : ∀ {d : Nat} {Λ Λ' : (LorentzGroup d).Elem}, Joined Λ Λ' → Eq Λ.val.det Λ'.val.det

-- Source: PhysLean (LorentzGroup.generalizedBoost_apply_eq_minkowskiProduct)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_generalizedboost_apply_eq_minkowskiproduct : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem) (μ ν : Sum (Fin 1) (Fin d)),
--   Eq ((LorentzGroup.generalizedBoost u v).val μ ν)
--     (instHMul.hMul (minkowskiMatrix μ μ)
--       (instHSub.hSub
--         (instHAdd.hAdd
--           (ContinuousLinearMap.funLike.coe
--             (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct
--               (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ))
--             (Module.Basis.instFunLike.coe Lorentz.Vector.basis ν))
--           (instHMul.hMul
--             (instHMul.hMul 2
--               (ContinuousLinearMap.funLike.coe
--                 (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct
--                   (Module.Basis.instFunLike.coe Lorentz.Vector.basis ν))
--                 u.val))
--             (ContinuousLinearMap.funLike.coe
--               (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct
--                 (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ))
--               v.val)))
--         (instHDiv.hDiv
--           (instHMul.hMul
--             (ContinuousLinearMap.funLike.coe
--               (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct
--                 (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ))
--               (instHAdd.hAdd u.val v.val))
--             (ContinuousLinearMap.funLike.coe
--               (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct
--                 (Module.Basis.instFunLike.coe Lorentz.Vector.basis ν))
--               (instHAdd.hAdd u.val v.val)))
--           (instHAdd.hAdd 1
--             (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct u.val)
--               v.val)))))

-- Source: PhysLean (complexLorentzTensor.permT_ofRat)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_permt_ofrat : ∀ {n m : Nat} {c : Fin n → complexLorentzTensor.Color} {c1 : Fin m → complexLorentzTensor.Color} {σ : Fin m → Fin n}
--   (h : TensorSpecies.Tensor.PermCond c c1 σ) (f : TensorSpecies.Tensor.ComponentIdx c → RatComplexNum),
--   Eq
--     (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT σ h)
--       (LinearMap.instFunLike.coe complexLorentzTensor.ofRat f))
--     (LinearMap.instFunLike.coe complexLorentzTensor.ofRat fun b =>
--       f fun i => Fin.cast ⋯ (b (TensorSpecies.Tensor.PermCond.inv σ h i)))

-- Source: PhysLean (Lorentz.SL2C.toLorentzGroup_fst_col)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_tolorentzgroup_fst_col : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (fun μ => (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M).val μ (Sum.inl 0)) fun μ =>
--     Lorentz.SL2C.toLorentzGroup_fst_col.match_1 (fun μ => Real) μ
--       (fun _ =>
--         instHDiv.hDiv
--           (instHAdd.hAdd
--             (instHAdd.hAdd
--               (instHAdd.hAdd (instHPow.hPow (Complex.instNorm.norm (M.val 0 0)) 2)
--                 (instHPow.hPow (Complex.instNorm.norm (M.val 0 1)) 2))
--               (instHPow.hPow (Complex.instNorm.norm (M.val 1 0)) 2))
--             (instHPow.hPow (Complex.instNorm.norm (M.val 1 1)) 2))
--           2)
--       (fun _ =>
--         Real.instNeg.neg
--           (instHAdd.hAdd
--             (instHAdd.hAdd
--               (instHAdd.hAdd (instHMul.hMul (M.val 0 1).re (M.val 1 1).re)
--                 (instHMul.hMul (M.val 0 1).im (M.val 1 1).im))
--               (instHMul.hMul (M.val 0 0).im (M.val 1 0).im))
--             (instHMul.hMul (M.val 0 0).re (M.val 1 0).re)))
--       (fun _ =>
--         instHAdd.hAdd
--           (instHSub.hSub
--             (instHAdd.hAdd (instHMul.hMul (Real.instNeg.neg (M.val 0 0).re) (M.val 1 0).im)
--               (instHMul.hMul (M.val 1 0).re (M.val 0 0).im))
--             (instHMul.hMul (M.val 0 1).re (M.val 1 1).im))
--           (instHMul.hMul (M.val 0 1).im (M.val 1 1).re))
--       fun _ =>
--       instHDiv.hDiv
--         (instHAdd.hAdd
--           (instHAdd.hAdd
--             (instHSub.hSub (Real.instNeg.neg (instHPow.hPow (Complex.instNorm.norm (M.val 0 0)) 2))
--               (instHPow.hPow (Complex.instNorm.norm (M.val 0 1)) 2))
--             (instHPow.hPow (Complex.instNorm.norm (M.val 1 0)) 2))
--           (instHPow.hPow (Complex.instNorm.norm (M.val 1 1)) 2))
--         2

-- Source: PhysLean (complexLorentzTensor.Color.up.sizeOf_spec)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_color_up_sizeof_spec : Eq (complexLorentzTensor.Color._sizeOf_inst.sizeOf complexLorentzTensor.Color.up) 1

-- Source: PhysLean (SpaceTime.boost_x_smul)
-- [complex signature, not re-axiomatized]
-- spacetime_boost_x_smul : ∀ (β : Real) (hβ : Real.instLT.lt (abs β) 1) (x : SpaceTime),
--   Eq (instHSMul.hSMul (LorentzGroup.boost 0 β hβ) x) fun x_1 =>
--     SpaceTime.boost_x_smul.match_1 (fun x => Real) x_1
--       (fun _ => instHMul.hMul (LorentzGroup.γ β) (instHSub.hSub (x (Sum.inl 0)) (instHMul.hMul β (x (Sum.inr 0)))))
--       (fun _ => instHMul.hMul (LorentzGroup.γ β) (instHSub.hSub (x (Sum.inr 0)) (instHMul.hMul β (x (Sum.inl 0)))))
--       (fun _ => x (Sum.inr 1)) fun _ => x (Sum.inr 2)

-- Source: PhysLean (Lorentz.complexCoBasis.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcobasis_eq_1 : Eq Lorentz.complexCoBasis (Module.Basis.ofEquivFun Lorentz.CoℂModule.toFin13ℂEquiv)

-- Source: PhysLean (complexLorentzTensor.termδL')
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_termδl' : Lean.ParserDescr

-- Source: PhysLean (Lorentz.CoVector.smul_neg)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_smul_neg : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem) (p : Lorentz.CoVector d),
--   Eq (instHSMul.hSMul Λ (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg p))
--     (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg (instHSMul.hSMul Λ p))

-- Source: PhysLean (LorentzGroup.boost_zero_eq_id)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_zero_eq_id : ∀ {d : Nat} (i : Fin d), Eq (LorentzGroup.boost i 0 ⋯) 1

-- Source: PhysLean (LorentzGroup.isOrthochronous_inv_iff)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_isorthochronous_inv_iff : ∀ {d : Nat} {Λ : (LorentzGroup d).Elem},
--   Iff (LorentzGroup.IsOrthochronous (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ))
--     (LorentzGroup.IsOrthochronous Λ)

-- Source: PhysLean (complexLorentzTensor.contrMetric_eq_complexContrBasisFin4)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrmetric_eq_complexcontrbasisfin4 : Eq complexLorentzTensor.contrMetric
--   (instHSub.hSub
--     (instHSub.hSub
--       (instHSub.hSub
--         (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasisFin4 0)
--             (Module.Basis.instFunLike.coe Lorentz.complexContrBasisFin4 0)))
--         (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasisFin4 1)
--             (Module.Basis.instFunLike.coe Lorentz.complexContrBasisFin4 1))))
--       (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--         (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasisFin4 2)
--           (Module.Basis.instFunLike.coe Lorentz.complexContrBasisFin4 2))))
--     (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasisFin4 3)
--         (Module.Basis.instFunLike.coe Lorentz.complexContrBasisFin4 3))))

-- Source: PhysLean (Lorentz.contrBasis)
-- [complex signature, not re-axiomatized]
-- lorentz_contrbasis : (d : optParam Nat 3) → Module.Basis (Sum (Fin 1) (Fin d)) Real (Lorentz.Contr d).V.carrier

-- Source: PhysLean (CliffordAlgebra.comp_ι_sq_scalar)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_comp_ι_sq_scalar : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   {Q : QuadraticForm R M} {A : Type u_3} [inst_3 : Semiring A] [inst_4 : Algebra R A]
--   (g : AlgHom R (CliffordAlgebra Q) A) (m : M),
--   Eq
--     (instHMul.hMul (AlgHom.funLike.coe g (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) m))
--       (AlgHom.funLike.coe g (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) m)))
--     (RingHom.instFunLike.coe (algebraMap R A) (QuadraticMap.instFunLike.coe Q m))

-- Source: PhysLean (LorentzGroup.toProd_embedding)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_toprod_embedding : ∀ {d : Nat}, Topology.IsEmbedding (MonoidHom.instFunLike.coe LorentzGroup.toProd)

-- Source: PhysLean (minkowskiMatrix.η_apply_mul_η_apply_diag)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_η_apply_mul_η_apply_diag : ∀ {d : Nat} (μ : Sum (Fin 1) (Fin d)), Eq (instHMul.hMul (minkowskiMatrix μ μ) (minkowskiMatrix μ μ)) 1

-- Source: PhysLean (Lorentz.Vector.actionCLM_injective)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_actionclm_injective : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Function.Injective (ContinuousLinearMap.funLike.coe (Lorentz.Vector.actionCLM Λ))

-- Source: PhysLean (LorentzGroup.generalizedBoost_self)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_generalizedboost_self : ∀ {d : Nat} (u : (Lorentz.Velocity d).Elem), Eq (LorentzGroup.generalizedBoost u u) 1

-- Source: PhysLean (Lorentz.complexContrBasis_ρ_val)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcontrbasis_ρ_val : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex) (v : Lorentz.complexContr.V.carrier),
--   Eq (LinearMap.instFunLike.coe (MonoidHom.instFunLike.coe Lorentz.complexContr.ρ M) v).val
--     ((MonoidHom.instFunLike.coe LorentzGroup.toComplex (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M)).mulVec
--       v.val)

-- Source: PhysLean (realLorentzTensor.coMetric)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_cometric : (d : optParam Nat 3) →
--   (realLorentzTensor d).Tensor
--     (Matrix.vecCons realLorentzTensor.Color.down (Matrix.vecCons realLorentzTensor.Color.down Matrix.vecEmpty))

-- Source: PhysLean (Lorentz.Vector.causalDiamond)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causaldiamond : {d : Nat} → Lorentz.Vector d → Lorentz.Vector d → Set (Lorentz.Vector d)

-- Source: PhysLean (LorentzGroup.toVector_mul)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_tovector_mul : ∀ {d : Nat} (Λ₁ Λ₂ : (LorentzGroup d).Elem),
--   Eq (LorentzGroup.toVector (instHMul.hMul Λ₁ Λ₂)) (instHSMul.hSMul Λ₁ (LorentzGroup.toVector Λ₂))

-- Source: PhysLean (Lorentz.Vector.temporalCLM_apply_eq_timeComponent)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_temporalclm_apply_eq_timecomponent : ∀ {d : Nat} (v : Lorentz.Vector d),
--   Eq (ContinuousLinearMap.funLike.coe (Lorentz.Vector.temporalCLM d) v) v.timeComponent

-- Source: PhysLean (Lorentz.coMetricVal.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_cometricval_eq_1 : Eq Lorentz.coMetricVal
--   (EquivLike.toFunLike.coe Lorentz.coCoToMatrix.symm (minkowskiMatrix.map (RingHom.instFunLike.coe Complex.ofRealHom)))

-- Source: PhysLean (complexLorentzTensor.«termℂT(_)»)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_«termℂt(_)» : Lean.ParserDescr

-- Source: PhysLean (Lorentz.coContrToMatrixRe.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrtomatrixre_eq_1 : ∀ {d : Nat},
--   Eq Lorentz.coContrToMatrixRe
--     ((((Lorentz.coBasis d).tensorProduct (Lorentz.contrBasis d)).repr.trans
--           (Finsupp.linearEquivFunOnFinite Real Real (Prod (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d))))).trans
--       (LinearEquiv.curry Real Real (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d))))

-- Source: PhysLean (SpaceTime.instSMulElemMatrixSumFinOfNatNatRealLorentzGroupDistribution.congr_simp)
-- [complex signature, not re-axiomatized]
-- spacetime_instsmulelemmatrixsumfinofnatnatreallorentzgroupdistribution_congr_simp : ∀ {n d : Nat} {c : Fin n → realLorentzTensor.Color} {M : Type} [inst : NormedAddCommGroup M]
--   [inst_1 : NormedSpace Real M] [inst_2 : (realLorentzTensor d).Tensorial c M] [inst_3 : T2Space M],
--   Eq SpaceTime.instSMulElemMatrixSumFinOfNatNatRealLorentzGroupDistribution
--     SpaceTime.instSMulElemMatrixSumFinOfNatNatRealLorentzGroupDistribution

-- Source: PhysLean (complexLorentzTensor.altRightRightUnit_eq_basis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altrightrightunit_eq_basis : Eq complexLorentzTensor.altRightRightUnit
--   (Finset.univ.sum fun i =>
--     Module.Basis.instFunLike.coe
--       (TensorSpecies.Tensor.basis
--         (Matrix.vecCons complexLorentzTensor.Color.downR
--           (Matrix.vecCons complexLorentzTensor.Color.upR Matrix.vecEmpty)))
--       fun x =>
--       complexLorentzTensor.coContrUnit_eq_basis.match_1
--         (fun x =>
--           Fin
--             (complexLorentzTensor.repDim
--               (Matrix.vecCons complexLorentzTensor.Color.downR
--                 (Matrix.vecCons complexLorentzTensor.Color.upR Matrix.vecEmpty) x)))
--         x (fun _ => i) fun _ => i)

-- Source: PhysLean (SpaceTime.deriv_equivariant)
-- [complex signature, not re-axiomatized]
-- spacetime_deriv_equivariant : ∀ {n d : Nat} {c : Fin n → realLorentzTensor.Color} {M : Type} [inst : NormedAddCommGroup M]
--   [inst_1 : NormedSpace Real M] [inst_2 : (realLorentzTensor d).Tensorial c M] [T2Space M] (f : SpaceTime d → M)
--   (Λ : (LorentzGroup d).Elem) (x : SpaceTime d),
--   Differentiable Real f →
--     ∀ (μ : Sum (Fin 1) (Fin d)),
--       Eq
--         (SpaceTime.deriv μ
--           (fun x => instHSMul.hSMul Λ (f (instHSMul.hSMul (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ) x))) x)
--         (Finset.univ.sum fun ν =>
--           instHSMul.hSMul ((DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ).val ν μ)
--             (instHSMul.hSMul Λ
--               (SpaceTime.deriv ν f (instHSMul.hSMul (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ) x))))

-- Source: PhysLean (Lorentz.Vector.minkowskiProduct_basis_left)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproduct_basis_left : ∀ {d : Nat} (μ : Sum (Fin 1) (Fin d)) (p : Lorentz.Vector d),
--   Eq
--     (ContinuousLinearMap.funLike.coe
--       (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct
--         (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ))
--       p)
--     (instHMul.hMul (minkowskiMatrix μ μ) (p μ))

-- Source: PhysLean (Lorentz.coCoToMatrixRe_ρ_symm)
-- [complex signature, not re-axiomatized]
-- lorentz_cocotomatrixre_ρ_symm : ∀ {d : Nat} (v : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real) (M : (LorentzGroup d).Elem),
--   Eq
--     (LinearMap.instFunLike.coe
--       (TensorProduct.map (MonoidHom.instFunLike.coe (Lorentz.Co d).ρ M) (MonoidHom.instFunLike.coe (Lorentz.Co d).ρ M))
--       (EquivLike.toFunLike.coe Lorentz.coCoToMatrixRe.symm v))
--     (EquivLike.toFunLike.coe Lorentz.coCoToMatrixRe.symm
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--         (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.inv.inv M.val).transpose v) (Matrix.inv.inv M.val)))

-- Source: PhysLean (Lorentz.CoMod.stdBasis_toFin1dℝEquiv_apply_ne)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_stdbasis_tofin1dℝequiv_apply_ne : ∀ {d : Nat} {μ ν : Sum (Fin 1) (Fin d)},
--   Ne μ ν →
--     Eq (EquivLike.toFunLike.coe Lorentz.CoMod.toFin1dℝEquiv (Module.Basis.instFunLike.coe Lorentz.CoMod.stdBasis μ) ν) 0

-- Source: PhysLean (Lorentz.contrCoContract_tmul_symm)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcocontract_tmul_symm : ∀ {d : Nat} (φ : (Lorentz.Contr d).V.carrier) (ψ : (Lorentz.Co d).V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom Lorentz.contrCoContract.hom)
--       (TensorProduct.tmul Real φ ψ))
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom Lorentz.coContrContract.hom)
--       (TensorProduct.tmul Real ψ φ))

-- Source: PhysLean (complexLorentzTensor.rightMetric_eq_basis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_rightmetric_eq_basis : Eq complexLorentzTensor.rightMetric
--   (instHAdd.hAdd
--     (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg
--       (Module.Basis.instFunLike.coe
--         (TensorSpecies.Tensor.basis
--           (Matrix.vecCons complexLorentzTensor.Color.upR
--             (Matrix.vecCons complexLorentzTensor.Color.upR Matrix.vecEmpty)))
--         fun x =>
--         complexLorentzTensor.coMetric_eq_basis.match_1
--           (fun x =>
--             Fin
--               (complexLorentzTensor.repDim
--                 (Matrix.vecCons complexLorentzTensor.Color.upR
--                   (Matrix.vecCons complexLorentzTensor.Color.upR Matrix.vecEmpty) x)))
--           x (fun _ => 0) fun _ => 1))
--     (Module.Basis.instFunLike.coe
--       (TensorSpecies.Tensor.basis
--         (Matrix.vecCons complexLorentzTensor.Color.upR (Matrix.vecCons complexLorentzTensor.Color.upR Matrix.vecEmpty)))
--       fun x =>
--       complexLorentzTensor.coMetric_eq_basis.match_1
--         (fun x =>
--           Fin
--             (complexLorentzTensor.repDim
--               (Matrix.vecCons complexLorentzTensor.Color.upR
--                 (Matrix.vecCons complexLorentzTensor.Color.upR Matrix.vecEmpty) x)))
--         x (fun _ => 1) fun _ => 0))

-- Source: PhysLean (LorentzGroup.one_mem)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_one_mem : ∀ {d : Nat}, Set.instMembership.mem (LorentzGroup d) 1

-- Source: PhysLean (realLorentzTensor.termη')
-- [complex signature, not re-axiomatized]
-- reallorentztensor_termη' : Lean.ParserDescr

-- Source: PhysLean (complexLorentzTensor.«_aux_PhysLean_Relativity_Tensors_ComplexTensor_Basic___macroRules_complexLorentzTensor_termℂT(_)_1»)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_«_aux_physlean_relativity_tensors_complextensor_basic___macrorules_complexlorentztensor_termℂt(_)_1» : Lean.Macro

-- Source: PhysLean (Lorentz.Vector.minkowskiProduct_toCoord)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproduct_tocoord : ∀ {d : Nat} (p q : Lorentz.Vector d),
--   Eq (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct p) q)
--     (instHSub.hSub (instHMul.hMul (p (Sum.inl 0)) (q (Sum.inl 0)))
--       (Finset.univ.sum fun i => instHMul.hMul (p (Sum.inr i)) (q (Sum.inr i))))

-- Source: PhysLean (SpaceTime.properTime.eq_1)
-- [complex signature, not re-axiomatized]
-- spacetime_propertime_eq_1 : ∀ {d : Nat} (q p : SpaceTime d),
--   Eq (q.properTime p)
--     (ContinuousLinearMap.funLike.coe
--         (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct (instHSub.hSub p q)) (instHSub.hSub p q)).sqrt

-- Source: PhysLean (SpaceTime.spaceTime_integrable_iff_space_time_integrable)
-- [complex signature, not re-axiomatized]
-- spacetime_spacetime_integrable_iff_space_time_integrable : ∀ {M : Type u_1} [inst : NormedAddCommGroup M] {d : Nat} (c : SpeedOfLight) (f : SpaceTime d → M),
--   Iff (MeasureTheory.Integrable f SpaceTime.instMeasureSpace.volume)
--     (MeasureTheory.Integrable (Function.comp f (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c).symm))
--       (measureSpaceOfInnerProductSpace.volume.prod measureSpaceOfInnerProductSpace.volume))

-- Source: PhysLean (realLorentzTensor.«_aux_PhysLean_Relativity_Tensors_RealTensor_Basic___macroRules_realLorentzTensor_termℝT(_,_)_1»)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_«_aux_physlean_relativity_tensors_realtensor_basic___macrorules_reallorentztensor_termℝt(_,_)_1» : Lean.Macro

-- Source: PhysLean (Lorentz.ContrMod.stdBasis_toFin1dℝEquiv_apply_ne)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_stdbasis_tofin1dℝequiv_apply_ne : ∀ {d : Nat} {μ ν : Sum (Fin 1) (Fin d)},
--   Ne μ ν →
--     Eq
--       (EquivLike.toFunLike.coe Lorentz.ContrMod.toFin1dℝEquiv (Module.Basis.instFunLike.coe Lorentz.ContrMod.stdBasis μ)
--         ν)
--       0

-- Source: PhysLean (realLorentzTensor.coMetric_repr_apply_eq_minkowskiMatrix)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_cometric_repr_apply_eq_minkowskimatrix : ∀ {d : Nat}
--   (b :
--     TensorSpecies.Tensor.ComponentIdx
--       (Matrix.vecCons realLorentzTensor.Color.down (Matrix.vecCons realLorentzTensor.Color.down Matrix.vecEmpty))),
--   Eq
--     (Finsupp.instFunLike.coe
--       (EquivLike.toFunLike.coe
--         (TensorSpecies.Tensor.basis
--             (Matrix.vecCons realLorentzTensor.Color.down
--               (Matrix.vecCons realLorentzTensor.Color.down Matrix.vecEmpty))).repr
--         (realLorentzTensor.coMetric d))
--       b)
--     (minkowskiMatrix (EquivLike.toFunLike.coe finSumFinEquiv.symm (b 0))
--       (EquivLike.toFunLike.coe finSumFinEquiv.symm (b 1)))

-- Source: PhysLean (Lorentz.coCoToMatrixRe_ρ)
-- [complex signature, not re-axiomatized]
-- lorentz_cocotomatrixre_ρ : ∀ {d : Nat} (v : (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Co d)).V.carrier)
--   (M : (LorentzGroup d).Elem),
--   Eq
--     (EquivLike.toFunLike.coe Lorentz.coCoToMatrixRe
--       (LinearMap.instFunLike.coe
--         (TensorProduct.map (MonoidHom.instFunLike.coe (Lorentz.Co d).ρ M)
--           (MonoidHom.instFunLike.coe (Lorentz.Co d).ρ M))
--         v))
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.inv.inv M.val).transpose
--         (EquivLike.toFunLike.coe Lorentz.coCoToMatrixRe v))
--       (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv M).val)

-- Source: PhysLean (LorentzGroup.toVector_apply)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_tovector_apply : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem) (i : Sum (Fin 1) (Fin d)), Eq (LorentzGroup.toVector Λ i) (Λ.val i (Sum.inl 0))

-- Source: PhysLean (Lorentz.complexCoBasisFin4_apply_zero)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcobasisfin4_apply_zero : Eq (Module.Basis.instFunLike.coe Lorentz.complexCoBasisFin4 0)
--   (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inl 0))

-- Source: PhysLean (Lorentz.CoVector.toTensor_symm_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_totensor_symm_apply : ∀ {d : Nat} (p : (realLorentzTensor d).Tensor (Matrix.vecCons realLorentzTensor.Color.down Matrix.vecEmpty)),
--   Eq (EquivLike.toFunLike.coe Lorentz.CoVector.tensorial.toTensor.symm p)
--     (EquivLike.toFunLike.coe (Equiv.piCongrLeft' (fun a => Real) Lorentz.CoVector.indexEquiv)
--       (EquivLike.toFunLike.coe Finsupp.equivFunOnFinite
--         (EquivLike.toFunLike.coe
--           (TensorSpecies.Tensor.basis (Matrix.vecCons realLorentzTensor.Color.down Matrix.vecEmpty)).repr p)))

-- Source: PhysLean (Lorentz.CoVector.zero_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_zero_apply : ∀ {d : Nat} (i : Sum (Fin 1) (Fin d)), Eq (0 i) 0

-- Source: PhysLean (Lorentz.ContrℂModule.val_smul)
-- [complex signature, not re-axiomatized]
-- lorentz_contrℂmodule_val_smul : ∀ (r : Complex) (ψ : Lorentz.ContrℂModule), Eq (instHSMul.hSMul r ψ).val (instHSMul.hSMul r ψ.val)

-- Source: PhysLean (Lorentz.Vector.minkowskiProduct_map_eq_adjoint)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproduct_map_eq_adjoint : ∀ {d : Nat} (f : LinearMap (RingHom.id Real) (Lorentz.Vector d) (Lorentz.Vector d)) (p q : Lorentz.Vector d),
--   Eq
--     (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct p)
--       (LinearMap.instFunLike.coe f q))
--     (ContinuousLinearMap.funLike.coe
--       (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct
--         (LinearMap.instFunLike.coe (Lorentz.Vector.adjoint f) p))
--       q)

-- Source: PhysLean (Lorentz.coCoToMatrix_ρ_symm)
-- [complex signature, not re-axiomatized]
-- lorentz_cocotomatrix_ρ_symm : ∀ (v : Matrix (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3)) Complex) (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (LinearMap.instFunLike.coe
--       (TensorProduct.map (MonoidHom.instFunLike.coe Lorentz.complexCo.ρ M)
--         (MonoidHom.instFunLike.coe Lorentz.complexCo.ρ M))
--       (EquivLike.toFunLike.coe Lorentz.coCoToMatrix.symm v))
--     (EquivLike.toFunLike.coe Lorentz.coCoToMatrix.symm
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--         (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--           (Matrix.inv.inv
--               (MonoidHom.instFunLike.coe LorentzGroup.toComplex
--                 (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M))).transpose
--           v)
--         (Matrix.inv.inv
--           (MonoidHom.instFunLike.coe LorentzGroup.toComplex
--             (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M)))))

-- Source: PhysLean (Lorentz.contrContrContractField.dual_mulVec_left)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_dual_mulvec_left : ∀ {d : Nat} (x y : (Lorentz.Contr d).V.carrier) {Λ : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real},
--   Eq
--     (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--       (TensorProduct.tmul Real (Lorentz.ContrMod.mulVec (minkowskiMatrix.dual Λ) x) y))
--     (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--       (TensorProduct.tmul Real x (Lorentz.ContrMod.mulVec Λ y)))

-- Source: PhysLean (LorentzGroup.id_joined_generalizedBoost)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_id_joined_generalizedboost : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem), Joined 1 (LorentzGroup.generalizedBoost u v)

-- Source: PhysLean (Lorentz.CoℂModule.instAddCommMonoid)
-- [complex signature, not re-axiomatized]
-- lorentz_coℂmodule_instaddcommmonoid : AddCommMonoid Lorentz.CoℂModule

-- Source: PhysLean (Lorentz.Vector.actionCLM_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_actionclm_apply : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem) (p : Lorentz.Vector d),
--   Eq (ContinuousLinearMap.funLike.coe (Lorentz.Vector.actionCLM Λ) p) (instHSMul.hSMul Λ p)

-- Source: PhysLean (Lorentz.contrContrContractField.ge_sub_norm)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_ge_sub_norm : ∀ {d : Nat} (v w : (Lorentz.Contr d).V.carrier),
--   Real.instLE.le
--     (instHSub.hSub (instHMul.hMul (v.val (Sum.inl 0)) (w.val (Sum.inl 0)))
--       (instHMul.hMul ((PiLp.instNorm 2 fun x => Real).norm (Lorentz.ContrMod.toSpace v))
--         ((PiLp.instNorm 2 fun x => Real).norm (Lorentz.ContrMod.toSpace w))))
--     (LinearMap.instFunLike.coe Lorentz.contrContrContractField (TensorProduct.tmul Real v w))

-- Source: PhysLean (Lorentz.contrContrContract)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontract : {d : Nat} →
--   Action.instCategory.Hom (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Contr d))
--     (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem))

-- Source: PhysLean (LorentzGroup.IsProper.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_isproper_eq_1 : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem), Eq (LorentzGroup.IsProper Λ) (Eq Λ.val.det 1)

-- Source: PhysLean (Lorentz.CoℂModule.ctorIdx)
-- [complex signature, not re-axiomatized]
-- lorentz_coℂmodule_ctoridx : Lorentz.CoℂModule → Nat

-- Source: PhysLean (CliffordAlgebra.ι_range_map_map)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_ι_range_map_map : ∀ {R : Type u_1} [inst : CommRing R] {M₁ : Type u_4} {M₂ : Type u_5} [inst_1 : AddCommGroup M₁]
--   [inst_2 : AddCommGroup M₂] [inst_3 : Module R M₁] [inst_4 : Module R M₂] {Q₁ : QuadraticForm R M₁}
--   {Q₂ : QuadraticForm R M₂} (f : QuadraticMap.Isometry Q₁ Q₂),
--   Eq (Submodule.map (CliffordAlgebra.map f).toLinearMap (LinearMap.range (CliffordAlgebra.ι Q₁)))
--     (Submodule.map (CliffordAlgebra.ι Q₂) (LinearMap.range f))

-- Source: PhysLean (SpaceTime.distDeriv_inl_distTimeSlice_symm)
-- [complex signature, not re-axiomatized]
-- spacetime_distderiv_inl_disttimeslice_symm : ∀ {M : Type} {d : Nat} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] {c : SpeedOfLight}
--   (f : Distribution Real (Prod Time (Space d)) M),
--   Eq
--     (LinearMap.instFunLike.coe (SpaceTime.distDeriv (Sum.inl 0))
--       (EquivLike.toFunLike.coe (SpaceTime.distTimeSlice c).symm f))
--     (instHSMul.hSMul (instHDiv.hDiv 1 c.val)
--       (EquivLike.toFunLike.coe (SpaceTime.distTimeSlice c).symm (LinearMap.instFunLike.coe Space.distTimeDeriv f)))

-- Source: PhysLean (Lorentz.CoVector.smul_eq_sum)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_smul_eq_sum : ∀ {d : Nat} (i : Sum (Fin 1) (Fin d)) (Λ : (LorentzGroup d).Elem) (p : Lorentz.CoVector d),
--   Eq (instHSMul.hSMul Λ p i)
--     (Finset.univ.sum fun j => instHMul.hMul ((DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ).val j i) (p j))

-- Source: PhysLean (LorentzGroup.ofSpecialOrthogonal_continuous)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_ofspecialorthogonal_continuous : ∀ {d : Nat}, Continuous (EquivLike.toFunLike.coe LorentzGroup.ofSpecialOrthogonal)

-- Source: PhysLean (Lorentz.SL2C.toLorentzGroup)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_tolorentzgroup : MonoidHom (Matrix.SpecialLinearGroup (Fin 2) Complex) (LorentzGroup 3).Elem

-- Source: PhysLean (Lorentz.SL2C.toMatrix.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_tomatrix_eq_1 : Eq Lorentz.SL2C.toMatrix
--   {
--     toFun := fun M =>
--       EquivLike.toFunLike.coe (LinearMap.toMatrix PauliMatrix.pauliBasis' PauliMatrix.pauliBasis')
--         (Lorentz.SL2C.toSelfAdjointMap M),
--     map_one' := Lorentz.SL2C.toMatrix._proof_5, map_mul' := Lorentz.SL2C.toMatrix._proof_6 }

-- Source: PhysLean (complexLorentzTensor.altLeftMetric)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altleftmetric : complexLorentzTensor.Tensor
--   (Matrix.vecCons complexLorentzTensor.Color.downL (Matrix.vecCons complexLorentzTensor.Color.downL Matrix.vecEmpty))

-- Source: PhysLean (Lorentz.ContrMod.toFin1dℝEquiv_symm_isInducing)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_tofin1dℝequiv_symm_isinducing : ∀ {d : Nat}, Topology.IsInducing (EquivLike.toFunLike.coe Lorentz.ContrMod.toFin1dℝEquiv.symm)

-- Source: PhysLean (SpaceTime.space)
-- [complex signature, not re-axiomatized]
-- spacetime_space : {d : Nat} → ContinuousLinearMap (RingHom.id Real) (SpaceTime d) (Space d)

-- Source: PhysLean (Lorentz.contrContrContractField.action_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_action_tmul : ∀ {d : Nat} (x y : (Lorentz.Contr d).V.carrier) (g : (LorentzGroup d).Elem),
--   Eq
--     (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--       (TensorProduct.tmul Real (LinearMap.instFunLike.coe (MonoidHom.instFunLike.coe (Lorentz.Contr d).ρ g) x)
--         (LinearMap.instFunLike.coe (MonoidHom.instFunLike.coe (Lorentz.Contr d).ρ g) y)))
--     (LinearMap.instFunLike.coe Lorentz.contrContrContractField (TensorProduct.tmul Real x y))

-- Source: PhysLean (Lorentz.contrContrContractField.inl_sq_eq)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_inl_sq_eq : ∀ {d : Nat} (v : (Lorentz.Contr d).V.carrier),
--   Eq (instHPow.hPow (v.val (Sum.inl 0)) 2)
--     (instHAdd.hAdd (LinearMap.instFunLike.coe Lorentz.contrContrContractField (TensorProduct.tmul Real v v))
--       (Finset.univ.sum fun i => instHPow.hPow (v.val (Sum.inr i)) 2))

-- Source: PhysLean (Lorentz.Vector.minkowskiProductMap_add_fst)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproductmap_add_fst : ∀ {d : Nat} (p q r : Lorentz.Vector d),
--   Eq ((instHAdd.hAdd p q).minkowskiProductMap r) (instHAdd.hAdd (p.minkowskiProductMap r) (q.minkowskiProductMap r))

-- Source: PhysLean (SpaceTime.time_val_toCoord_symm)
-- [complex signature, not re-axiomatized]
-- spacetime_time_val_tocoord_symm : ∀ {d : Nat} (c : SpeedOfLight) (f : Sum (Fin 1) (Fin d) → Real),
--   Eq (LinearMap.instFunLike.coe (SpaceTime.time c) f).val (instHDiv.hDiv (f (Sum.inl 0)) c.val)

-- Source: PhysLean (Lorentz.SL2C.toSelfAdjointMap.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_toselfadjointmap_eq_1 : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (Lorentz.SL2C.toSelfAdjointMap M)
--     {
--       toFun := fun A =>
--         ⟨instHMul.hMul (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul M.val A.val) M.val.conjTranspose, ⋯⟩,
--       map_add' := ⋯, map_smul' := ⋯ }

-- Source: PhysLean (Lorentz.ContrℂModule.instAddCommMonoid)
-- [complex signature, not re-axiomatized]
-- lorentz_contrℂmodule_instaddcommmonoid : AddCommMonoid Lorentz.ContrℂModule

-- Source: PhysLean (Lorentz.CoVector.toTensor_basis_eq_tensor_basis)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_totensor_basis_eq_tensor_basis : ∀ {d : Nat} (μ : Sum (Fin 1) (Fin d)),
--   Eq
--     (EquivLike.toFunLike.coe Lorentz.CoVector.tensorial.toTensor
--       (Module.Basis.instFunLike.coe Lorentz.CoVector.basis μ))
--     (Module.Basis.instFunLike.coe
--       (TensorSpecies.Tensor.basis (Matrix.vecCons realLorentzTensor.Color.down Matrix.vecEmpty))
--       (EquivLike.toFunLike.coe Lorentz.CoVector.indexEquiv.symm μ))

-- Source: PhysLean (Lorentz.Velocity.zero_timeComponent)
-- [complex signature, not re-axiomatized]
-- lorentz_velocity_zero_timecomponent : ∀ {d : Nat}, Eq (Subtype.val 0).timeComponent 1

-- Source: PhysLean (LorentzGroup.isOrthochronous_iff_toVector_timeComponet_nonneg)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_isorthochronous_iff_tovector_timecomponet_nonneg : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Iff (LorentzGroup.IsOrthochronous Λ) (Real.instLE.le 0 (LorentzGroup.toVector Λ).timeComponent)

-- Source: PhysLean (Lorentz.CoVector)
-- [complex signature, not re-axiomatized]
-- lorentz_covector : optParam Nat 3 → Type

-- Source: PhysLean (SpaceTime.distActionLinearMap)
-- [complex signature, not re-axiomatized]
-- spacetime_distactionlinearmap : {n : Nat} →
--   {c : Fin n → realLorentzTensor.Color} →
--     {d : Nat} →
--       {M : Type} →
--         [inst : NormedAddCommGroup M] →
--           [inst_1 : NormedSpace Real M] →
--             [(realLorentzTensor d).Tensorial c M] →
--               [T2Space M] →
--                 (LorentzGroup d).Elem →
--                   LinearMap (RingHom.id Real) (Distribution Real (SpaceTime d) M) (Distribution Real (SpaceTime d) M)

-- Source: PhysLean (Lorentz.CoℂModule.instAddCommGroup)
-- [complex signature, not re-axiomatized]
-- lorentz_coℂmodule_instaddcommgroup : AddCommGroup Lorentz.CoℂModule

-- Source: PhysLean (SpaceTime.toTimeAndSpace_basis_inl')
-- [complex signature, not re-axiomatized]
-- spacetime_totimeandspace_basis_inl' : ∀ {d : Nat} {c : SpeedOfLight},
--   Eq
--     (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c)
--       (Module.Basis.instFunLike.coe Lorentz.Vector.basis (Sum.inl 0)))
--     (instHSMul.hSMul (instHDiv.hDiv 1 c.val) { fst := 1, snd := 0 })

-- Source: PhysLean (Lorentz.Vector.timelike_spatial_lt_time_squared)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_timelike_spatial_lt_time_squared : ∀ {d : Nat} {v : Lorentz.Vector d},
--   Eq v.causalCharacter Lorentz.Vector.CausalCharacter.timeLike →
--     Real.instLT.lt ((PiLp.innerProductSpace fun x => Real).inner Real v.spatialPart v.spatialPart)
--       (instHPow.hPow v.timeComponent 2)

-- Source: PhysLean (Lorentz.Vector.apply_sub)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_apply_sub : ∀ {d : Nat} (v w : Lorentz.Vector d) (i : Sum (Fin 1) (Fin d)), Eq (instHSub.hSub v w i) (instHSub.hSub (v i) (w i))

-- Source: PhysLean (Lorentz.Vector.CausalCharacter.toCtorIdx)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causalcharacter_toctoridx : Lorentz.Vector.CausalCharacter → Nat

-- Source: PhysLean (SpaceTime.distDeriv_apply')
-- [complex signature, not re-axiomatized]
-- spacetime_distderiv_apply' : ∀ {M : Type} {d : Nat} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] (μ : Sum (Fin 1) (Fin d))
--   (f : Distribution Real (SpaceTime d) M) (ε : SchwartzMap (SpaceTime d) Real),
--   Eq (ContinuousLinearMap.funLike.coe (LinearMap.instFunLike.coe (SpaceTime.distDeriv μ) f) ε)
--     (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg
--       (ContinuousLinearMap.funLike.coe f
--         (ContinuousLinearMap.funLike.coe (SchwartzMap.evalCLM (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ))
--           (ContinuousLinearMap.funLike.coe (SchwartzMap.fderivCLM Real) ε))))

-- Source: PhysLean (complexLorentzTensor.contrMetric_eq_fromConstPair)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrmetric_eq_fromconstpair : Eq complexLorentzTensor.contrMetric (TensorSpecies.Tensor.fromConstPair Lorentz.contrMetric)

-- Source: PhysLean (Lorentz.coContrUnit_apply_one)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrunit_apply_one : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.coContrUnit.hom) 1)
--   Lorentz.coContrUnitVal

-- Source: PhysLean (complexLorentzTensor.basis_up_eq)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_basis_up_eq : ∀ {i : Fin 4},
--   Eq (Module.Basis.instFunLike.coe (complexLorentzTensor.basis complexLorentzTensor.Color.up) i)
--     (Module.Basis.instFunLike.coe Lorentz.complexContrBasisFin4 i)

-- Source: PhysLean (Lorentz.Vector.causalCharacter.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causalcharacter_eq_1 : ∀ {d : Nat} (p : Lorentz.Vector d),
--   Eq p.causalCharacter
--     (ite (Eq (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct p) p) 0)
--       Lorentz.Vector.CausalCharacter.lightLike
--       (ite
--         (Real.instLT.lt 0
--           (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct p) p))
--         Lorentz.Vector.CausalCharacter.timeLike Lorentz.Vector.CausalCharacter.spaceLike))

-- Source: PhysLean (minkowskiMatrix.η_apply_sq_eq_one)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_η_apply_sq_eq_one : ∀ {d : Nat} (μ : Sum (Fin 1) (Fin d)), Eq (instHPow.hPow (minkowskiMatrix μ μ) 2) 1

-- Source: PhysLean (CliffordAlgebra.ι_mul_ι_add_swap)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_ι_mul_ι_add_swap : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   {Q : QuadraticForm R M} (a b : M),
--   Eq
--     (instHAdd.hAdd
--       (instHMul.hMul (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) a)
--         (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) b))
--       (instHMul.hMul (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) b)
--         (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) a)))
--     (RingHom.instFunLike.coe (algebraMap R (CliffordAlgebra Q))
--       (QuadraticMap.polar (QuadraticMap.instFunLike.coe Q) a b))

-- Source: PhysLean (Lorentz.ContrMod.instAddCommGroup)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_instaddcommgroup : {d : Nat} → AddCommGroup (Lorentz.ContrMod d)

-- Source: PhysLean (complexLorentzTensor.coContrUnit.eq_1)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cocontrunit_eq_1 : Eq complexLorentzTensor.coContrUnit (TensorSpecies.unitTensor complexLorentzTensor.Color.up)

-- Source: PhysLean (LorentzGroup.boost.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_eq_1 : ∀ {d : Nat} (i : Fin d) (β : Real) (hβ : Real.instLT.lt (abs β) 1),
--   Eq (LorentzGroup.boost i β hβ)
--     ⟨fun j k =>
--       ite (And (Eq k (Sum.inl 0)) (Eq j (Sum.inl 0))) (LorentzGroup.γ β)
--         (ite (And (Eq k (Sum.inl 0)) (Eq j (Sum.inr i))) (instHMul.hMul (Real.instNeg.neg (LorentzGroup.γ β)) β)
--           (ite (And (Eq k (Sum.inr i)) (Eq j (Sum.inl 0))) (instHMul.hMul (Real.instNeg.neg (LorentzGroup.γ β)) β)
--             (ite (And (Eq k (Sum.inr i)) (Eq j (Sum.inr i))) (LorentzGroup.γ β) (ite (Eq j k) 1 0)))),
--       ⋯⟩

-- Source: PhysLean (LorentzGroup.toVector_eq_basis_iff_timeComponent_eq_one)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_tovector_eq_basis_iff_timecomponent_eq_one : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Iff (Eq (LorentzGroup.toVector Λ) (Module.Basis.instFunLike.coe Lorentz.Vector.basis (Sum.inl 0)))
--     (Eq (Λ.val (Sum.inl 0) (Sum.inl 0)) 1)

-- Source: PhysLean (Lorentz.coContrContract_hom_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrcontract_hom_tmul : ∀ {d : Nat} (φ : (Lorentz.Co d).V.carrier) (ψ : (Lorentz.Contr d).V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom Lorentz.coContrContract.hom)
--       (TensorProduct.tmul Real φ ψ))
--     (dotProduct (Lorentz.CoMod.toFin1dℝ φ) (Lorentz.ContrMod.toFin1dℝ ψ))

-- Source: PhysLean (Lorentz.coCoToMatrix)
-- [complex signature, not re-axiomatized]
-- lorentz_cocotomatrix : LinearEquiv (RingHom.id Complex) (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexCo).V.carrier
--   (Matrix (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3)) Complex)

-- Source: PhysLean (LorentzGroup.transpose_mul_minkowskiMatrix_mul_self)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_transpose_mul_minkowskimatrix_mul_self : ∀ {d : Nat} {Λ : (LorentzGroup d).Elem},
--   Eq (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (instHMul.hMul Λ.val.transpose minkowskiMatrix) Λ.val)
--     minkowskiMatrix

-- Source: PhysLean (Lorentz.preCoContrUnitVal_expand_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_precocontrunitval_expand_tmul : ∀ {d : Nat},
--   Eq (Lorentz.preCoContrUnitVal d)
--     (Finset.univ.sum fun i =>
--       TensorProduct.tmul Real (Module.Basis.instFunLike.coe (Lorentz.coBasis d) i)
--         (Module.Basis.instFunLike.coe (Lorentz.contrBasis d) i))

-- Source: PhysLean (Lorentz.ContrMod.mulVec_mulVec)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_mulvec_mulvec : ∀ {d : Nat} (M N : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real) (v : Lorentz.ContrMod d),
--   Eq (Lorentz.ContrMod.mulVec M (Lorentz.ContrMod.mulVec N v))
--     (Lorentz.ContrMod.mulVec (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul M N) v)

-- Source: PhysLean (Lorentz.coContrToMatrix_ρ)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrtomatrix_ρ : ∀ (v : (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr).V.carrier)
--   (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (EquivLike.toFunLike.coe Lorentz.coContrToMatrix
--       (LinearMap.instFunLike.coe
--         (TensorProduct.map (MonoidHom.instFunLike.coe Lorentz.complexCo.ρ M)
--           (MonoidHom.instFunLike.coe Lorentz.complexContr.ρ M))
--         v))
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--         (Matrix.inv.inv
--             (MonoidHom.instFunLike.coe LorentzGroup.toComplex
--               (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M))).transpose
--         (EquivLike.toFunLike.coe Lorentz.coContrToMatrix v))
--       (MonoidHom.instFunLike.coe LorentzGroup.toComplex
--           (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M)).transpose)

-- Source: PhysLean (LorentzGroup.mem_iff_transpose)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_mem_iff_transpose : ∀ {d : Nat} {Λ : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real},
--   Iff (Set.instMembership.mem (LorentzGroup d) Λ) (Set.instMembership.mem (LorentzGroup d) Λ.transpose)

-- Source: PhysLean (SpaceTime.toTimeAndSpace_symm_apply_time_space)
-- [complex signature, not re-axiomatized]
-- spacetime_totimeandspace_symm_apply_time_space : ∀ {d : Nat} {c : SpeedOfLight} (x : SpaceTime d),
--   Eq
--     (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c).symm
--       { fst := LinearMap.instFunLike.coe (SpaceTime.time c) x,
--         snd := ContinuousLinearMap.funLike.coe SpaceTime.space x })
--     x

-- Source: PhysLean (complexLorentzTensor.leftAltLeftUnit)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_leftaltleftunit : complexLorentzTensor.Tensor
--   (Matrix.vecCons complexLorentzTensor.Color.upL (Matrix.vecCons complexLorentzTensor.Color.downL Matrix.vecEmpty))

-- Source: PhysLean (LorentzGroup.detContinuous.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_detcontinuous_eq_1 : ∀ {d : Nat},
--   Eq LorentzGroup.detContinuous (LorentzGroup.coeForℤ₂.comp { toFun := fun Λ => ⟨Λ.val.det, ⋯⟩, continuous_toFun := ⋯ })

-- Source: PhysLean (Lorentz.preCoMetricVal)
-- [complex signature, not re-axiomatized]
-- lorentz_precometricval : (d : optParam Nat 3) → (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Co d)).V.carrier

-- Source: PhysLean (LorentzGroup.eq_of_action_vector_eq)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_eq_of_action_vector_eq : ∀ {d : Nat} {Λ Λ' : (LorentzGroup d).Elem},
--   (∀ (p : Lorentz.Vector d), Eq (instHSMul.hSMul Λ p) (instHSMul.hSMul Λ' p)) → Eq Λ Λ'

-- Source: PhysLean (complexLorentzTensor.rightAltRightUnit)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_rightaltrightunit : complexLorentzTensor.Tensor
--   (Matrix.vecCons complexLorentzTensor.Color.upR (Matrix.vecCons complexLorentzTensor.Color.downR Matrix.vecEmpty))

-- Source: PhysLean (complexLorentzTensor.altRightMetric_contr_rightMetric)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altrightmetric_contr_rightmetric : Eq
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.contrT 2 1 2 ⋯)
--     (LinearMap.instFunLike.coe
--       (LinearMap.instFunLike.coe TensorSpecies.Tensor.prodT
--         (EquivLike.toFunLike.coe
--           (TensorSpecies.Tensorial.self complexLorentzTensor
--               (Matrix.vecCons complexLorentzTensor.Color.downR
--                 (Matrix.vecCons complexLorentzTensor.Color.downR Matrix.vecEmpty))).toTensor
--           complexLorentzTensor.altRightMetric))
--       (EquivLike.toFunLike.coe
--         (TensorSpecies.Tensorial.self complexLorentzTensor
--             (Matrix.vecCons complexLorentzTensor.Color.upR
--               (Matrix.vecCons complexLorentzTensor.Color.upR Matrix.vecEmpty))).toTensor
--         complexLorentzTensor.rightMetric)))
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT (Matrix.vecCons 0 (Matrix.vecCons 1 Matrix.vecEmpty)) ⋯)
--     (EquivLike.toFunLike.coe
--       (TensorSpecies.Tensorial.self complexLorentzTensor
--           (Matrix.vecCons complexLorentzTensor.Color.downR
--             (Matrix.vecCons complexLorentzTensor.Color.upR Matrix.vecEmpty))).toTensor
--       complexLorentzTensor.altRightRightUnit))

-- Source: PhysLean (Lorentz.ContrMod.mulVec_toFin1dℝ)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_mulvec_tofin1dℝ : ∀ {d : Nat} (M : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real) (v : Lorentz.ContrMod d),
--   Eq (Lorentz.ContrMod.mulVec M v).toFin1dℝ (M.mulVec v.toFin1dℝ)

-- Source: PhysLean (complexLorentzTensor.contrCoUnit.eq_1)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrcounit_eq_1 : Eq complexLorentzTensor.contrCoUnit (TensorSpecies.unitTensor complexLorentzTensor.Color.down)

-- Source: PhysLean (complexLorentzTensor.actionT_contrMetric)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_actiont_contrmetric : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (instHSMul.hSMul g complexLorentzTensor.contrMetric) complexLorentzTensor.contrMetric

-- Source: PhysLean (Lorentz.coContrUnit)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrunit : Action.instCategory.Hom
--   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--   (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr)

-- Source: PhysLean (SpaceTime.time)
-- [complex signature, not re-axiomatized]
-- spacetime_time : {d : Nat} → optParam SpeedOfLight 1 → LinearMap (RingHom.id Real) (SpaceTime d) Time

-- Source: PhysLean (Lorentz.SL2C.toSelfAdjointMap)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_toselfadjointmap : Matrix.SpecialLinearGroup (Fin 2) Complex →
--   LinearMap (RingHom.id Real)
--     (Subtype fun x => SetLike.instMembership.mem (selfAdjoint (Matrix (Fin 2) (Fin 2) Complex)) x)
--     (Subtype fun x => SetLike.instMembership.mem (selfAdjoint (Matrix (Fin 2) (Fin 2) Complex)) x)

-- Source: PhysLean (SpaceTime.timeSlice.eq_1)
-- [complex signature, not re-axiomatized]
-- spacetime_timeslice_eq_1 : ∀ {d : Nat} {M : Type} (c : SpeedOfLight),
--   Eq (SpaceTime.timeSlice c)
--     { toFun := fun f => Function.curry (Function.comp f (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c).symm)),
--       invFun := fun f => Function.comp (Function.uncurry f) (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c)),
--       left_inv := ⋯, right_inv := ⋯ }

-- Source: PhysLean (LorentzGroup.generalizedBoost_isProper)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_generalizedboost_isproper : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem), LorentzGroup.IsProper (LorentzGroup.generalizedBoost u v)

-- Source: PhysLean (LorentzGroup.instDiscreteTopologyMultiplicativeZModOfNatNat)
/-- The topological space defined by `ℤ₂` is discrete.  -/
axiom lorentzgroup_instdiscretetopologymultiplicativezmodofnatnat :
  DiscreteTopology (Multiplicative (ZMod 2))

-- Source: PhysLean (CliffordAlgebra.mul_ι_mul_ι_of_isOrtho)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_mul_ι_mul_ι_of_isortho : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   {Q : QuadraticForm R M} (x : CliffordAlgebra Q) {a b : M},
--   QuadraticMap.IsOrtho Q a b →
--     Eq
--       (instHMul.hMul (instHMul.hMul x (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) a))
--         (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) b))
--       (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg
--         (instHMul.hMul (instHMul.hMul x (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) b))
--           (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) a)))

-- Source: PhysLean (CliffordAlgebra.ι_range_map_lift)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_ι_range_map_lift : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   {Q : QuadraticForm R M} {A : Type u_3} [inst_3 : Semiring A] [inst_4 : Algebra R A] (f : LinearMap (RingHom.id R) M A)
--   (cond :
--     ∀ (m : M),
--       Eq (instHMul.hMul (LinearMap.instFunLike.coe f m) (LinearMap.instFunLike.coe f m))
--         (RingHom.instFunLike.coe (algebraMap R A) (QuadraticMap.instFunLike.coe Q m))),
--   Eq
--     (Submodule.map (EquivLike.toFunLike.coe (CliffordAlgebra.lift Q) ⟨f, cond⟩).toLinearMap
--       (LinearMap.range (CliffordAlgebra.ι Q)))
--     (LinearMap.range f)

-- Source: PhysLean (Lorentz.Velocity)
-- [complex signature, not re-axiomatized]
-- lorentz_velocity : (d : optParam Nat 3) → Set (Lorentz.Vector d)

-- Source: PhysLean (LorentzGroup.boost)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost : {d : Nat} → Fin d → (β : Real) → Real.instLT.lt (abs β) 1 → (LorentzGroup d).Elem

-- Source: PhysLean (complexLorentzTensor.altRightMetric)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altrightmetric : complexLorentzTensor.Tensor
--   (Matrix.vecCons complexLorentzTensor.Color.downR (Matrix.vecCons complexLorentzTensor.Color.downR Matrix.vecEmpty))

-- Source: PhysLean (Lorentz.Vector.instInnerReal)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_instinnerreal : (d : Nat) → Inner Real (Lorentz.Vector d)

-- Source: PhysLean (Lorentz.ContrMod.stdBasis_repr_apply_toFun)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_stdbasis_repr_apply_tofun : ∀ {d : Nat} (a : Lorentz.ContrMod d) (a_1 : Sum (Fin 1) (Fin d)),
--   Eq (Finsupp.instFunLike.coe (EquivLike.toFunLike.coe Lorentz.ContrMod.stdBasis.repr a) a_1)
--     (EquivLike.toFunLike.coe Lorentz.ContrMod.toFin1dℝEquiv a a_1)

-- Source: PhysLean (LorentzGroup.mem_iff_neg_mem)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_mem_iff_neg_mem : ∀ {d : Nat} {Λ : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real},
--   Iff (Set.instMembership.mem (LorentzGroup d) Λ) (Set.instMembership.mem (LorentzGroup d) (Matrix.neg.neg Λ))

-- Source: PhysLean (realLorentzTensor.prodT_toComplex)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_prodt_tocomplex : InformalLemma

-- Source: PhysLean (complexLorentzTensor.coMetric_eq_complexCoBasisFin4)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cometric_eq_complexcobasisfin4 : Eq complexLorentzTensor.coMetric
--   (instHSub.hSub
--     (instHSub.hSub
--       (instHSub.hSub
--         (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasisFin4 0)
--             (Module.Basis.instFunLike.coe Lorentz.complexCoBasisFin4 0)))
--         (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasisFin4 1)
--             (Module.Basis.instFunLike.coe Lorentz.complexCoBasisFin4 1))))
--       (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--         (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasisFin4 2)
--           (Module.Basis.instFunLike.coe Lorentz.complexCoBasisFin4 2))))
--     (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasisFin4 3)
--         (Module.Basis.instFunLike.coe Lorentz.complexCoBasisFin4 3))))

-- Source: PhysLean (Lorentz.coContrContract_basis)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrcontract_basis : ∀ {d : Nat} (i j : Sum (Fin 1) (Fin d)),
--   Eq
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom Lorentz.coContrContract.hom)
--       (TensorProduct.tmul Real (Module.Basis.instFunLike.coe (Lorentz.coBasis d) i)
--         (Module.Basis.instFunLike.coe (Lorentz.contrBasis d) j)))
--     (ite (Eq i j) 1 0)

-- Source: PhysLean (Lorentz.Vector.isLorentz_iff_basis)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_islorentz_iff_basis : ∀ {d : Nat} (f : LinearMap (RingHom.id Real) (Lorentz.Vector d) (Lorentz.Vector d)),
--   Iff (Lorentz.Vector.IsLorentz f)
--     (∀ (μ ν : Sum (Fin 1) (Fin d)),
--       Eq
--         (ContinuousLinearMap.funLike.coe
--           (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct
--             (LinearMap.instFunLike.coe f (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ)))
--           (LinearMap.instFunLike.coe f (Module.Basis.instFunLike.coe Lorentz.Vector.basis ν)))
--         (ContinuousLinearMap.funLike.coe
--           (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct
--             (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ))
--           (Module.Basis.instFunLike.coe Lorentz.Vector.basis ν)))

-- Source: PhysLean (Lorentz.inclCongrRealLorentz_val)
-- [complex signature, not re-axiomatized]
-- lorentz_inclcongrreallorentz_val : ∀ (v : Lorentz.ContrMod 3),
--   Eq (LinearMap.instFunLike.coe Lorentz.inclCongrRealLorentz v).val
--     (Function.comp (RingHom.instFunLike.coe Complex.ofRealHom) v.toFin1dℝ)

-- Source: PhysLean (LorentzGroup.boost_zero_inr_succ_inr_succ)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_zero_inr_succ_inr_succ : ∀ {d : Nat} {β : Real} (hβ : Real.instLT.lt (abs β) 1) (i1 i2 : Fin d),
--   Eq ((LorentzGroup.boost 0 β hβ).val (Sum.inr i1.succ) (Sum.inr i2.succ)) (ite (Eq i1 i2) 1 0)

-- Source: PhysLean (SpaceTime.«_aux_PhysLean_SpaceAndTime_SpaceTime_Derivatives___macroRules_SpaceTime_term∂__1»)
-- [complex signature, not re-axiomatized]
-- spacetime_«_aux_physlean_spaceandtime_spacetime_derivatives___macrorules_spacetime_term∂__1» : Lean.Macro

-- Source: PhysLean (complexLorentzTensor.contrCoUnit_eq_complexContrBasisFin4_complexCoBasisFin4)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrcounit_eq_complexcontrbasisfin4_complexcobasisfin4 : Eq complexLorentzTensor.contrCoUnit
--   (Finset.univ.sum fun i =>
--     LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasisFin4 i)
--         (Module.Basis.instFunLike.coe Lorentz.complexCoBasisFin4 i)))

-- Source: PhysLean (complexLorentzTensor.leftAltLeftUnit_eq_ofRat)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_leftaltleftunit_eq_ofrat : Eq complexLorentzTensor.leftAltLeftUnit
--   (LinearMap.instFunLike.coe complexLorentzTensor.ofRat fun f => ite (Eq (f 0) (f 1)) 1 0)

-- Source: PhysLean (CliffordAlgebra.lift_unique)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_lift_unique : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   {Q : QuadraticForm R M} {A : Type u_3} [inst_3 : Semiring A] [inst_4 : Algebra R A] (f : LinearMap (RingHom.id R) M A)
--   (cond :
--     ∀ (m : M),
--       Eq (instHMul.hMul (LinearMap.instFunLike.coe f m) (LinearMap.instFunLike.coe f m))
--         (RingHom.instFunLike.coe (algebraMap R A) (QuadraticMap.instFunLike.coe Q m)))
--   (g : AlgHom R (CliffordAlgebra Q) A),
--   Iff (Eq (g.toLinearMap.comp (CliffordAlgebra.ι Q)) f)
--     (Eq g (EquivLike.toFunLike.coe (CliffordAlgebra.lift Q) ⟨f, cond⟩))

-- Source: PhysLean (Lorentz.CoMod.toFin1dℝ)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_tofin1dℝ : {d : Nat} → Lorentz.CoMod d → Sum (Fin 1) (Fin d) → Real

-- Source: PhysLean (LorentzGroup.toGL)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_togl : {d : Nat} → MonoidHom (LorentzGroup d).Elem (Matrix.GeneralLinearGroup (Sum (Fin 1) (Fin d)) Real)

-- Source: PhysLean (LorentzGroup.toProd_continuous)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_toprod_continuous : ∀ {d : Nat}, Continuous (MonoidHom.instFunLike.coe LorentzGroup.toProd)

-- Source: PhysLean (complexLorentzTensor.rightAltRightUnit_eq_fromPairT)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_rightaltrightunit_eq_frompairt : Eq complexLorentzTensor.rightAltRightUnit
--   (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT Fermion.rightAltRightUnitVal)

-- Source: PhysLean (complexLorentzTensor.leftMetric_antisymm)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_leftmetric_antisymm : Eq
--   (EquivLike.toFunLike.coe
--     (TensorSpecies.Tensorial.self complexLorentzTensor
--         (Matrix.vecCons complexLorentzTensor.Color.upL
--           (Matrix.vecCons complexLorentzTensor.Color.upL Matrix.vecEmpty))).toTensor
--     complexLorentzTensor.leftMetric)
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT (Matrix.vecCons 1 (Matrix.vecCons 0 Matrix.vecEmpty)) ⋯)
--     (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg
--       (EquivLike.toFunLike.coe
--         (TensorSpecies.Tensorial.self complexLorentzTensor
--             (Matrix.vecCons complexLorentzTensor.Color.upL
--               (Matrix.vecCons complexLorentzTensor.Color.upL Matrix.vecEmpty))).toTensor
--         complexLorentzTensor.leftMetric)))

-- Source: PhysLean (Lorentz.preCoMetric)
-- [complex signature, not re-axiomatized]
-- lorentz_precometric : (d : optParam Nat 3) →
--   Action.instCategory.Hom (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem))
--     (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Co d))

-- Source: PhysLean (Lorentz.instTopologicalSpaceCarrierRealVModuleCatElemMatrixSumFinOfNatNatLorentzGroupContr)
-- [complex signature, not re-axiomatized]
-- lorentz_insttopologicalspacecarrierrealvmodulecatelemmatrixsumfinofnatnatlorentzgroupcontr : {d : Nat} → TopologicalSpace (Lorentz.Contr d).V.carrier

-- Source: PhysLean (Lorentz.Vector.equivEuclid_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_equiveuclid_apply : ∀ (d : Nat) (v : Lorentz.Vector d) (i : Sum (Fin 1) (Fin d)),
--   Eq ((EquivLike.toFunLike.coe (Lorentz.Vector.equivEuclid d) v).ofLp i) (v i)

-- Source: PhysLean (SpaceTime.timeSpaceBasis.eq_1)
-- [complex signature, not re-axiomatized]
-- spacetime_timespacebasis_eq_1 : ∀ {d : Nat} (c : SpeedOfLight),
--   Eq (SpaceTime.timeSpaceBasis c)
--     { repr := (SpaceTime.toTimeAndSpace c).trans (Time.basis.toBasis.prod Space.basis.toBasis).repr }

-- Source: PhysLean (Lorentz.coContrToMatrix)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrtomatrix : LinearEquiv (RingHom.id Complex)
--   (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr).V.carrier
--   (Matrix (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3)) Complex)

-- Source: PhysLean (Lorentz.CoVector.neg_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_neg_apply : ∀ {d : Nat} (v : Lorentz.CoVector d) (i : Sum (Fin 1) (Fin d)),
--   Eq (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg v i) (Real.instNeg.neg (v i))

-- Source: PhysLean (Lorentz.contrCoToMatrixRe_ρ_symm)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcotomatrixre_ρ_symm : ∀ {d : Nat} (v : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real) (M : (LorentzGroup d).Elem),
--   Eq
--     (LinearMap.instFunLike.coe
--       (TensorProduct.map (MonoidHom.instFunLike.coe (Lorentz.Contr d).ρ M)
--         (MonoidHom.instFunLike.coe (Lorentz.Co d).ρ M))
--       (EquivLike.toFunLike.coe Lorentz.contrCoToMatrixRe.symm v))
--     (EquivLike.toFunLike.coe Lorentz.contrCoToMatrixRe.symm
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul M.val v)
--         (Matrix.inv.inv M.val)))

-- Source: PhysLean (Lorentz.complexCoBasisFin4.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcobasisfin4_eq_1 : Eq Lorentz.complexCoBasisFin4 (Lorentz.complexCoBasis.reindex finSumFinEquiv)

-- Source: PhysLean (Lorentz.Vector.innerProductSpace)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_innerproductspace : (d : Nat) → InnerProductSpace Real (Lorentz.Vector d)

-- Source: PhysLean (LorentzGroup.rotations_subset_restricted)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_rotations_subset_restricted : ∀ (d : Nat), CompleteLattice.instOmegaCompletePartialOrder.le (LorentzGroup.Rotations d) (LorentzGroup.restricted d)

-- Source: PhysLean (CliffordAlgebra.map_comp_ι)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_map_comp_ι : ∀ {R : Type u_1} [inst : CommRing R] {M₁ : Type u_4} {M₂ : Type u_5} [inst_1 : AddCommGroup M₁]
--   [inst_2 : AddCommGroup M₂] [inst_3 : Module R M₁] [inst_4 : Module R M₂] {Q₁ : QuadraticForm R M₁}
--   {Q₂ : QuadraticForm R M₂} (f : QuadraticMap.Isometry Q₁ Q₂),
--   Eq ((CliffordAlgebra.map f).toLinearMap.comp (CliffordAlgebra.ι Q₁)) ((CliffordAlgebra.ι Q₂).comp f.toLinearMap)

-- Source: PhysLean (LorentzGroup.not_isOrthochronous_iff_toVector_timeComponet_nonpos)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_not_isorthochronous_iff_tovector_timecomponet_nonpos : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Iff (Not (LorentzGroup.IsOrthochronous Λ)) (Real.instLE.le (LorentzGroup.toVector Λ).timeComponent 0)

-- Source: PhysLean (SpaceTime.apply_fderiv_eq_distDeriv)
-- [complex signature, not re-axiomatized]
-- spacetime_apply_fderiv_eq_distderiv : ∀ {M : Type} {d : Nat} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] (μ : Sum (Fin 1) (Fin d))
--   (f : Distribution Real (SpaceTime d) M) (ε : SchwartzMap (SpaceTime d) Real),
--   Eq
--     (ContinuousLinearMap.funLike.coe f
--       (ContinuousLinearMap.funLike.coe (SchwartzMap.evalCLM (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ))
--         (ContinuousLinearMap.funLike.coe (SchwartzMap.fderivCLM Real) ε)))
--     (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg
--       (ContinuousLinearMap.funLike.coe (LinearMap.instFunLike.coe (SpaceTime.distDeriv μ) f) ε))

-- Source: PhysLean (LorentzGroup.instInvertibleMatrixSumFinOfNatNatRealValMemSet)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_instinvertiblematrixsumfinofnatnatrealvalmemset : {d : Nat} → (M : (LorentzGroup d).Elem) → Invertible M.val

-- Source: PhysLean (CliffordAlgebra.ι_mul_ι_mul_of_isOrtho)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_ι_mul_ι_mul_of_isortho : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   {Q : QuadraticForm R M} (x : CliffordAlgebra Q) {a b : M},
--   QuadraticMap.IsOrtho Q a b →
--     Eq
--       (instHMul.hMul (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) a)
--         (instHMul.hMul (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) b) x))
--       (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg
--         (instHMul.hMul (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) b)
--           (instHMul.hMul (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) a) x)))

-- Source: PhysLean (complexLorentzTensor.rightMetric_eq_ofRat)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_rightmetric_eq_ofrat : Eq complexLorentzTensor.rightMetric
--   (LinearMap.instFunLike.coe complexLorentzTensor.ofRat fun f =>
--     ite (And (Eq (f 0) 0) (Eq (f 1) 1)) (-1) (ite (And (Eq (f 1) 0) (Eq (f 0) 1)) 1 0))

-- Source: PhysLean (realLorentzTensor.Color.down.elim)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_color_down_elim : {motive : realLorentzTensor.Color → Sort u} →
--   (t : realLorentzTensor.Color) → Eq t.ctorIdx 1 → motive realLorentzTensor.Color.down → motive t

-- Source: PhysLean (complexLorentzTensor.altRightRightUnit_eq_altRightBasis_rightBasis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altrightrightunit_eq_altrightbasis_rightbasis : Eq complexLorentzTensor.altRightRightUnit
--   (Finset.univ.sum fun i =>
--     LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altRightBasis i)
--         (Module.Basis.instFunLike.coe Fermion.rightBasis i)))

-- Source: PhysLean (Lorentz.Vector.coord_contDiff)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_coord_contdiff : ∀ {n : WithTop ENat} {d : Nat} (i : Sum (Fin 1) (Fin d)), ContDiff Real n fun v => v i

-- Source: PhysLean (Lorentz.Vector.minkowskiProduct_basis_right)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproduct_basis_right : ∀ {d : Nat} (μ : Sum (Fin 1) (Fin d)) (p : Lorentz.Vector d),
--   Eq
--     (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct p)
--       (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ))
--     (instHMul.hMul (minkowskiMatrix μ μ) (p μ))

-- Source: PhysLean (complexLorentzTensor.Color.upL.elim)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_color_upl_elim : {motive : complexLorentzTensor.Color → Sort u} →
--   (t : complexLorentzTensor.Color) → Eq t.ctorIdx 0 → motive complexLorentzTensor.Color.upL → motive t

-- Source: PhysLean (Lorentz.contrContrContractField.matrix_apply_stdBasis)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_matrix_apply_stdbasis : ∀ {d : Nat} {Λ : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real} (ν μ : Sum (Fin 1) (Fin d)),
--   Eq (Λ ν μ)
--     (instHMul.hMul (minkowskiMatrix ν ν)
--       (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--         (TensorProduct.tmul Real (Module.Basis.instFunLike.coe Lorentz.ContrMod.stdBasis ν)
--           (Lorentz.ContrMod.mulVec Λ (Module.Basis.instFunLike.coe Lorentz.ContrMod.stdBasis μ)))))

-- Source: PhysLean (Lorentz.Vector.CausalCharacter.timeLike.sizeOf_spec)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causalcharacter_timelike_sizeof_spec : Eq (Lorentz.Vector.CausalCharacter._sizeOf_inst.sizeOf Lorentz.Vector.CausalCharacter.timeLike) 1

-- Source: PhysLean (Lorentz.coContrUnitVal_expand_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrunitval_expand_tmul : Eq Lorentz.coContrUnitVal
--   (instHAdd.hAdd
--     (instHAdd.hAdd
--       (instHAdd.hAdd
--         (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inl 0))
--           (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inl 0)))
--         (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 0))
--           (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 0))))
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 1))
--         (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 1))))
--     (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 2))
--       (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 2))))

-- Source: PhysLean (Lorentz.Vector.CausalCharacter.ofNat)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causalcharacter_ofnat : Nat → Lorentz.Vector.CausalCharacter

-- Source: PhysLean (complexLorentzTensor.coBispinorUp_eq_metric_contr_coBispinorDown)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cobispinorup_eq_metric_contr_cobispinordown : InformalLemma

-- Source: PhysLean (complexLorentzTensor.prodT_ofRat_ofRat)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_prodt_ofrat_ofrat : ∀ {n n1 : Nat} {c : Fin n → complexLorentzTensor.Color}
--   (f : TensorSpecies.Tensor.ComponentIdx c → RatComplexNum) {c1 : Fin n1 → complexLorentzTensor.Color}
--   (f1 : TensorSpecies.Tensor.ComponentIdx c1 → RatComplexNum),
--   Eq
--     (LinearMap.instFunLike.coe
--       (LinearMap.instFunLike.coe TensorSpecies.Tensor.prodT (LinearMap.instFunLike.coe complexLorentzTensor.ofRat f))
--       (LinearMap.instFunLike.coe complexLorentzTensor.ofRat f1))
--     (LinearMap.instFunLike.coe complexLorentzTensor.ofRat fun b =>
--       instHMul.hMul (f (EquivLike.toFunLike.coe TensorSpecies.Tensor.ComponentIdx.prodEquiv b).fst)
--         (f1 (EquivLike.toFunLike.coe TensorSpecies.Tensor.ComponentIdx.prodEquiv b).snd))

-- Source: PhysLean (Lorentz.ContrℂModule.SL2CRep)
-- [complex signature, not re-axiomatized]
-- lorentz_contrℂmodule_sl2crep : Representation Complex (Matrix.SpecialLinearGroup (Fin 2) Complex) Lorentz.ContrℂModule

-- Source: PhysLean (LorentzGroup.toVector_rotation)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_tovector_rotation : ∀ {d : Nat} (Λ : Subtype fun x => SetLike.instMembership.mem (LorentzGroup.Rotations d) x),
--   Eq (LorentzGroup.toVector Λ.val) (Module.Basis.instFunLike.coe Lorentz.Vector.basis (Sum.inl 0))

-- Source: PhysLean (minkowskiMatrix.eq_transpose)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_eq_transpose : ∀ {d : Nat}, Eq minkowskiMatrix.transpose minkowskiMatrix

-- Source: PhysLean (complexLorentzTensor.altLeftLeftUnit.eq_1)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altleftleftunit_eq_1 : Eq complexLorentzTensor.altLeftLeftUnit (TensorSpecies.unitTensor complexLorentzTensor.Color.upL)

-- Source: PhysLean (SpaceTime.toTimeAndSpace_basis_inr)
-- [complex signature, not re-axiomatized]
-- spacetime_totimeandspace_basis_inr : ∀ {d : Nat} {c : SpeedOfLight} (i : Fin d),
--   Eq
--     (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c)
--       (Module.Basis.instFunLike.coe Lorentz.Vector.basis (Sum.inr i)))
--     { fst := 0, snd := OrthonormalBasis.instFunLike.coe Space.basis i }

-- Source: PhysLean (complexLorentzTensor.altLeftMetric_eq_ofRat)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altleftmetric_eq_ofrat : Eq complexLorentzTensor.altLeftMetric
--   (LinearMap.instFunLike.coe complexLorentzTensor.ofRat fun f =>
--     ite (And (Eq (f 0) 0) (Eq (f 1) 1)) 1 (ite (And (Eq (f 1) 0) (Eq (f 0) 1)) (-1) 0))

-- Source: PhysLean (Lorentz.CoVector.tensor_basis_map_eq_basis_reindex)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_tensor_basis_map_eq_basis_reindex : ∀ {d : Nat},
--   Eq
--     ((TensorSpecies.Tensor.basis (Matrix.vecCons realLorentzTensor.Color.down Matrix.vecEmpty)).map
--       Lorentz.CoVector.tensorial.toTensor.symm)
--     (Lorentz.CoVector.basis.reindex Lorentz.CoVector.indexEquiv.symm)

-- Source: PhysLean (Lorentz.Vector.boost_toCoord_eq)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_boost_tocoord_eq : ∀ {d : Nat} (i : Fin d) (β : Real) (hβ : Real.instLT.lt (abs β) 1) (p : Lorentz.Vector d),
--   Eq (instHSMul.hSMul (LorentzGroup.boost i β hβ) p) fun j =>
--     Lorentz.Vector.boost_toCoord_eq.match_1 (fun j => Real) j
--       (fun _ => instHMul.hMul (LorentzGroup.γ β) (instHSub.hSub (p (Sum.inl 0)) (instHMul.hMul β (p (Sum.inr i)))))
--       fun j =>
--       ite (Eq j i) (instHMul.hMul (LorentzGroup.γ β) (instHSub.hSub (p (Sum.inr i)) (instHMul.hMul β (p (Sum.inl 0)))))
--         (p (Sum.inr j))

-- Source: PhysLean (Lorentz.Vector.fderiv_coord)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_fderiv_coord : ∀ {d : Nat} (μ : Sum (Fin 1) (Fin d)) (x : Lorentz.Vector d),
--   Eq (fderiv Real (fun v => v μ) x) (Lorentz.Vector.coordCLM μ)

-- Source: PhysLean (complexLorentzTensor.ofRat_basis_repr_apply)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_ofrat_basis_repr_apply : ∀ {n : Nat} {c : Fin n → complexLorentzTensor.Color} (f : TensorSpecies.Tensor.ComponentIdx c → RatComplexNum)
--   (b : TensorSpecies.Tensor.ComponentIdx c),
--   Eq
--     (Finsupp.instFunLike.coe
--       (EquivLike.toFunLike.coe (TensorSpecies.Tensor.basis c).repr
--         (LinearMap.instFunLike.coe complexLorentzTensor.ofRat f))
--       b)
--     (RingHom.instFunLike.coe RatComplexNum.toComplexNum (f b))

-- Source: PhysLean (complexLorentzTensor.contrT_ofRat)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrt_ofrat : ∀ {n : Nat} {c : Fin (instHAdd.hAdd (instHAdd.hAdd n 1) 1) → complexLorentzTensor.Color}
--   {i j : Fin (instHAdd.hAdd (instHAdd.hAdd n 1) 1)} {h : And (Ne i j) (Eq (complexLorentzTensor.τ (c i)) (c j))}
--   (f : TensorSpecies.Tensor.ComponentIdx c → RatComplexNum),
--   Eq
--     (LinearMap.instFunLike.coe (TensorSpecies.Tensor.contrT n i j h)
--       (LinearMap.instFunLike.coe complexLorentzTensor.ofRat f))
--     (LinearMap.instFunLike.coe complexLorentzTensor.ofRat fun b =>
--       Finset.univ.sum fun x =>
--         f
--           (EquivLike.toFunLike.coe (TensorSpecies.Tensor.ComponentIdx.DropPairSection.ofFinEquiv ⋯ b)
--               { fst := x, snd := Fin.cast ⋯ x }).val)

-- Source: PhysLean (Lorentz.Vector.IsLorentz)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_islorentz : {d : Nat} → LinearMap (RingHom.id Real) (Lorentz.Vector d) (Lorentz.Vector d) → Prop

-- Source: PhysLean (complexLorentzTensor.rightMetric)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_rightmetric : complexLorentzTensor.Tensor
--   (Matrix.vecCons complexLorentzTensor.Color.upR (Matrix.vecCons complexLorentzTensor.Color.upR Matrix.vecEmpty))

-- Source: PhysLean (complexLorentzTensor.coBispinorUp)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cobispinorup : complexLorentzTensor.Tensor (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty) →
--   complexLorentzTensor.Tensor
--     (Matrix.vecCons complexLorentzTensor.Color.upL (Matrix.vecCons complexLorentzTensor.Color.upR Matrix.vecEmpty))

-- Source: PhysLean (SpaceTime.tensorDeriv_equivariant)
-- [complex signature, not re-axiomatized]
-- spacetime_tensorderiv_equivariant : ∀ {n d : Nat} {c : Fin n → realLorentzTensor.Color} {M : Type} [inst : NormedAddCommGroup M]
--   [inst_1 : NormedSpace Real M] [inst_2 : (realLorentzTensor d).Tensorial c M] [T2Space M] (f : SpaceTime d → M)
--   (Λ : (LorentzGroup d).Elem) (x : SpaceTime d),
--   Differentiable Real f →
--     Eq
--       (SpaceTime.tensorDeriv
--         (fun x => instHSMul.hSMul Λ (f (instHSMul.hSMul (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ) x))) x)
--       (instHSMul.hSMul Λ
--         (SpaceTime.tensorDeriv f (instHSMul.hSMul (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ) x)))

-- Source: PhysLean (Lorentz.CoVector.basis_eq_map_tensor_basis)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_basis_eq_map_tensor_basis : ∀ {d : Nat},
--   Eq Lorentz.CoVector.basis
--     (((TensorSpecies.Tensor.basis (Matrix.vecCons realLorentzTensor.Color.down Matrix.vecEmpty)).map
--           Lorentz.CoVector.tensorial.toTensor.symm).reindex
--       Lorentz.CoVector.indexEquiv)

-- Source: PhysLean (Lorentz.contrModCoModBi)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmodcomodbi : (d : Nat) → LinearMap (RingHom.id Real) (Lorentz.ContrMod d) (LinearMap (RingHom.id Real) (Lorentz.CoMod d) Real)

-- Source: PhysLean (Lorentz.Co)
-- [complex signature, not re-axiomatized]
-- lorentz_co : (d : Nat) → Rep Real (LorentzGroup d).Elem

-- Source: PhysLean (Lorentz.ContrMod.stdBasis_repr_apply_support_val)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_stdbasis_repr_apply_support_val : ∀ {d : Nat} (a : Lorentz.ContrMod d),
--   Eq (EquivLike.toFunLike.coe Lorentz.ContrMod.stdBasis.repr a).support.val (Multiset.map Subtype.val Finset.univ.val)

-- Source: PhysLean (Lorentz.preCoContrUnit)
-- [complex signature, not re-axiomatized]
-- lorentz_precocontrunit : (d : Nat) →
--   Action.instCategory.Hom (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem))
--     (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d))

-- Source: PhysLean (Lorentz.contrBasis_ρ_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_contrbasis_ρ_apply : ∀ {d : Nat} (M : (LorentzGroup d).Elem) (i j : Sum (Fin 1) (Fin d)),
--   Eq
--     (EquivLike.toFunLike.coe (LinearMap.toMatrix (Lorentz.contrBasis d) (Lorentz.contrBasis d))
--       (MonoidHom.instFunLike.coe (Lorentz.Contr d).ρ M) i j)
--     (M.val i j)

-- Source: PhysLean (Lorentz.CoVector.isNormedSpace)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_isnormedspace : (d : Nat) → NormedSpace Real (Lorentz.CoVector d)

-- Source: PhysLean (Lorentz.Vector.minkowskiProduct_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproduct_apply : ∀ {d : Nat} (p q : Lorentz.Vector d),
--   Eq (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct p) q)
--     (p.minkowskiProductMap q)

-- Source: PhysLean (LorentzGroup.det_on_connected_component)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_det_on_connected_component : ∀ {d : Nat} {Λ Λ' : (LorentzGroup d).Elem}, Set.instMembership.mem (connectedComponent Λ) Λ' → Eq Λ.val.det Λ'.val.det

-- Source: PhysLean (minkowskiMatrix.det_dual)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_det_dual : ∀ {d : Nat} (Λ : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real), Eq (minkowskiMatrix.dual Λ).det Λ.det

-- Source: PhysLean (Lorentz.CoMod.ext)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_ext : ∀ {d : Nat} {ψ ψ' : Lorentz.CoMod d}, Eq ψ.val ψ'.val → Eq ψ ψ'

-- Source: PhysLean (Lorentz.Vector.spatialCLM_basis_sum_inr)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_spatialclm_basis_sum_inr : ∀ {d : Nat} (i : Fin d),
--   Eq
--     (ContinuousLinearMap.funLike.coe (Lorentz.Vector.spatialCLM d)
--       (Module.Basis.instFunLike.coe Lorentz.Vector.basis (Sum.inr i)))
--     (OrthonormalBasis.instFunLike.coe (EuclideanSpace.basisFun (Fin d) Real) i)

-- Source: PhysLean (Lorentz.SL2C.toMatrix)
/-- The monoid homomorphisms from `SL(2, ℂ)` to matrices indexed by `Fin 1 ⊕ Fin 3`
formed by the action `M A Mᴴ`.  -/
axiom lorentz_sl2c_tomatrix :
  MonoidHom (Matrix.SpecialLinearGroup (Fin 2) Complex) (Matrix (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3)) Real)

-- Source: PhysLean (complexLorentzTensor.leftMetric_eq_ofRat)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_leftmetric_eq_ofrat : Eq complexLorentzTensor.leftMetric
--   (LinearMap.instFunLike.coe complexLorentzTensor.ofRat fun f =>
--     ite (And (Eq (f 0) 0) (Eq (f 1) 1)) (-1) (ite (And (Eq (f 1) 0) (Eq (f 0) 1)) 1 0))

-- Source: PhysLean (Lorentz.contrContrContract_hom_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontract_hom_tmul : ∀ {d : Nat} (φ ψ : (Lorentz.Contr d).V.carrier),
--   Eq (LinearMap.instFunLike.coe Lorentz.contrContrContractField (TensorProduct.tmul Real φ ψ))
--     (dotProduct (Lorentz.ContrMod.toFin1dℝ φ) (minkowskiMatrix.mulVec (Lorentz.ContrMod.toFin1dℝ ψ)))

-- Source: PhysLean (Lorentz.Vector.map_minkowskiProduct_eq_self_forall_iff)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_map_minkowskiproduct_eq_self_forall_iff : ∀ {d : Nat} (f : LinearMap (RingHom.id Real) (Lorentz.Vector d) (Lorentz.Vector d)),
--   Iff
--     (∀ (p q : Lorentz.Vector d),
--       Eq
--         (ContinuousLinearMap.funLike.coe
--           (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct (LinearMap.instFunLike.coe f p)) q)
--         (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct p) q))
--     (Eq f LinearMap.id)

-- Source: PhysLean (complexLorentzTensor.contrCoUnit_eq_complexContrBasis_complexCoBasis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrcounit_eq_complexcontrbasis_complexcobasis : Eq complexLorentzTensor.contrCoUnit
--   (Finset.univ.sum fun i =>
--     LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasis i)
--         (Module.Basis.instFunLike.coe Lorentz.complexCoBasis i)))

-- Source: PhysLean (complexLorentzTensor.actionT_leftMetric)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_actiont_leftmetric : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (instHSMul.hSMul g complexLorentzTensor.leftMetric) complexLorentzTensor.leftMetric

-- Source: PhysLean (complexLorentzTensor.coContrUnit_eq_complexCoBasis_complexContrBasis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cocontrunit_eq_complexcobasis_complexcontrbasis : Eq complexLorentzTensor.coContrUnit
--   (Finset.univ.sum fun i =>
--     LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasis i)
--         (Module.Basis.instFunLike.coe Lorentz.complexContrBasis i)))

-- Source: PhysLean (complexLorentzTensor.leftAltLeftUnit_eq_leftBasis_altLeftBasis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_leftaltleftunit_eq_leftbasis_altleftbasis : Eq complexLorentzTensor.leftAltLeftUnit
--   (Finset.univ.sum fun i =>
--     LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.leftBasis i)
--         (Module.Basis.instFunLike.coe Fermion.altLeftBasis i)))

-- Source: PhysLean (CliffordAlgebra.equivOfIsometry_apply)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_equivofisometry_apply : ∀ {R : Type u_1} [inst : CommRing R] {M₁ : Type u_4} {M₂ : Type u_5} [inst_1 : AddCommGroup M₁]
--   [inst_2 : AddCommGroup M₂] [inst_3 : Module R M₁] [inst_4 : Module R M₂] {Q₁ : QuadraticForm R M₁}
--   {Q₂ : QuadraticForm R M₂} (e : QuadraticMap.IsometryEquiv Q₁ Q₂) (a : CliffordAlgebra Q₁),
--   Eq (AlgEquiv.instFunLike.coe (CliffordAlgebra.equivOfIsometry e) a)
--     (AlgHom.funLike.coe (CliffordAlgebra.map e.toIsometry) a)

-- Source: PhysLean (Lorentz.Vector.interiorFutureLightCone.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_interiorfuturelightcone_eq_1 : ∀ {d : Nat} (p : Lorentz.Vector d),
--   Eq p.interiorFutureLightCone
--     (setOf fun q =>
--       And (Eq (instHSub.hSub q p).causalCharacter Lorentz.Vector.CausalCharacter.timeLike)
--         (Real.instLT.lt 0 (instHSub.hSub q p (Sum.inl 0))))

-- Source: PhysLean (complexLorentzTensor.termδR')
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_termδr' : Lean.ParserDescr

-- Source: PhysLean (SpaceTime.deriv_zero)
-- [complex signature, not re-axiomatized]
-- spacetime_deriv_zero : ∀ {d : Nat} (μ : Sum (Fin 1) (Fin d)), Eq (SpaceTime.deriv μ fun x => 0) 0

-- Source: PhysLean (SpaceTime.timeSpaceBasis_addHaar)
-- [complex signature, not re-axiomatized]
-- spacetime_timespacebasis_addhaar : ∀ {d : Nat} (c : optParam SpeedOfLight 1),
--   Eq (SpaceTime.timeSpaceBasis c).addHaar
--     (instHSMul.hSMul (ENNReal.ofReal (Real.instInv.inv c.val)) SpaceTime.instMeasureSpace.volume)

-- Source: PhysLean (Lorentz.coContrContraction_apply_metric)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrcontraction_apply_metric : Eq
--   (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr).V
--         (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--       ((Action.instBraidedCategory (ModuleCat Complex) (Matrix.SpecialLinearGroup (Fin 2) Complex)).braiding
--             Lorentz.complexCo Lorentz.complexContr).hom.hom)
--     (((fun X Y => LinearMap.instFunLike)
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexCo.V
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorUnit (ModuleCat Complex))
--               Lorentz.complexContr.V))
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexCo.V
--             Lorentz.complexContr.V)).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--         (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft Lorentz.complexCo.V
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.leftUnitor Lorentz.complexContr.V).hom))
--       (((fun X Y => LinearMap.instFunLike)
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexCo.V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                 (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr).V
--                 Lorentz.complexContr.V))
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexCo.V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                 (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                 Lorentz.complexContr.V))).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft Lorentz.complexCo.V
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerRight Lorentz.coContrContraction.hom
--               Lorentz.complexContr.V)))
--         (((fun X Y => LinearMap.instFunLike)
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexCo.V
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexCo.V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexContr.V
--                     Lorentz.complexContr.V)))
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexCo.V
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexCo.V
--                     Lorentz.complexContr.V)
--                   Lorentz.complexContr.V))).coe
--           ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft Lorentz.complexCo.V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.associator Lorentz.complexCo.V
--                   Lorentz.complexContr.V Lorentz.complexContr.V).inv))
--           (((fun X Y => LinearMap.instFunLike)
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexCo.V
--                     Lorentz.complexCo.V)
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexContr.V
--                     Lorentz.complexContr.V))
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexCo.V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexCo.V
--                     (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexContr.V
--                       Lorentz.complexContr.V)))).coe
--             ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.associator Lorentz.complexCo.V Lorentz.complexCo.V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexContr.V
--                     Lorentz.complexContr.V)).hom)
--             (TensorProduct.tmul Complex
--               (((fun X Y => LinearMap.instFunLike)
--                     (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                     (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexCo).V).coe
--                 ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.coMetric.hom) 1)
--               (((fun X Y => LinearMap.instFunLike)
--                     (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                     (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexContr).V).coe
--                 ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.contrMetric.hom) 1)))))))
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.contrCoUnit.hom) 1)

-- Source: PhysLean (minkowskiMatrix.det_eq_neg_one_pow_d)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_det_eq_neg_one_pow_d : ∀ {d : Nat}, Eq minkowskiMatrix.det (instHPow.hPow (-1) d)

-- Source: PhysLean (Lorentz.Vector.toTensor_symm_basis)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_totensor_symm_basis : ∀ {d : Nat} (μ : Sum (Fin 1) (Fin d)),
--   Eq
--     (EquivLike.toFunLike.coe Lorentz.Vector.tensorial.toTensor.symm
--       (Module.Basis.instFunLike.coe
--         (TensorSpecies.Tensor.basis (Matrix.vecCons realLorentzTensor.Color.up Matrix.vecEmpty))
--         (EquivLike.toFunLike.coe Lorentz.Vector.indexEquiv.symm μ)))
--     (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ)

-- Source: PhysLean (Lorentz.contrCoContraction_tmul_symm)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcocontraction_tmul_symm : ∀ (φ : Lorentz.complexContr.V.carrier) (ψ : Lorentz.complexCo.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.contrCoContraction.hom)
--       (TensorProduct.tmul Complex φ ψ))
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.coContrContraction.hom)
--       (TensorProduct.tmul Complex ψ φ))

-- Source: PhysLean (Lorentz.CoVector.smul_add)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_smul_add : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem) (p q : Lorentz.CoVector d),
--   Eq (instHSMul.hSMul Λ (instHAdd.hAdd p q)) (instHAdd.hAdd (instHSMul.hSMul Λ p) (instHSMul.hSMul Λ q))

-- Source: PhysLean (LorentzGroup.boost_inr_other_inr)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_inr_other_inr : ∀ {d : Nat} {i j k : Fin d} {β : Real} (hβ : Real.instLT.lt (abs β) 1),
--   Ne j i → Eq ((LorentzGroup.boost i β hβ).val (Sum.inr j) (Sum.inr k)) (ite (Eq j k) 1 0)

-- Source: PhysLean (SpaceTime.toTimeAndSpace_symm_apply_inl)
-- [complex signature, not re-axiomatized]
-- spacetime_totimeandspace_symm_apply_inl : ∀ {d : Nat} {c : SpeedOfLight} (t : Time) (s : Space d),
--   Eq (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c).symm { fst := t, snd := s } (Sum.inl 0))
--     (instHMul.hMul c.val t.val)

-- Source: PhysLean (Lorentz.coMetric.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_cometric_eq_1 : Eq Lorentz.coMetric
--   {
--     hom :=
--       ModuleCat.ofHom
--         {
--           toFun := fun a =>
--             have a' := a;
--             instHSMul.hSMul a' Lorentz.coMetricVal,
--           map_add' := Lorentz.coMetric._proof_1, map_smul' := Lorentz.coMetric._proof_2 },
--     comm := Lorentz.coMetric._proof_3 }

-- Source: PhysLean (LorentzGroup.orthchroRep_inv_eq_self)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_orthchrorep_inv_eq_self : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Eq (MonoidHom.instFunLike.coe LorentzGroup.orthchroRep Λ)
--     (MonoidHom.instFunLike.coe LorentzGroup.orthchroRep (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ))

-- Source: PhysLean (minkowskiMatrix.dual)
/-- The dual of a matrix with respect to the Minkowski metric.
A suitable name for this construction is the Minkowski dual.  -/
axiom minkowskimatrix_dual :
  {d : Nat} →
  Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real → Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real

-- Source: PhysLean (LorentzGroup.generalizedBoost)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_generalizedboost : {d : Nat} → (Lorentz.Velocity d).Elem → (Lorentz.Velocity d).Elem → (LorentzGroup d).Elem

-- Source: PhysLean (LorentzGroup.stepFunction.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_stepfunction_eq_1 : ∀ (t : Real), Eq (LorentzGroup.stepFunction t) (ite (Real.instLE.le t (-1)) (-1) (ite (Real.instLE.le 1 t) 1 t))

-- Source: PhysLean (LorentzGroup.detRep_on_connected_component)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_detrep_on_connected_component : ∀ {d : Nat} {Λ Λ' : (LorentzGroup d).Elem},
--   Set.instMembership.mem (connectedComponent Λ) Λ' →
--     Eq (MonoidHom.instFunLike.coe LorentzGroup.detRep Λ) (MonoidHom.instFunLike.coe LorentzGroup.detRep Λ')

-- Source: PhysLean (SpaceTime.tensorDeriv.eq_1)
-- [complex signature, not re-axiomatized]
-- spacetime_tensorderiv_eq_1 : ∀ {d : Nat} {M : Type} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] (f : SpaceTime d → M)
--   (x : SpaceTime d),
--   Eq (SpaceTime.tensorDeriv f x)
--     (Finset.univ.sum fun μ =>
--       TensorProduct.tmul Real (Module.Basis.instFunLike.coe Lorentz.CoVector.basis μ) (SpaceTime.deriv μ f x))

-- Source: PhysLean (LorentzGroup.isOrthochronous_mul_iff)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_isorthochronous_mul_iff : ∀ {d : Nat} {Λ Λ' : (LorentzGroup d).Elem},
--   Iff (LorentzGroup.IsOrthochronous (instHMul.hMul Λ Λ'))
--     (Eq (LorentzGroup.IsOrthochronous Λ) (LorentzGroup.IsOrthochronous Λ'))

-- Source: PhysLean (LorentzGroup.detRep_apply)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_detrep_apply : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Eq (MonoidHom.instFunLike.coe LorentzGroup.detRep Λ) (ContinuousMap.instFunLike.coe LorentzGroup.detContinuous Λ)

-- Source: PhysLean (Lorentz.Vector.tensorial)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_tensorial : {d : Nat} →
--   (realLorentzTensor d).Tensorial (Matrix.vecCons realLorentzTensor.Color.up Matrix.vecEmpty) (Lorentz.Vector d)

-- Source: PhysLean (Lorentz.contrContrContractField.as_sum)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_as_sum : ∀ {d : Nat} (x y : (Lorentz.Contr d).V.carrier),
--   Eq (LinearMap.instFunLike.coe Lorentz.contrContrContractField (TensorProduct.tmul Real x y))
--     (instHSub.hSub (instHMul.hMul (x.val (Sum.inl 0)) (y.val (Sum.inl 0)))
--       (Finset.univ.sum fun i => instHMul.hMul (x.val (Sum.inr i)) (y.val (Sum.inr i))))

-- Source: PhysLean (SpaceTime.instIsOpenPosMeasureVolume)
-- [complex signature, not re-axiomatized]
-- spacetime_instisopenposmeasurevolume : ∀ {d : Nat}, SpaceTime.instMeasureSpace.volume.IsOpenPosMeasure

-- Source: PhysLean (Lorentz.CoVector.toTensor_symm_pure)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_totensor_symm_pure : ∀ {d : Nat}
--   (p : TensorSpecies.Tensor.Pure (realLorentzTensor d) (Matrix.vecCons realLorentzTensor.Color.down Matrix.vecEmpty))
--   (i : Sum (Fin 1) (Fin d)),
--   Eq (EquivLike.toFunLike.coe Lorentz.CoVector.tensorial.toTensor.symm p.toTensor i)
--     (Finsupp.instFunLike.coe (EquivLike.toFunLike.coe (Lorentz.coBasisFin d).repr (p 0))
--       (EquivLike.toFunLike.coe Lorentz.CoVector.indexEquiv.symm i 0))

-- Source: PhysLean (minkowskiMatrix.η_diag_ne_zero)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_η_diag_ne_zero : ∀ {d : Nat} {μ : Sum (Fin 1) (Fin d)}, Ne (minkowskiMatrix μ μ) 0

-- Source: PhysLean (Lorentz.Vector.apply_add)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_apply_add : ∀ {d : Nat} (v w : Lorentz.Vector d) (i : Sum (Fin 1) (Fin d)), Eq (instHAdd.hAdd v w i) (instHAdd.hAdd (v i) (w i))

-- Source: PhysLean (Lorentz.CoMod.toFin1dℝEquiv)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_tofin1dℝequiv : {d : Nat} → LinearEquiv (RingHom.id Real) (Lorentz.CoMod d) (Sum (Fin 1) (Fin d) → Real)

-- Source: PhysLean (LorentzGroup.isProper_mul)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_isproper_mul : ∀ {d : Nat} {Λ Λ' : (LorentzGroup d).Elem},
--   LorentzGroup.IsProper Λ → LorentzGroup.IsProper Λ' → LorentzGroup.IsProper (instHMul.hMul Λ Λ')

-- Source: PhysLean (SpaceTime.toTimeAndSpace_fderiv)
-- [complex signature, not re-axiomatized]
-- spacetime_totimeandspace_fderiv : ∀ {d : Nat} {c : SpeedOfLight} (x : SpaceTime d),
--   Eq (fderiv Real (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c)) x)
--     (SpaceTime.toTimeAndSpace c).toContinuousLinearMap

-- Source: PhysLean (SpaceTime.instMeasurableSpace)
-- [complex signature, not re-axiomatized]
-- spacetime_instmeasurablespace : {d : Nat} → MeasurableSpace (SpaceTime d)

-- Source: PhysLean (Lorentz.Vector.causalCharacter_invariant)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causalcharacter_invariant : ∀ {d : Nat} (p : Lorentz.Vector d) (Λ : (LorentzGroup d).Elem),
--   Eq (instHSMul.hSMul Λ p).causalCharacter p.causalCharacter

-- Source: PhysLean (realLorentzTensor.contrT_basis_repr_apply_eq_fin)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_contrt_basis_repr_apply_eq_fin : ∀ {n d : Nat} {c : Fin (instHAdd.hAdd (instHAdd.hAdd n 1) 1) → realLorentzTensor.Color}
--   {i j : Fin (instHAdd.hAdd (instHAdd.hAdd n 1) 1)} {h : And (Ne i j) (Eq ((realLorentzTensor d).τ (c i)) (c j))}
--   (t : (realLorentzTensor d).Tensor c)
--   (b : TensorSpecies.Tensor.ComponentIdx (Function.comp c (TensorSpecies.Tensor.Pure.dropPairEmb i j))),
--   Eq
--     (Finsupp.instFunLike.coe
--       (EquivLike.toFunLike.coe
--         (TensorSpecies.Tensor.basis (Function.comp c (TensorSpecies.Tensor.Pure.dropPairEmb i j))).repr
--         (LinearMap.instFunLike.coe (TensorSpecies.Tensor.contrT n i j h) t))
--       b)
--     (Finset.univ.sum fun x =>
--       Finsupp.instFunLike.coe (EquivLike.toFunLike.coe (TensorSpecies.Tensor.basis c).repr t)
--         (EquivLike.toFunLike.coe (TensorSpecies.Tensor.ComponentIdx.DropPairSection.ofFinEquiv ⋯ b)
--             { fst := Fin.cast ⋯ x, snd := Fin.cast ⋯ x }).val)

-- Source: PhysLean (Lorentz.Co.toContr)
-- [complex signature, not re-axiomatized]
-- lorentz_co_tocontr : (d : Nat) → Action.instCategory.Hom (Lorentz.Co d) (Lorentz.Contr d)

-- Source: PhysLean (minkowskiMatrix.sq)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_sq : ∀ {d : Nat}, Eq (instHMul.hMul minkowskiMatrix minkowskiMatrix) 1

-- Source: PhysLean (complexLorentzTensor.altRightMetric_antisymm)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altrightmetric_antisymm : Eq
--   (EquivLike.toFunLike.coe
--     (TensorSpecies.Tensorial.self complexLorentzTensor
--         (Matrix.vecCons complexLorentzTensor.Color.downR
--           (Matrix.vecCons complexLorentzTensor.Color.downR Matrix.vecEmpty))).toTensor
--     complexLorentzTensor.altRightMetric)
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT (Matrix.vecCons 1 (Matrix.vecCons 0 Matrix.vecEmpty)) ⋯)
--     (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg
--       (EquivLike.toFunLike.coe
--         (TensorSpecies.Tensorial.self complexLorentzTensor
--             (Matrix.vecCons complexLorentzTensor.Color.downR
--               (Matrix.vecCons complexLorentzTensor.Color.downR Matrix.vecEmpty))).toTensor
--         complexLorentzTensor.altRightMetric)))

-- Source: PhysLean (Lorentz.ContrMod.instAddCommMonoid)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_instaddcommmonoid : {d : Nat} → AddCommMonoid (Lorentz.ContrMod d)

-- Source: PhysLean (complexLorentzTensor.Color.upL.sizeOf_spec)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_color_upl_sizeof_spec : Eq (complexLorentzTensor.Color._sizeOf_inst.sizeOf complexLorentzTensor.Color.upL) 1

-- Source: PhysLean (SpaceTime.space_equivariant)
-- [complex signature, not re-axiomatized]
-- spacetime_space_equivariant : InformalLemma

-- Source: PhysLean (LorentzGroup.IsOrthochronous.iff_in_orthchroRep_ker)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_isorthochronous_iff_in_orthchrorep_ker : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Iff (LorentzGroup.IsOrthochronous Λ) (SetLike.instMembership.mem LorentzGroup.orthchroRep.ker Λ)

-- Source: PhysLean (Lorentz.complexContrBasisFin4_apply_succ)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcontrbasisfin4_apply_succ : ∀ (i : Fin 3),
--   Eq (Module.Basis.instFunLike.coe Lorentz.complexContrBasisFin4 i.succ)
--     (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr i))

-- Source: PhysLean (CliffordAlgebra.ι)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_ι : {R : Type u_1} →
--   [inst : CommRing R] →
--     {M : Type u_2} →
--       [inst_1 : AddCommGroup M] →
--         [inst_2 : Module R M] → (Q : QuadraticForm R M) → LinearMap (RingHom.id R) M (CliffordAlgebra Q)

-- Source: PhysLean (Lorentz.coContrContraction_basis')
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrcontraction_basis' : ∀ (i j : Sum (Fin 1) (Fin 3)),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.coContrContraction.hom)
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasis i)
--         (Module.Basis.instFunLike.coe Lorentz.complexContrBasis j)))
--     (ite (Eq i j) 1 0)

-- Source: PhysLean (LorentzGroup.boost.congr_simp)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_congr_simp : ∀ {d : Nat} (i i_1 : Fin d),
--   Eq i i_1 →
--     ∀ (β β_1 : Real) (e_β : Eq β β_1) (hβ : Real.instLT.lt (abs β) 1),
--       Eq (LorentzGroup.boost i β hβ) (LorentzGroup.boost i_1 β_1 ⋯)

-- Source: PhysLean (SpaceTime.distTimeSlice)
-- [complex signature, not re-axiomatized]
-- spacetime_disttimeslice : {M : Type} →
--   {d : Nat} →
--     [inst : NormedAddCommGroup M] →
--       [inst_1 : NormedSpace Real M] →
--         optParam SpeedOfLight 1 →
--           ContinuousLinearEquiv (RingHom.id Real) (Distribution Real (SpaceTime d) M)
--             (Distribution Real (Prod Time (Space d)) M)

-- Source: PhysLean (Lorentz.complexCoBasisFin4_apply_one)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcobasisfin4_apply_one : Eq (Module.Basis.instFunLike.coe Lorentz.complexCoBasisFin4 1)
--   (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 0))

-- Source: PhysLean (complexLorentzTensor.Color.upR.sizeOf_spec)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_color_upr_sizeof_spec : Eq (complexLorentzTensor.Color._sizeOf_inst.sizeOf complexLorentzTensor.Color.upR) 1

-- Source: PhysLean (Lorentz.Velocity.instZeroElemVector)
-- [complex signature, not re-axiomatized]
-- lorentz_velocity_instzeroelemvector : {d : Nat} → Zero (Lorentz.Velocity d).Elem

-- Source: PhysLean (LorentzGroup.genBoostAux₂_toMatrix_apply)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_genboostaux₂_tomatrix_apply : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem) (μ ν : Sum (Fin 1) (Fin d)),
--   Eq
--     (EquivLike.toFunLike.coe (LinearMap.toMatrix Lorentz.Vector.basis Lorentz.Vector.basis)
--       (LorentzGroup.genBoostAux₂ u v) μ ν)
--     (instHMul.hMul (minkowskiMatrix ν ν)
--       (instHDiv.hDiv
--         (instHMul.hMul (Real.instNeg.neg (instHAdd.hAdd (u.val μ) (v.val μ))) (instHAdd.hAdd (u.val ν) (v.val ν)))
--         (instHAdd.hAdd 1
--           (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct u.val)
--             v.val))))

-- Source: PhysLean (Lorentz.CoMod.instAddCommMonoid)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_instaddcommmonoid : {d : Nat} → AddCommMonoid (Lorentz.CoMod d)

-- Source: PhysLean (Lorentz.Vector.smul_zero)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_smul_zero : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem), Eq (instHSMul.hSMul Λ 0) 0

-- Source: PhysLean (Lorentz.Vector.pastLightConeBoundary)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_pastlightconeboundary : {d : Nat} → Lorentz.Vector d → Set (Lorentz.Vector d)

-- Source: PhysLean (SpaceTime.distDeriv_commute)
-- [complex signature, not re-axiomatized]
-- spacetime_distderiv_commute : ∀ {M : Type} {d : Nat} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] (μ ν : Sum (Fin 1) (Fin d))
--   (f : Distribution Real (SpaceTime d) M),
--   Eq (LinearMap.instFunLike.coe (SpaceTime.distDeriv μ) (LinearMap.instFunLike.coe (SpaceTime.distDeriv ν) f))
--     (LinearMap.instFunLike.coe (SpaceTime.distDeriv ν) (LinearMap.instFunLike.coe (SpaceTime.distDeriv μ) f))

-- Source: PhysLean (Lorentz.contrCoUnitVal.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcounitval_eq_1 : Eq Lorentz.contrCoUnitVal (EquivLike.toFunLike.coe Lorentz.contrCoToMatrix.symm 1)

-- Source: PhysLean (LorentzGroup.toComplex_transpose_mul_minkowskiMatrix_mul_self)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_tocomplex_transpose_mul_minkowskimatrix_mul_self : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Eq
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--       (instHMul.hMul (MonoidHom.instFunLike.coe LorentzGroup.toComplex Λ).transpose
--         (minkowskiMatrix.map (RingHom.instFunLike.coe Complex.ofRealHom)))
--       (MonoidHom.instFunLike.coe LorentzGroup.toComplex Λ))
--     (minkowskiMatrix.map (RingHom.instFunLike.coe Complex.ofRealHom))

-- Source: PhysLean (Lorentz.contrMetricVal.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmetricval_eq_1 : Eq Lorentz.contrMetricVal
--   (EquivLike.toFunLike.coe Lorentz.contrContrToMatrix.symm
--     (minkowskiMatrix.map (RingHom.instFunLike.coe Complex.ofRealHom)))

-- Source: PhysLean (SpaceTime.toTimeAndSpace_symm_fderiv)
-- [complex signature, not re-axiomatized]
-- spacetime_totimeandspace_symm_fderiv : ∀ {d : Nat} {c : SpeedOfLight} (x : Prod Time (Space d)),
--   Eq (fderiv Real (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c).symm) x)
--     (SpaceTime.toTimeAndSpace c).symm.toContinuousLinearMap

-- Source: PhysLean (LorentzGroup.generalizedBoost_in_connected_component_of_id)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_generalizedboost_in_connected_component_of_id : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem),
--   Set.instMembership.mem (connectedComponent 1) (LorentzGroup.generalizedBoost u v)

-- Source: PhysLean (Lorentz.contrMetricVal)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmetricval : (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexContr).V.carrier

-- Source: PhysLean (SpaceTime.toTimeAndSpace)
-- [complex signature, not re-axiomatized]
-- spacetime_totimeandspace : {d : Nat} → optParam SpeedOfLight 1 → ContinuousLinearEquiv (RingHom.id Real) (SpaceTime d) (Prod Time (Space d))

-- Source: PhysLean (SpaceTime.toTimeAndSpace_symm_apply_inr)
-- [complex signature, not re-axiomatized]
-- spacetime_totimeandspace_symm_apply_inr : ∀ {d : Nat} {c : SpeedOfLight} (t : Time) (x : Space d) (i : Fin d),
--   Eq (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c).symm { fst := t, snd := x } (Sum.inr i)) (x.val i)

-- Source: PhysLean (complexLorentzTensor.altRightRightUnit.eq_1)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altrightrightunit_eq_1 : Eq complexLorentzTensor.altRightRightUnit (TensorSpecies.unitTensor complexLorentzTensor.Color.upR)

-- Source: PhysLean (Lorentz.complexContrBasisFin4)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcontrbasisfin4 : Module.Basis (Fin 4) Complex Lorentz.complexContr.V.carrier

-- Source: PhysLean (Lorentz.«term_*ᵥ_»)
-- [complex signature, not re-axiomatized]
-- lorentz_«term_*ᵥ_» : Lean.TrailingParserDescr

-- Source: PhysLean (complexLorentzTensor.contrBispinorDown)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrbispinordown : complexLorentzTensor.Tensor (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty) →
--   complexLorentzTensor.Tensor
--     (Matrix.vecCons complexLorentzTensor.Color.downL (Matrix.vecCons complexLorentzTensor.Color.downR Matrix.vecEmpty))

-- Source: PhysLean (LorentzGroup.orthchroMapReal_on_not_IsOrthochronous)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_orthchromapreal_on_not_isorthochronous : ∀ {d : Nat} {Λ : (LorentzGroup d).Elem},
--   Not (LorentzGroup.IsOrthochronous Λ) → Eq (ContinuousMap.instFunLike.coe LorentzGroup.orthchroMapReal Λ) (-1)

-- Source: PhysLean (SpaceTime.tensorDeriv_toTensor_basis_repr)
-- [complex signature, not re-axiomatized]
-- spacetime_tensorderiv_totensor_basis_repr : ∀ {n d : Nat} {c : Fin n → realLorentzTensor.Color} {M : Type} [inst : NormedAddCommGroup M]
--   [inst_1 : NormedSpace Real M] [inst_2 : (realLorentzTensor d).Tensorial c M] [T2Space M] {f : SpaceTime d → M},
--   Differentiable Real f →
--     ∀ (x : SpaceTime d)
--       (b :
--         TensorSpecies.Tensor.ComponentIdx (Fin.append (Matrix.vecCons realLorentzTensor.Color.down Matrix.vecEmpty) c)),
--       Eq
--         (Finsupp.instFunLike.coe
--           (EquivLike.toFunLike.coe
--             (TensorSpecies.Tensor.basis
--                 (Fin.append (Matrix.vecCons realLorentzTensor.Color.down Matrix.vecEmpty) c)).repr
--             (EquivLike.toFunLike.coe TensorSpecies.Tensorial.prod.toTensor (SpaceTime.tensorDeriv f x)))
--           b)
--         (SpaceTime.deriv
--           (EquivLike.toFunLike.coe Lorentz.CoVector.indexEquiv
--             (EquivLike.toFunLike.coe TensorSpecies.Tensor.ComponentIdx.prodEquiv b).fst)
--           (fun x =>
--             Finsupp.instFunLike.coe
--               (EquivLike.toFunLike.coe (TensorSpecies.Tensor.basis c).repr
--                 (EquivLike.toFunLike.coe inst_2.toTensor (f x)))
--               (EquivLike.toFunLike.coe TensorSpecies.Tensor.ComponentIdx.prodEquiv b).snd)
--           x)

-- Source: PhysLean (Lorentz.Vector.minkowskiProductMap_add_snd)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproductmap_add_snd : ∀ {d : Nat} (p q r : Lorentz.Vector d),
--   Eq (p.minkowskiProductMap (instHAdd.hAdd q r)) (instHAdd.hAdd (p.minkowskiProductMap q) (p.minkowskiProductMap r))

-- Source: PhysLean (Lorentz.Vector.CausalCharacter.lightLike.sizeOf_spec)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causalcharacter_lightlike_sizeof_spec : Eq (Lorentz.Vector.CausalCharacter._sizeOf_inst.sizeOf Lorentz.Vector.CausalCharacter.lightLike) 1

-- Source: PhysLean (realLorentzTensor.contrMetric_eq_fromConstPair)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_contrmetric_eq_fromconstpair : ∀ {d : Nat}, Eq (realLorentzTensor.contrMetric d) (TensorSpecies.Tensor.fromConstPair (Lorentz.preContrMetric d))

-- Source: PhysLean (Lorentz.coContrContraction_hom_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrcontraction_hom_tmul : ∀ (φ : Lorentz.complexCo.V.carrier) (ψ : Lorentz.complexContr.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.coContrContraction.hom)
--       (TensorProduct.tmul Complex φ ψ))
--     (dotProduct (Lorentz.CoℂModule.toFin13ℂ φ) (Lorentz.ContrℂModule.toFin13ℂ ψ))

-- Source: PhysLean (Lorentz.ContrMod.mulVec_val)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_mulvec_val : ∀ {d : Nat} (M : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real) (v : Lorentz.ContrMod d),
--   Eq (Lorentz.ContrMod.mulVec M v).val (M.mulVec v.val)

-- Source: PhysLean (complexLorentzTensor.altLeftMetric_eq_basis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altleftmetric_eq_basis : Eq complexLorentzTensor.altLeftMetric
--   (instHSub.hSub
--     (Module.Basis.instFunLike.coe
--       (TensorSpecies.Tensor.basis
--         (Matrix.vecCons complexLorentzTensor.Color.downL
--           (Matrix.vecCons complexLorentzTensor.Color.downL Matrix.vecEmpty)))
--       fun x =>
--       complexLorentzTensor.coMetric_eq_basis.match_1
--         (fun x =>
--           Fin
--             (complexLorentzTensor.repDim
--               (Matrix.vecCons complexLorentzTensor.Color.downL
--                 (Matrix.vecCons complexLorentzTensor.Color.downL Matrix.vecEmpty) x)))
--         x (fun _ => 0) fun _ => 1)
--     (Module.Basis.instFunLike.coe
--       (TensorSpecies.Tensor.basis
--         (Matrix.vecCons complexLorentzTensor.Color.downL
--           (Matrix.vecCons complexLorentzTensor.Color.downL Matrix.vecEmpty)))
--       fun x =>
--       complexLorentzTensor.coMetric_eq_basis.match_1
--         (fun x =>
--           Fin
--             (complexLorentzTensor.repDim
--               (Matrix.vecCons complexLorentzTensor.Color.downL
--                 (Matrix.vecCons complexLorentzTensor.Color.downL Matrix.vecEmpty) x)))
--         x (fun _ => 1) fun _ => 0))

-- Source: PhysLean (Lorentz.SL2C.inverse_coe)
axiom lorentz_sl2c_inverse_coe :
  ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
  Eq (Matrix.inv.inv M.val) (Matrix.SpecialLinearGroup.hasInv.inv M).val

-- Source: PhysLean (Lorentz.CoVector.smul_zero)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_smul_zero : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem), Eq (instHSMul.hSMul Λ 0) 0

-- Source: PhysLean (Lorentz.Vector.CausalCharacter.spaceLike.elim)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causalcharacter_spacelike_elim : {motive : Lorentz.Vector.CausalCharacter → Sort u} →
--   (t : Lorentz.Vector.CausalCharacter) → Eq t.ctorIdx 2 → motive Lorentz.Vector.CausalCharacter.spaceLike → motive t

-- Source: PhysLean (LorentzGroup.Rotations)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_rotations : (d : Nat) → Subgroup (LorentzGroup d).Elem

-- Source: PhysLean (minkowskiMatrix.dual_apply)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_dual_apply : ∀ {d : Nat} (Λ : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real) (μ ν : Sum (Fin 1) (Fin d)),
--   Eq (minkowskiMatrix.dual Λ μ ν) (instHMul.hMul (instHMul.hMul (minkowskiMatrix μ μ) (Λ ν μ)) (minkowskiMatrix ν ν))

-- Source: PhysLean (LorentzGroup.transpose)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_transpose : {d : Nat} → (LorentzGroup d).Elem → (LorentzGroup d).Elem

-- Source: PhysLean (LorentzGroup.restricted)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_restricted : (d : Nat) → Subgroup (LorentzGroup d).Elem

-- Source: PhysLean (Lorentz.Vector.CausalCharacter.spaceLike.sizeOf_spec)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causalcharacter_spacelike_sizeof_spec : Eq (Lorentz.Vector.CausalCharacter._sizeOf_inst.sizeOf Lorentz.Vector.CausalCharacter.spaceLike) 1

-- Source: PhysLean (Lorentz.Velocity.minkowskiProduct_continuous_snd)
-- [complex signature, not re-axiomatized]
-- lorentz_velocity_minkowskiproduct_continuous_snd : ∀ {d : Nat} (u : Lorentz.Vector d),
--   Continuous fun x =>
--     ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct u) x.val

-- Source: PhysLean (Lorentz.CoVector.instCoeFunForallSumFinOfNatNatReal)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_instcoefunforallsumfinofnatnatreal : {d : Nat} → CoeFun (Lorentz.CoVector d) fun x => Sum (Fin 1) (Fin d) → Real

-- Source: PhysLean (Lorentz.ContrMod.val)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_val : {d : Nat} → Lorentz.ContrMod d → Sum (Fin 1) (Fin d) → Real

-- Source: PhysLean (complexLorentzTensor.termη')
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_termη' : Lean.ParserDescr

-- Source: PhysLean (Lorentz.coMetricVal)
-- [complex signature, not re-axiomatized]
-- lorentz_cometricval : (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexCo).V.carrier

-- Source: PhysLean (SpaceTime.distTensorDeriv_apply)
-- [complex signature, not re-axiomatized]
-- spacetime_disttensorderiv_apply : ∀ {M : Type} {d : Nat} [inst : NormedAddCommGroup M] [inst_1 : InnerProductSpace Real M]
--   [inst_2 : FiniteDimensional Real M] (f : Distribution Real (SpaceTime d) M) (ε : SchwartzMap (SpaceTime d) Real),
--   Eq (ContinuousLinearMap.funLike.coe (LinearMap.instFunLike.coe SpaceTime.distTensorDeriv f) ε)
--     (Finset.univ.sum fun μ =>
--       TensorProduct.tmul Real (Module.Basis.instFunLike.coe Lorentz.CoVector.basis μ)
--         (ContinuousLinearMap.funLike.coe (LinearMap.instFunLike.coe (SpaceTime.distDeriv μ) f) ε))

-- Source: PhysLean (LorentzGroup.toProd_injective)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_toprod_injective : ∀ {d : Nat}, Function.Injective (MonoidHom.instFunLike.coe LorentzGroup.toProd)

-- Source: PhysLean (Lorentz.preContrMetricVal_expand_tmul_minkowskiMatrix)
-- [complex signature, not re-axiomatized]
-- lorentz_precontrmetricval_expand_tmul_minkowskimatrix : ∀ {d : Nat},
--   Eq (Lorentz.preContrMetricVal d)
--     (Finset.univ.sum fun i =>
--       instHSMul.hSMul (minkowskiMatrix i i)
--         (TensorProduct.tmul Real (Module.Basis.instFunLike.coe (Lorentz.contrBasis d) i)
--           (Module.Basis.instFunLike.coe (Lorentz.contrBasis d) i)))

-- Source: PhysLean (Lorentz.CoℂModule.toFin13ℂEquiv_symm_apply_val)
-- [complex signature, not re-axiomatized]
-- lorentz_coℂmodule_tofin13ℂequiv_symm_apply_val : ∀ (a : Sum (Fin 1) (Fin 3) → Complex) (a_1 : Sum (Fin 1) (Fin 3)),
--   Eq ((EquivLike.toFunLike.coe Lorentz.CoℂModule.toFin13ℂEquiv.symm a).val a_1) (a a_1)

-- Source: PhysLean (complexLorentzTensor.antiSymm_contr_symm)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_antisymm_contr_symm : ∀
--   {A :
--     complexLorentzTensor.Tensor
--       (Matrix.vecCons complexLorentzTensor.Color.up (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty))}
--   {S :
--     complexLorentzTensor.Tensor
--       (Matrix.vecCons complexLorentzTensor.Color.down
--         (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty))},
--   Eq
--       (EquivLike.toFunLike.coe
--         (TensorSpecies.Tensorial.self complexLorentzTensor
--             (Matrix.vecCons complexLorentzTensor.Color.up
--               (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty))).toTensor
--         A)
--       (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT (Matrix.vecCons 1 (Matrix.vecCons 0 Matrix.vecEmpty)) ⋯)
--         (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg
--           (EquivLike.toFunLike.coe
--             (TensorSpecies.Tensorial.self complexLorentzTensor
--                 (Matrix.vecCons complexLorentzTensor.Color.up
--                   (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty))).toTensor
--             A))) →
--     Eq
--         (EquivLike.toFunLike.coe
--           (TensorSpecies.Tensorial.self complexLorentzTensor
--               (Matrix.vecCons complexLorentzTensor.Color.down
--                 (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty))).toTensor
--           S)
--         (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT (Matrix.vecCons 1 (Matrix.vecCons 0 Matrix.vecEmpty)) ⋯)
--           (EquivLike.toFunLike.coe
--             (TensorSpecies.Tensorial.self complexLorentzTensor
--                 (Matrix.vecCons complexLorentzTensor.Color.down
--                   (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty))).toTensor
--             S)) →
--       Eq
--         (LinearMap.instFunLike.coe (TensorSpecies.Tensor.contrT 0 0 1 ⋯)
--           (LinearMap.instFunLike.coe (TensorSpecies.Tensor.contrT 2 1 3 ⋯)
--             (LinearMap.instFunLike.coe
--               (LinearMap.instFunLike.coe TensorSpecies.Tensor.prodT
--                 (EquivLike.toFunLike.coe
--                   (TensorSpecies.Tensorial.self complexLorentzTensor
--                       (Matrix.vecCons complexLorentzTensor.Color.up
--                         (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty))).toTensor
--                   A))
--               (EquivLike.toFunLike.coe
--                 (TensorSpecies.Tensorial.self complexLorentzTensor
--                     (Matrix.vecCons complexLorentzTensor.Color.down
--                       (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty))).toTensor
--                 S))))
--         (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT Matrix.vecEmpty ⋯)
--           (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg
--             (LinearMap.instFunLike.coe (TensorSpecies.Tensor.contrT 0 0 1 ⋯)
--               (LinearMap.instFunLike.coe (TensorSpecies.Tensor.contrT 2 1 3 ⋯)
--                 (LinearMap.instFunLike.coe
--                   (LinearMap.instFunLike.coe TensorSpecies.Tensor.prodT
--                     (EquivLike.toFunLike.coe
--                       (TensorSpecies.Tensorial.self complexLorentzTensor
--                           (Matrix.vecCons complexLorentzTensor.Color.up
--                             (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty))).toTensor
--                       A))
--                   (EquivLike.toFunLike.coe
--                     (TensorSpecies.Tensorial.self complexLorentzTensor
--                         (Matrix.vecCons complexLorentzTensor.Color.down
--                           (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty))).toTensor
--                     S))))))

-- Source: PhysLean (Lorentz.contrCoContract_basis)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcocontract_basis : ∀ {d : Nat} (i j : Sum (Fin 1) (Fin d)),
--   Eq
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom Lorentz.contrCoContract.hom)
--       (TensorProduct.tmul Real (Module.Basis.instFunLike.coe (Lorentz.contrBasis d) i)
--         (Module.Basis.instFunLike.coe (Lorentz.coBasis d) j)))
--     (ite (Eq i j) 1 0)

-- Source: PhysLean (Lorentz.coContrToMatrixRe_ρ_symm)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrtomatrixre_ρ_symm : ∀ {d : Nat} (v : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real) (M : (LorentzGroup d).Elem),
--   Eq
--     (LinearMap.instFunLike.coe
--       (TensorProduct.map (MonoidHom.instFunLike.coe (Lorentz.Co d).ρ M)
--         (MonoidHom.instFunLike.coe (Lorentz.Contr d).ρ M))
--       (EquivLike.toFunLike.coe Lorentz.coContrToMatrixRe.symm v))
--     (EquivLike.toFunLike.coe Lorentz.coContrToMatrixRe.symm
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--         (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.inv.inv M.val).transpose v) M.val.transpose))

-- Source: PhysLean (CliffordAlgebra.lift_comp_ι)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_lift_comp_ι : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   {Q : QuadraticForm R M} {A : Type u_3} [inst_3 : Semiring A] [inst_4 : Algebra R A]
--   (g : AlgHom R (CliffordAlgebra Q) A),
--   Eq (EquivLike.toFunLike.coe (CliffordAlgebra.lift Q) ⟨g.toLinearMap.comp (CliffordAlgebra.ι Q), ⋯⟩) g

-- Source: PhysLean (Lorentz.CoVector.tensorial)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_tensorial : {d : Nat} →
--   (realLorentzTensor d).Tensorial (Matrix.vecCons realLorentzTensor.Color.down Matrix.vecEmpty) (Lorentz.CoVector d)

-- Source: PhysLean (Lorentz.contrContrToMatrixRe.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrtomatrixre_eq_1 : ∀ {d : Nat},
--   Eq Lorentz.contrContrToMatrixRe
--     ((((Lorentz.contrBasis d).tensorProduct (Lorentz.contrBasis d)).repr.trans
--           (Finsupp.linearEquivFunOnFinite Real Real (Prod (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d))))).trans
--       (LinearEquiv.curry Real Real (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d))))

-- Source: PhysLean (Lorentz.ContrMod.mulVec)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_mulvec : {d : Nat} → Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real → Lorentz.ContrMod d → Lorentz.ContrMod d

-- Source: PhysLean (Lorentz.ContrℂModule.lorentzGroupRep)
-- [complex signature, not re-axiomatized]
-- lorentz_contrℂmodule_lorentzgrouprep : Representation Complex (LorentzGroup 3).Elem Lorentz.ContrℂModule

-- Source: PhysLean (LorentzGroup.genBoostAux₂.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_genboostaux₂_eq_1 : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem),
--   Eq (LorentzGroup.genBoostAux₂ u v)
--     {
--       toFun := fun x =>
--         instHSMul.hSMul
--           (Real.instNeg.neg
--             (instHDiv.hDiv
--               (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct x)
--                 (instHAdd.hAdd u.val v.val))
--               (instHAdd.hAdd 1
--                 (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct u.val)
--                   v.val))))
--           (instHAdd.hAdd u.val v.val),
--       map_add' := ⋯, map_smul' := ⋯ }

-- Source: PhysLean (realLorentzTensor.coMetric_eq_fromConstPair)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_cometric_eq_fromconstpair : ∀ {d : Nat}, Eq (realLorentzTensor.coMetric d) (TensorSpecies.Tensor.fromConstPair (Lorentz.preCoMetric d))

-- Source: PhysLean (minkowskiMatrix.dual_dual)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_dual_dual : ∀ {d : Nat}, Function.Involutive minkowskiMatrix.dual

-- Source: PhysLean (Lorentz.complexCoBasisFin4_apply_two)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcobasisfin4_apply_two : Eq (Module.Basis.instFunLike.coe Lorentz.complexCoBasisFin4 2)
--   (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 1))

-- Source: PhysLean (Lorentz.Vector.adjoint.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_adjoint_eq_1 : ∀ {d : Nat} (f : LinearMap (RingHom.id Real) (Lorentz.Vector d) (Lorentz.Vector d)),
--   Eq (Lorentz.Vector.adjoint f)
--     (EquivLike.toFunLike.coe (LinearMap.toMatrix Lorentz.Vector.basis Lorentz.Vector.basis).symm
--       (minkowskiMatrix.dual (EquivLike.toFunLike.coe (LinearMap.toMatrix Lorentz.Vector.basis Lorentz.Vector.basis) f)))

-- Source: PhysLean (complexLorentzTensor.rightAltRightUnit.eq_1)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_rightaltrightunit_eq_1 : Eq complexLorentzTensor.rightAltRightUnit (TensorSpecies.unitTensor complexLorentzTensor.Color.downR)

-- Source: PhysLean (Lorentz.Vector.basis_eq_map_tensor_basis)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_basis_eq_map_tensor_basis : ∀ {d : Nat},
--   Eq Lorentz.Vector.basis
--     (((TensorSpecies.Tensor.basis (Matrix.vecCons realLorentzTensor.Color.up Matrix.vecEmpty)).map
--           Lorentz.Vector.tensorial.toTensor.symm).reindex
--       Lorentz.Vector.indexEquiv)

-- Source: PhysLean (LorentzGroup.generalizedBoost_apply_fst)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_generalizedboost_apply_fst : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem), Eq (instHSMul.hSMul (LorentzGroup.generalizedBoost u v) u.val) v.val

-- Source: PhysLean (Lorentz.preCoMetricVal.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_precometricval_eq_1 : ∀ (d : Nat), Eq (Lorentz.preCoMetricVal d) (EquivLike.toFunLike.coe Lorentz.coCoToMatrixRe.symm minkowskiMatrix)

-- Source: PhysLean (LorentzGroup.orthchroMap.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_orthchromap_eq_1 : ∀ {d : Nat},
--   Eq LorentzGroup.orthchroMap
--     (LorentzGroup.coeForℤ₂.comp
--       { toFun := fun Λ => ⟨ContinuousMap.instFunLike.coe LorentzGroup.orthchroMapReal Λ, ⋯⟩, continuous_toFun := ⋯ })

-- Source: PhysLean (complexLorentzTensor.altLeftLeftUnit_eq_fromConstPair)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altleftleftunit_eq_fromconstpair : Eq complexLorentzTensor.altLeftLeftUnit (TensorSpecies.Tensor.fromConstPair Fermion.altLeftLeftUnit)

-- Source: PhysLean (Lorentz.contrCoToMatrix_symm_expand_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcotomatrix_symm_expand_tmul : ∀ (M : Matrix (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3)) Complex),
--   Eq (EquivLike.toFunLike.coe Lorentz.contrCoToMatrix.symm M)
--     (Finset.univ.sum fun i =>
--       Finset.univ.sum fun j =>
--         instHSMul.hSMul (M i j)
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasis i)
--             (Module.Basis.instFunLike.coe Lorentz.complexCoBasis j)))

-- Source: PhysLean (Lorentz.Vector.timelike_time_dominates_space)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_timelike_time_dominates_space : ∀ {d : Nat} {v : Lorentz.Vector d},
--   Eq v.causalCharacter Lorentz.Vector.CausalCharacter.timeLike →
--     Real.instLT.lt ((PiLp.innerProductSpace fun x => Real).inner Real v.spatialPart v.spatialPart)
--       (instHMul.hMul v.timeComponent v.timeComponent)

-- Source: PhysLean (CliffordAlgebra.ι_mul_ι_mul_ι)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_ι_mul_ι_mul_ι : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   {Q : QuadraticForm R M} (a b : M),
--   Eq
--     (instHMul.hMul
--       (instHMul.hMul (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) a)
--         (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) b))
--       (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) a))
--     (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q)
--       (instHSub.hSub (instHSMul.hSMul (QuadraticMap.polar (QuadraticMap.instFunLike.coe Q) a b) a)
--         (instHSMul.hSMul (QuadraticMap.instFunLike.coe Q a) b)))

-- Source: PhysLean (realLorentzTensor.Color.ctorElimType)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_color_ctorelimtype : {motive : realLorentzTensor.Color → Sort u} → Nat → Sort (max 1 u)

-- Source: PhysLean (Lorentz.coBasis_toFin1dℝ)
-- [complex signature, not re-axiomatized]
-- lorentz_cobasis_tofin1dℝ : ∀ {d : Nat} (i : Sum (Fin 1) (Fin d)),
--   Eq (Lorentz.CoMod.toFin1dℝ (Module.Basis.instFunLike.coe (Lorentz.coBasis d) i)) (Pi.single i 1)

-- Source: PhysLean (Lorentz.contrMetricVal_expand_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmetricval_expand_tmul : Eq Lorentz.contrMetricVal
--   (instHSub.hSub
--     (instHSub.hSub
--       (instHSub.hSub
--         (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inl 0))
--           (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inl 0)))
--         (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 0))
--           (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 0))))
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 1))
--         (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 1))))
--     (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 2))
--       (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 2))))

-- Source: PhysLean (Lorentz.ContrMod.stdBasis_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_stdbasis_apply : ∀ {d : Nat} (μ ν : Sum (Fin 1) (Fin d)),
--   Eq ((Module.Basis.instFunLike.coe Lorentz.ContrMod.stdBasis μ).val ν) (ite (Eq μ ν) 1 0)

-- Source: PhysLean (Lorentz.contrContrContractField.self_parity_eq_zero_iff)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_self_parity_eq_zero_iff : ∀ {d : Nat} (y : (Lorentz.Contr d).V.carrier),
--   Iff
--     (Eq
--       (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--         (TensorProduct.tmul Real y
--           (LinearMap.instFunLike.coe (MonoidHom.instFunLike.coe (Lorentz.Contr d).ρ LorentzGroup.parity) y)))
--       0)
--     (Eq y 0)

-- Source: PhysLean (Lorentz.Velocity.zero)
-- [complex signature, not re-axiomatized]
-- lorentz_velocity_zero : {d : Nat} → (Lorentz.Velocity d).Elem

-- Source: PhysLean (Lorentz.complexContrBasisFin4_apply_two)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcontrbasisfin4_apply_two : Eq (Module.Basis.instFunLike.coe Lorentz.complexContrBasisFin4 2)
--   (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 1))

-- Source: PhysLean (Lorentz.CoVector.basis.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_basis_eq_1 : ∀ {d : Nat}, Eq Lorentz.CoVector.basis (Pi.basisFun Real (Sum (Fin 1) (Fin d)))

-- Source: PhysLean (Lorentz.SL2C.toSelfAdjointMap_apply_coe)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_toselfadjointmap_apply_coe : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex)
--   (A : Subtype fun x => SetLike.instMembership.mem (selfAdjoint (Matrix (Fin 2) (Fin 2) Complex)) x),
--   Eq (LinearMap.instFunLike.coe (Lorentz.SL2C.toSelfAdjointMap M) A).val
--     (instHMul.hMul (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul M.val A.val) M.val.conjTranspose)

-- Source: PhysLean (Lorentz.coCoToMatrixRe)
-- [complex signature, not re-axiomatized]
-- lorentz_cocotomatrixre : {d : Nat} →
--   LinearEquiv (RingHom.id Real) (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Co d)).V.carrier
--     (Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real)

-- Source: PhysLean (CliffordAlgebra.map_id)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_map_id : ∀ {R : Type u_1} [inst : CommRing R] {M₁ : Type u_4} [inst_1 : AddCommGroup M₁] [inst_2 : Module R M₁]
--   (Q₁ : QuadraticForm R M₁), Eq (CliffordAlgebra.map (QuadraticMap.Isometry.id Q₁)) (AlgHom.id R (CliffordAlgebra Q₁))

-- Source: PhysLean (minkowskiMatrix.termη)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_termη : Lean.ParserDescr

-- Source: PhysLean (SpaceTime.properTime)
-- [complex signature, not re-axiomatized]
-- spacetime_propertime : {d : Nat} → SpaceTime d → SpaceTime d → Real

-- Source: PhysLean (LorentzGroup.detRep_continuous)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_detrep_continuous : ∀ {d : Nat}, Continuous (MonoidHom.instFunLike.coe LorentzGroup.detRep)

-- Source: PhysLean (CliffordAlgebra.hom_ext)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_hom_ext : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   {Q : QuadraticForm R M} {A : Type u_4} [inst_3 : Semiring A] [inst_4 : Algebra R A]
--   {f g : AlgHom R (CliffordAlgebra Q) A},
--   Eq (f.toLinearMap.comp (CliffordAlgebra.ι Q)) (g.toLinearMap.comp (CliffordAlgebra.ι Q)) → Eq f g

-- Source: PhysLean (LorentzGroup.neg_isOrthochronous_iff_not)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_neg_isorthochronous_iff_not : ∀ {d : Nat} {Λ : (LorentzGroup d).Elem},
--   Iff (LorentzGroup.IsOrthochronous (LorentzGroup.instNegElemMatrixSumFinOfNatNatReal.neg Λ))
--     (Not (LorentzGroup.IsOrthochronous Λ))

-- Source: PhysLean (complexLorentzTensor.leftAltLeftUnit_symm)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_leftaltleftunit_symm : Eq
--   (EquivLike.toFunLike.coe
--     (TensorSpecies.Tensorial.self complexLorentzTensor
--         (Matrix.vecCons complexLorentzTensor.Color.upL
--           (Matrix.vecCons complexLorentzTensor.Color.downL Matrix.vecEmpty))).toTensor
--     complexLorentzTensor.leftAltLeftUnit)
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT (Matrix.vecCons 1 (Matrix.vecCons 0 Matrix.vecEmpty)) ⋯)
--     (EquivLike.toFunLike.coe
--       (TensorSpecies.Tensorial.self complexLorentzTensor
--           (Matrix.vecCons complexLorentzTensor.Color.downL
--             (Matrix.vecCons complexLorentzTensor.Color.upL Matrix.vecEmpty))).toTensor
--       complexLorentzTensor.altLeftLeftUnit))

-- Source: PhysLean (CliffordAlgebra.instIsScalarTower)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_instisscalartower : ∀ {R : Type u_3} {S : Type u_4} {A : Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]
--   [inst_2 : AddCommGroup M] [inst_3 : CommRing A] [inst_4 : SMul R S] [inst_5 : Algebra R A] [inst_6 : Algebra S A]
--   [inst_7 : Module R M] [inst_8 : Module S M] [inst_9 : Module A M] [inst_10 : IsScalarTower R A M]
--   [inst_11 : IsScalarTower S A M] [IsScalarTower R S A] (Q : QuadraticForm A M), IsScalarTower R S (CliffordAlgebra Q)

-- Source: PhysLean (complexLorentzTensor.termη)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_termη : Lean.ParserDescr

-- Source: PhysLean (Lorentz.ContrℂModule.val)
-- [complex signature, not re-axiomatized]
-- lorentz_contrℂmodule_val : Lorentz.ContrℂModule → Sum (Fin 1) (Fin 3) → Complex

-- Source: PhysLean (complexLorentzTensor.altLeftLeftUnit_eq_fromPairT)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altleftleftunit_eq_frompairt : Eq complexLorentzTensor.altLeftLeftUnit
--   (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT Fermion.altLeftLeftUnitVal)

-- Source: PhysLean (complexLorentzTensor.coContrUnit_eq_ofRat)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cocontrunit_eq_ofrat : Eq complexLorentzTensor.coContrUnit
--   (LinearMap.instFunLike.coe complexLorentzTensor.ofRat fun f => ite (Eq (f 0) (f 1)) 1 0)

-- Source: PhysLean (Lorentz.CoℂModule.toFin13ℂFun)
-- [complex signature, not re-axiomatized]
-- lorentz_coℂmodule_tofin13ℂfun : Equiv Lorentz.CoℂModule (Sum (Fin 1) (Fin 3) → Complex)

-- Source: PhysLean (Lorentz.preContrMetricVal_expand_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_precontrmetricval_expand_tmul : ∀ {d : Nat},
--   Eq (Lorentz.preContrMetricVal d)
--     (instHSub.hSub
--       (TensorProduct.tmul Real (Module.Basis.instFunLike.coe (Lorentz.contrBasis d) (Sum.inl 0))
--         (Module.Basis.instFunLike.coe (Lorentz.contrBasis d) (Sum.inl 0)))
--       (Finset.univ.sum fun i =>
--         TensorProduct.tmul Real (Module.Basis.instFunLike.coe (Lorentz.contrBasis d) (Sum.inr i))
--           (Module.Basis.instFunLike.coe (Lorentz.contrBasis d) (Sum.inr i))))

-- Source: PhysLean (LorentzGroup.eq_of_mulVec_eq)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_eq_of_mulvec_eq : ∀ {d : Nat} {Λ Λ' : (LorentzGroup d).Elem},
--   (∀ (x : Sum (Fin 1) (Fin d) → Real), Eq (Λ.val.mulVec x) (Λ'.val.mulVec x)) → Eq Λ Λ'

-- Source: PhysLean (Lorentz.contrContrContractField.matrix_apply_eq_iff_sub)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_matrix_apply_eq_iff_sub : ∀ {d : Nat} (x y : (Lorentz.Contr d).V.carrier) {Λ Λ' : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real},
--   Iff
--     (Eq
--       (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--         (TensorProduct.tmul Real x (Lorentz.ContrMod.mulVec Λ y)))
--       (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--         (TensorProduct.tmul Real x (Lorentz.ContrMod.mulVec Λ' y))))
--     (Eq
--       (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--         (TensorProduct.tmul Real x (Lorentz.ContrMod.mulVec (instHSub.hSub Λ Λ') y)))
--       0)

-- Source: PhysLean (LorentzGroup.mem_iff_transpose_mul_minkowskiMatrix_mul_self)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_mem_iff_transpose_mul_minkowskimatrix_mul_self : ∀ {d : Nat} (Λ : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real),
--   Iff (Set.instMembership.mem (LorentzGroup d) Λ)
--     (Eq (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (instHMul.hMul Λ.transpose minkowskiMatrix) Λ)
--       minkowskiMatrix)

-- Source: PhysLean (realLorentzTensor.«_aux_PhysLean_Relativity_Tensors_RealTensor_Derivative___macroRules_realLorentzTensor_term∂_1»)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_«_aux_physlean_relativity_tensors_realtensor_derivative___macrorules_reallorentztensor_term∂_1» : Lean.Macro

-- Source: PhysLean (complexLorentzTensor.leftMetric_eq_basis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_leftmetric_eq_basis : Eq complexLorentzTensor.leftMetric
--   (instHAdd.hAdd
--     (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg
--       (Module.Basis.instFunLike.coe
--         (TensorSpecies.Tensor.basis
--           (Matrix.vecCons complexLorentzTensor.Color.upL
--             (Matrix.vecCons complexLorentzTensor.Color.upL Matrix.vecEmpty)))
--         fun x =>
--         complexLorentzTensor.coMetric_eq_basis.match_1
--           (fun x =>
--             Fin
--               (complexLorentzTensor.repDim
--                 (Matrix.vecCons complexLorentzTensor.Color.upL
--                   (Matrix.vecCons complexLorentzTensor.Color.upL Matrix.vecEmpty) x)))
--           x (fun _ => 0) fun _ => 1))
--     (Module.Basis.instFunLike.coe
--       (TensorSpecies.Tensor.basis
--         (Matrix.vecCons complexLorentzTensor.Color.upL (Matrix.vecCons complexLorentzTensor.Color.upL Matrix.vecEmpty)))
--       fun x =>
--       complexLorentzTensor.coMetric_eq_basis.match_1
--         (fun x =>
--           Fin
--             (complexLorentzTensor.repDim
--               (Matrix.vecCons complexLorentzTensor.Color.upL
--                 (Matrix.vecCons complexLorentzTensor.Color.upL Matrix.vecEmpty) x)))
--         x (fun _ => 1) fun _ => 0))

-- Source: PhysLean (complexLorentzTensor.coContrUnit_eq_complexCoBasisFin4_complexContrBasisFin4)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cocontrunit_eq_complexcobasisfin4_complexcontrbasisfin4 : Eq complexLorentzTensor.coContrUnit
--   (Finset.univ.sum fun i =>
--     LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasisFin4 i)
--         (Module.Basis.instFunLike.coe Lorentz.complexContrBasisFin4 i)))

-- Source: PhysLean (SpaceTime.differentiable_vector)
-- [complex signature, not re-axiomatized]
-- spacetime_differentiable_vector : ∀ {d : Nat} (f : SpaceTime d → Lorentz.Vector d),
--   Iff (∀ (ν : Sum (Fin 1) (Fin d)), Differentiable Real fun x => f x ν) (Differentiable Real f)

-- Source: PhysLean (Lorentz.coContrToMatrixRe_symm_expand_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrtomatrixre_symm_expand_tmul : ∀ {d : Nat} (M : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real),
--   Eq (EquivLike.toFunLike.coe Lorentz.coContrToMatrixRe.symm M)
--     (Finset.univ.sum fun i =>
--       Finset.univ.sum fun j =>
--         instHSMul.hSMul (M i j)
--           (TensorProduct.tmul Real (Module.Basis.instFunLike.coe (Lorentz.coBasis d) i)
--             (Module.Basis.instFunLike.coe (Lorentz.contrBasis d) j)))

-- Source: PhysLean (Lorentz.Vector.timeComponent)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_timecomponent : {d : Nat} → Lorentz.Vector d → Real

-- Source: PhysLean (Lorentz.Vector.isLorentz_iff_comp_adjoint_eq_id)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_islorentz_iff_comp_adjoint_eq_id : ∀ {d : Nat} (f : LinearMap (RingHom.id Real) (Lorentz.Vector d) (Lorentz.Vector d)),
--   Iff (Lorentz.Vector.IsLorentz f) (Eq ((Lorentz.Vector.adjoint f).comp f) LinearMap.id)

-- Source: PhysLean (LorentzGroup.isOrthochronous_of_restricted)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_isorthochronous_of_restricted : ∀ {d : Nat} (Λ : Subtype fun x => SetLike.instMembership.mem (LorentzGroup.restricted d) x),
--   LorentzGroup.IsOrthochronous Λ.val

-- Source: PhysLean (realLorentzTensor.repDim_eq_one_plus_dim)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_repdim_eq_one_plus_dim : ∀ {d : Nat} {c : realLorentzTensor.Color}, Eq ((realLorentzTensor d).repDim c) (instHAdd.hAdd 1 d)

-- Source: PhysLean (Lorentz.Vector.pastLightConeBoundary.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_pastlightconeboundary_eq_1 : ∀ {d : Nat} (p : Lorentz.Vector d),
--   Eq p.pastLightConeBoundary
--     (setOf fun q =>
--       And (Eq (instHSub.hSub q p).causalCharacter Lorentz.Vector.CausalCharacter.lightLike)
--         (Real.instLE.le (instHSub.hSub q p (Sum.inl 0)) 0))

-- Source: PhysLean (Lorentz.ContrMod.rep_apply_toFin1dℝ)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_rep_apply_tofin1dℝ : ∀ {d : Nat} (g : (LorentzGroup d).Elem) (ψ : Lorentz.ContrMod d),
--   Eq (LinearMap.instFunLike.coe (MonoidHom.instFunLike.coe Lorentz.ContrMod.rep g) ψ).toFin1dℝ (g.val.mulVec ψ.toFin1dℝ)

-- Source: PhysLean (realLorentzTensor.mapToBasis)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_maptobasis : {d n m : Nat} →
--   {cm : Fin m → realLorentzTensor.Color} →
--     {cn : Fin n → realLorentzTensor.Color} →
--       ((realLorentzTensor d).Tensor cm → (realLorentzTensor d).Tensor cn) →
--         (TensorSpecies.Tensor.ComponentIdx cm → Real) → TensorSpecies.Tensor.ComponentIdx cn → Real

-- Source: PhysLean (Lorentz.preCoContrUnitVal.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_precocontrunitval_eq_1 : ∀ (d : Nat), Eq (Lorentz.preCoContrUnitVal d) (EquivLike.toFunLike.coe Lorentz.coContrToMatrixRe.symm 1)

-- Source: PhysLean (LorentzGroup.generalizedBoost_isOrthochronous)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_generalizedboost_isorthochronous : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem), LorentzGroup.IsOrthochronous (LorentzGroup.generalizedBoost u v)

-- Source: PhysLean (LorentzGroup.boost.h)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_h : ∀ {d : Nat} (i : Fin d) (β : Real),
--   Real.instLT.lt (abs β) 1 →
--     Set.instMembership.mem (LorentzGroup d) fun j k =>
--       ite (And (Eq k (Sum.inl 0)) (Eq j (Sum.inl 0))) (LorentzGroup.γ β)
--         (ite (And (Eq k (Sum.inl 0)) (Eq j (Sum.inr i))) (instHMul.hMul (Real.instNeg.neg (LorentzGroup.γ β)) β)
--           (ite (And (Eq k (Sum.inr i)) (Eq j (Sum.inl 0))) (instHMul.hMul (Real.instNeg.neg (LorentzGroup.γ β)) β)
--             (ite (And (Eq k (Sum.inr i)) (Eq j (Sum.inr i))) (LorentzGroup.γ β) (ite (Eq j k) 1 0))))

-- Source: PhysLean (complexLorentzTensor.Color.ctorElim)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_color_ctorelim : {motive : complexLorentzTensor.Color → Sort u} →
--   (ctorIdx : Nat) →
--     (t : complexLorentzTensor.Color) → Eq ctorIdx t.ctorIdx → complexLorentzTensor.Color.ctorElimType ctorIdx → motive t

-- Source: PhysLean (complexLorentzTensor.contrMetric_eq_ofRat)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrmetric_eq_ofrat : Eq complexLorentzTensor.contrMetric
--   (LinearMap.instFunLike.coe complexLorentzTensor.ofRat fun f =>
--     ite (And (Eq (f 0) 0) (Eq (f 1) 0)) 1 (ite (Eq (f 0) (f 1)) (-1) 0))

-- Source: PhysLean (complexLorentzTensor.termεL)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_termεl : Lean.ParserDescr

-- Source: PhysLean (Lorentz.Vector.sum_basis_eq_zero_iff)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_sum_basis_eq_zero_iff : ∀ {d : Nat} (f : Sum (Fin 1) (Fin d) → Real),
--   Iff (Eq (Finset.univ.sum fun μ => instHSMul.hSMul (f μ) (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ)) 0)
--     (∀ (μ : Sum (Fin 1) (Fin d)), Eq (f μ) 0)

-- Source: PhysLean (Lorentz.SL2C.toRestrictedLorentzGroup)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_torestrictedlorentzgroup : InformalLemma

-- Source: PhysLean (Lorentz.ContrℂModule.ctorIdx)
-- [complex signature, not re-axiomatized]
-- lorentz_contrℂmodule_ctoridx : Lorentz.ContrℂModule → Nat

-- Source: PhysLean (Lorentz.coContrContract_tmul_symm)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrcontract_tmul_symm : ∀ {d : Nat} (φ : (Lorentz.Co d).V.carrier) (ψ : (Lorentz.Contr d).V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom Lorentz.coContrContract.hom)
--       (TensorProduct.tmul Real φ ψ))
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom Lorentz.contrCoContract.hom)
--       (TensorProduct.tmul Real ψ φ))

-- Source: PhysLean (CliffordAlgebra.ι_mul_ι_comm)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_ι_mul_ι_comm : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   {Q : QuadraticForm R M} (a b : M),
--   Eq
--     (instHMul.hMul (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) a)
--       (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) b))
--     (instHSub.hSub
--       (RingHom.instFunLike.coe (algebraMap R (CliffordAlgebra Q))
--         (QuadraticMap.polar (QuadraticMap.instFunLike.coe Q) a b))
--       (instHMul.hMul (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) b)
--         (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) a)))

-- Source: PhysLean (LorentzGroup.restricted_eq_identity_component_of_isConnected)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_restricted_eq_identity_component_of_isconnected : ∀ {d : Nat},
--   IsConnected (Subgroup.instSetLike.coe (LorentzGroup.restricted d)) →
--     Eq (Subgroup.instSetLike.coe (LorentzGroup.restricted d)) (connectedComponent 1)

-- Source: PhysLean (complexLorentzTensor.rightAltRightUnit_eq_rightBasis_altRightBasis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_rightaltrightunit_eq_rightbasis_altrightbasis : Eq complexLorentzTensor.rightAltRightUnit
--   (Finset.univ.sum fun i =>
--     LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.rightBasis i)
--         (Module.Basis.instFunLike.coe Fermion.altRightBasis i)))

-- Source: PhysLean (SpaceTime.deriv_sum_inl)
-- [complex signature, not re-axiomatized]
-- spacetime_deriv_sum_inl : ∀ {d : Nat} {M : Type} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] (c : SpeedOfLight)
--   (f : SpaceTime d → M),
--   Differentiable Real f →
--     ∀ (x : SpaceTime d),
--       Eq (SpaceTime.deriv (Sum.inl 0) f x)
--         (instHSMul.hSMul (instHDiv.hDiv 1 c.val)
--           (Time.deriv
--             (fun t =>
--               f
--                 (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c).symm
--                   { fst := t, snd := (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c) x).snd }))
--             (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c) x).fst))

-- Source: PhysLean (complexLorentzTensor.actionT_rightMetric)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_actiont_rightmetric : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (instHSMul.hSMul g complexLorentzTensor.rightMetric) complexLorentzTensor.rightMetric

-- Source: PhysLean (Lorentz.Vector.minkowskiProductMap_smul_snd)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproductmap_smul_snd : ∀ {d : Nat} (c : Real) (p q : Lorentz.Vector d),
--   Eq (p.minkowskiProductMap (instHSMul.hSMul c q)) (instHMul.hMul c (p.minkowskiProductMap q))

-- Source: PhysLean (Lorentz.Vector.spatialPart_apply_eq_toCoord)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_spatialpart_apply_eq_tocoord : ∀ {d : Nat} (v : Lorentz.Vector d) (i : Fin d), Eq (v.spatialPart.ofLp i) (v (Sum.inr i))

-- Source: PhysLean (LorentzGroup.orthchroMap_IsOrthochronous)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_orthchromap_isorthochronous : ∀ {d : Nat} {Λ : (LorentzGroup d).Elem},
--   LorentzGroup.IsOrthochronous Λ → Eq (ContinuousMap.instFunLike.coe LorentzGroup.orthchroMap Λ) 1

-- Source: PhysLean (Lorentz.CoVector.smul_sub)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_smul_sub : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem) (p q : Lorentz.CoVector d),
--   Eq (instHSMul.hSMul Λ (instHSub.hSub p q)) (instHSub.hSub (instHSMul.hSMul Λ p) (instHSMul.hSMul Λ q))

-- Source: PhysLean (SpaceTime.timeSpaceBasisEquiv)
-- [complex signature, not re-axiomatized]
-- spacetime_timespacebasisequiv : {d : Nat} → SpeedOfLight → ContinuousLinearEquiv (RingHom.id Real) (SpaceTime d) (SpaceTime d)

-- Source: PhysLean (LorentzGroup.generalizedBoost_apply_expand)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_generalizedboost_apply_expand : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem) (x : Lorentz.Vector d),
--   Eq (instHSMul.hSMul (LorentzGroup.generalizedBoost u v) x)
--     (instHSub.hSub
--       (instHAdd.hAdd x
--         (instHSMul.hSMul
--           (instHMul.hMul 2
--             (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct x) u.val))
--           v.val))
--       (instHSMul.hSMul
--         (instHDiv.hDiv
--           (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct x)
--             (instHAdd.hAdd u.val v.val))
--           (instHAdd.hAdd 1
--             (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct u.val)
--               v.val)))
--         (instHAdd.hAdd u.val v.val)))

-- Source: PhysLean (realLorentzTensor.Color.up.elim)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_color_up_elim : {motive : realLorentzTensor.Color → Sort u} →
--   (t : realLorentzTensor.Color) → Eq t.ctorIdx 0 → motive realLorentzTensor.Color.up → motive t

-- Source: PhysLean (LorentzGroup.inv_eq_dual)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_inv_eq_dual : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Eq (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ) ⟨minkowskiMatrix.dual Λ.val, ⋯⟩

-- Source: PhysLean (LorentzGroup.detContinuous)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_detcontinuous : {d : Nat} → ContinuousMap (LorentzGroup d).Elem (Multiplicative (ZMod 2))

-- Source: PhysLean (complexLorentzTensor.actionT_coContrUnit)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_actiont_cocontrunit : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (instHSMul.hSMul g complexLorentzTensor.coContrUnit) complexLorentzTensor.coContrUnit

-- Source: PhysLean (LorentzGroup.id_isOrthochronous)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_id_isorthochronous : ∀ {d : Nat}, LorentzGroup.IsOrthochronous 1

-- Source: PhysLean (complexLorentzTensor.contrMetric_eq_fromPairT)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrmetric_eq_frompairt : Eq complexLorentzTensor.contrMetric (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT Lorentz.contrMetricVal)

-- Source: PhysLean (Lorentz.contrContrCoBi)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcobi : LinearMap (RingHom.id Complex) Lorentz.complexCo.V.carrier
--   (LinearMap (RingHom.id Complex) Lorentz.complexContr.V.carrier Complex)

-- Source: PhysLean (Lorentz.coContrUnit_symm)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrunit_symm : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.coContrUnit.hom) 1)
--   (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr).V
--         (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--       (Action.instMonoidalCategory.whiskerLeft Lorentz.complexCo (Action.instCategory.id Lorentz.complexContr)).hom)
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo).V
--           (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--         ((Action.instBraidedCategory (ModuleCat Complex) (Matrix.SpecialLinearGroup (Fin 2) Complex)).braiding
--               Lorentz.complexContr Lorentz.complexCo).hom.hom)
--       (((fun X Y => LinearMap.instFunLike)
--             (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--             (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo).V).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.contrCoUnit.hom) 1)))

-- Source: PhysLean (Lorentz.Velocity.zero_le_minkowskiProduct)
-- [complex signature, not re-axiomatized]
-- lorentz_velocity_zero_le_minkowskiproduct : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem),
--   Real.instLE.le 0
--     (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct u.val) v.val)

-- Source: PhysLean (Lorentz.contrCoContraction_hom_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcocontraction_hom_tmul : ∀ (ψ : Lorentz.complexContr.V.carrier) (φ : Lorentz.complexCo.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.contrCoContraction.hom)
--       (TensorProduct.tmul Complex ψ φ))
--     (dotProduct (Lorentz.ContrℂModule.toFin13ℂ ψ) (Lorentz.CoℂModule.toFin13ℂ φ))

-- Source: PhysLean (Lorentz.CoℂModule.instModuleComplex)
-- [complex signature, not re-axiomatized]
-- lorentz_coℂmodule_instmodulecomplex : Module Complex Lorentz.CoℂModule

-- Source: PhysLean (Lorentz.Vector.causallyFollows)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causallyfollows : {d : Nat} → Lorentz.Vector d → Lorentz.Vector d → Prop

-- Source: PhysLean (SpaceTime.det_timeSpaceBasisEquiv)
-- [complex signature, not re-axiomatized]
-- spacetime_det_timespacebasisequiv : ∀ {d : Nat} (c : SpeedOfLight),
--   Eq (MonoidHom.instFunLike.coe LinearEquiv.det (SpaceTime.timeSpaceBasisEquiv c).toLinearEquiv).val c.val

-- Source: PhysLean (complexLorentzTensor.Color.down.sizeOf_spec)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_color_down_sizeof_spec : Eq (complexLorentzTensor.Color._sizeOf_inst.sizeOf complexLorentzTensor.Color.down) 1

-- Source: PhysLean (Lorentz.Vector.instChartedSpace)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_instchartedspace : {d : Nat} → ChartedSpace (Lorentz.Vector d) (Lorentz.Vector d)

-- Source: PhysLean (minkowskiMatrix.mulVec_inl_0)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_mulvec_inl_0 : ∀ {d : Nat} (v : Sum (Fin 1) (Fin d) → Real), Eq (minkowskiMatrix.mulVec v (Sum.inl 0)) (v (Sum.inl 0))

-- Source: PhysLean (SpaceTime.deriv_coord)
-- [complex signature, not re-axiomatized]
-- spacetime_deriv_coord : ∀ {d : Nat} (μ ν : Sum (Fin 1) (Fin d)), Eq (SpaceTime.deriv μ fun x => x ν) (ite (Eq μ ν) 1 0)

-- Source: PhysLean (LorentzGroup.mem_rotations_iff)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_mem_rotations_iff : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Iff (SetLike.instMembership.mem (LorentzGroup.Rotations d) Λ)
--     (And (Eq (Λ.val (Sum.inl 0) (Sum.inl 0)) 1) (LorentzGroup.IsProper Λ))

-- Source: PhysLean (Lorentz.Vector.minkowskiProduct_self_le_timeComponent_sq)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproduct_self_le_timecomponent_sq : ∀ {d : Nat} (p : Lorentz.Vector d),
--   Real.instLE.le (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct p) p)
--     (instHPow.hPow p.timeComponent 2)

-- Source: PhysLean (LorentzGroup.toProd_apply)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_toprod_apply : ∀ {d : Nat} (a : (LorentzGroup d).Elem),
--   Eq (MonoidHom.instFunLike.coe LorentzGroup.toProd a)
--     { fst := (MonoidHom.instFunLike.coe LorentzGroup.toGL a).val,
--       snd := MulOpposite.instInv.inv (MulOpposite.op (MonoidHom.instFunLike.coe LorentzGroup.toGL a).val) }

-- Source: PhysLean (complexLorentzTensor.coContrUnit_eq_fromPairT)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cocontrunit_eq_frompairt : Eq complexLorentzTensor.coContrUnit (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT Lorentz.coContrUnitVal)

-- Source: PhysLean (Lorentz.Vector.timeLike_iff_norm_sq_pos)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_timelike_iff_norm_sq_pos : ∀ {d : Nat} (p : Lorentz.Vector d),
--   Iff (Eq p.causalCharacter Lorentz.Vector.CausalCharacter.timeLike)
--     (Real.instLT.lt 0
--       (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct p) p))

-- Source: PhysLean (Lorentz.CoVector.innerProductSpace)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_innerproductspace : (d : Nat) → InnerProductSpace Real (Lorentz.CoVector d)

-- Source: PhysLean (complexLorentzTensor.altRightMetric_eq_basis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altrightmetric_eq_basis : Eq complexLorentzTensor.altRightMetric
--   (instHSub.hSub
--     (Module.Basis.instFunLike.coe
--       (TensorSpecies.Tensor.basis
--         (Matrix.vecCons complexLorentzTensor.Color.downR
--           (Matrix.vecCons complexLorentzTensor.Color.downR Matrix.vecEmpty)))
--       fun x =>
--       complexLorentzTensor.coMetric_eq_basis.match_1
--         (fun x =>
--           Fin
--             (complexLorentzTensor.repDim
--               (Matrix.vecCons complexLorentzTensor.Color.downR
--                 (Matrix.vecCons complexLorentzTensor.Color.downR Matrix.vecEmpty) x)))
--         x (fun _ => 0) fun _ => 1)
--     (Module.Basis.instFunLike.coe
--       (TensorSpecies.Tensor.basis
--         (Matrix.vecCons complexLorentzTensor.Color.downR
--           (Matrix.vecCons complexLorentzTensor.Color.downR Matrix.vecEmpty)))
--       fun x =>
--       complexLorentzTensor.coMetric_eq_basis.match_1
--         (fun x =>
--           Fin
--             (complexLorentzTensor.repDim
--               (Matrix.vecCons complexLorentzTensor.Color.downR
--                 (Matrix.vecCons complexLorentzTensor.Color.downR Matrix.vecEmpty) x)))
--         x (fun _ => 1) fun _ => 0))

-- Source: PhysLean (LorentzGroup.isOrthochronous_iff_transpose)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_isorthochronous_iff_transpose : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Iff (LorentzGroup.IsOrthochronous Λ) (LorentzGroup.IsOrthochronous (LorentzGroup.transpose Λ))

-- Source: PhysLean (Lorentz.Vector.minkowskiProductMap_symm)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproductmap_symm : ∀ {d : Nat} (p q : Lorentz.Vector d), Eq (p.minkowskiProductMap q) (q.minkowskiProductMap p)

-- Source: PhysLean (complexLorentzTensor.contrMetric)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrmetric : complexLorentzTensor.Tensor
--   (Matrix.vecCons complexLorentzTensor.Color.up (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty))

-- Source: PhysLean (CliffordAlgebra.leftInverse_map_of_leftInverse)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_leftinverse_map_of_leftinverse : ∀ {R : Type u_1} [inst : CommRing R] {M₁ : Type u_4} {M₂ : Type u_5} [inst_1 : AddCommGroup M₁]
--   [inst_2 : AddCommGroup M₂] [inst_3 : Module R M₁] [inst_4 : Module R M₂] {Q₁ : QuadraticForm R M₁}
--   {Q₂ : QuadraticForm R M₂} (f : QuadraticMap.Isometry Q₁ Q₂) (g : QuadraticMap.Isometry Q₂ Q₁),
--   Function.LeftInverse (QuadraticMap.Isometry.instFunLike.coe g) (QuadraticMap.Isometry.instFunLike.coe f) →
--     Function.LeftInverse (AlgHom.funLike.coe (CliffordAlgebra.map g)) (AlgHom.funLike.coe (CliffordAlgebra.map f))

-- Source: PhysLean (Lorentz.coCoToMatrixRe.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_cocotomatrixre_eq_1 : ∀ {d : Nat},
--   Eq Lorentz.coCoToMatrixRe
--     ((((Lorentz.coBasis d).tensorProduct (Lorentz.coBasis d)).repr.trans
--           (Finsupp.linearEquivFunOnFinite Real Real (Prod (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d))))).trans
--       (LinearEquiv.curry Real Real (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d))))

-- Source: PhysLean (Lorentz.SL2C.toLorentzGroup_det_one)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_tolorentzgroup_det_one : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M).val.det 1

-- Source: PhysLean (Lorentz.Vector.actionCLM_surjective)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_actionclm_surjective : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Function.Surjective (ContinuousLinearMap.funLike.coe (Lorentz.Vector.actionCLM Λ))

-- Source: PhysLean (Lorentz.ℍ₂)
-- [complex signature, not re-axiomatized]
-- lorentz_ℍ₂ : AddSubgroup (Matrix (Fin 2) (Fin 2) Complex)

-- Source: PhysLean (complexLorentzTensor.coContrUnit_eq_basis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cocontrunit_eq_basis : Eq complexLorentzTensor.coContrUnit
--   (Finset.univ.sum fun i =>
--     Module.Basis.instFunLike.coe
--       (TensorSpecies.Tensor.basis
--         (Matrix.vecCons complexLorentzTensor.Color.down (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty)))
--       fun x =>
--       complexLorentzTensor.coContrUnit_eq_basis.match_1
--         (fun x =>
--           Fin
--             (complexLorentzTensor.repDim
--               (Matrix.vecCons complexLorentzTensor.Color.down
--                 (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty) x)))
--         x (fun _ => i) fun _ => i)

-- Source: PhysLean (SpaceTime.spaceTime_integral_eq_space_integral_time_integral)
-- [complex signature, not re-axiomatized]
-- spacetime_spacetime_integral_eq_space_integral_time_integral : ∀ {M : Type u_1} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] {d : Nat} (c : SpeedOfLight)
--   (f : SpaceTime d → M),
--   MeasureTheory.Integrable f SpaceTime.instMeasureSpace.volume →
--     Eq (MeasureTheory.integral SpaceTime.instMeasureSpace.volume fun x => f x)
--       (instHSMul.hSMul c.val
--         (MeasureTheory.integral measureSpaceOfInnerProductSpace.volume fun x =>
--           MeasureTheory.integral measureSpaceOfInnerProductSpace.volume fun t =>
--             f (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c).symm { fst := t, snd := x })))

-- Source: PhysLean (LorentzGroup.genBoostAux₁_basis_genBoostAux₂_minkowskiProduct)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_genboostaux₁_basis_genboostaux₂_minkowskiproduct : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem) (μ ν : Sum (Fin 1) (Fin d)),
--   Eq
--     (ContinuousLinearMap.funLike.coe
--       (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct
--         (LinearMap.instFunLike.coe (LorentzGroup.genBoostAux₁ u v)
--           (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ)))
--       (LinearMap.instFunLike.coe (LorentzGroup.genBoostAux₂ u v) (Module.Basis.instFunLike.coe Lorentz.Vector.basis ν)))
--     (instHMul.hMul
--       (instHMul.hMul (instHMul.hMul (instHMul.hMul (-2) (minkowskiMatrix μ μ)) (minkowskiMatrix ν ν)) (u.val μ))
--       (instHAdd.hAdd (u.val ν) (v.val ν)))

-- Source: PhysLean (LorentzGroup.isOrthochronous_iff_ge_one)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_isorthochronous_iff_ge_one : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Iff (LorentzGroup.IsOrthochronous Λ) (Real.instLE.le 1 (Λ.val (Sum.inl 0) (Sum.inl 0)))

-- Source: PhysLean (Lorentz.coContrContraction_tmul_symm)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrcontraction_tmul_symm : ∀ (φ : Lorentz.complexCo.V.carrier) (ψ : Lorentz.complexContr.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.coContrContraction.hom)
--       (TensorProduct.tmul Complex φ ψ))
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.contrCoContraction.hom)
--       (TensorProduct.tmul Complex ψ φ))

-- Source: PhysLean (CliffordAlgebra.map_apply_ι)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_map_apply_ι : ∀ {R : Type u_1} [inst : CommRing R] {M₁ : Type u_4} {M₂ : Type u_5} [inst_1 : AddCommGroup M₁]
--   [inst_2 : AddCommGroup M₂] [inst_3 : Module R M₁] [inst_4 : Module R M₂] {Q₁ : QuadraticForm R M₁}
--   {Q₂ : QuadraticForm R M₂} (f : QuadraticMap.Isometry Q₁ Q₂) (m : M₁),
--   Eq (AlgHom.funLike.coe (CliffordAlgebra.map f) (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q₁) m))
--     (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q₂) (QuadraticMap.Isometry.instFunLike.coe f m))

-- Source: PhysLean (LorentzGroup.γ.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_γ_eq_1 : ∀ (β : Real), Eq (LorentzGroup.γ β) (instHDiv.hDiv 1 (instHSub.hSub 1 (instHPow.hPow β 2)).sqrt)

-- Source: PhysLean (Lorentz.Vector.«_aux_PhysLean_Relativity_Tensors_RealTensor_Vector_MinkowskiProduct___macroRules_Lorentz_Vector_term⟪_,_⟫ₘ_1»)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_«_aux_physlean_relativity_tensors_realtensor_vector_minkowskiproduct___macrorules_lorentz_vector_term⟪_,_⟫ₘ_1» : Lean.Macro

-- Source: PhysLean (LorentzGroup.instInvertibleMatrixSumFinOfNatNatComplexCoeMonoidHomElemRealToComplex)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_instinvertiblematrixsumfinofnatnatcomplexcoemonoidhomelemrealtocomplex : {d : Nat} → (M : (LorentzGroup d).Elem) → Invertible (MonoidHom.instFunLike.coe LorentzGroup.toComplex M)

-- Source: PhysLean (complexLorentzTensor.actionT_altLeftLeftUnit)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_actiont_altleftleftunit : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (instHSMul.hSMul g complexLorentzTensor.altLeftLeftUnit) complexLorentzTensor.altLeftLeftUnit

-- Source: PhysLean (Lorentz.Vector.tensor_basis_map_eq_basis_reindex)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_tensor_basis_map_eq_basis_reindex : ∀ {d : Nat},
--   Eq
--     ((TensorSpecies.Tensor.basis (Matrix.vecCons realLorentzTensor.Color.up Matrix.vecEmpty)).map
--       Lorentz.Vector.tensorial.toTensor.symm)
--     (Lorentz.Vector.basis.reindex Lorentz.Vector.indexEquiv.symm)

-- Source: PhysLean (LorentzGroup.coe_neg)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_coe_neg : ∀ {d : Nat} {Λ : (LorentzGroup d).Elem},
--   Eq (LorentzGroup.instNegElemMatrixSumFinOfNatNatReal.neg Λ).val (Matrix.neg.neg Λ.val)

-- Source: PhysLean (Lorentz.Vector.timeComponent_basis_sum_inl)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_timecomponent_basis_sum_inl : ∀ {d : Nat}, Eq (Module.Basis.instFunLike.coe Lorentz.Vector.basis (Sum.inl 0)).timeComponent 1

-- Source: PhysLean (Lorentz.Vector.lightlike_eq_spatial_norm_of_eq_time)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_lightlike_eq_spatial_norm_of_eq_time : ∀ {d : Nat} {v w : Lorentz.Vector d},
--   Eq v.causalCharacter Lorentz.Vector.CausalCharacter.lightLike →
--     Eq w.causalCharacter Lorentz.Vector.CausalCharacter.lightLike →
--       Eq v.timeComponent w.timeComponent →
--         Eq ((PiLp.innerProductSpace fun x => Real).inner Real v.spatialPart v.spatialPart)
--           ((PiLp.innerProductSpace fun x => Real).inner Real w.spatialPart w.spatialPart)

-- Source: PhysLean (LorentzGroup.genBoostAux₁)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_genboostaux₁ : {d : Nat} →
--   (Lorentz.Velocity d).Elem →
--     (Lorentz.Velocity d).Elem → LinearMap (RingHom.id Real) (Lorentz.Vector d) (Lorentz.Vector d)

-- Source: PhysLean (Lorentz.complexCoBasis)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcobasis : Module.Basis (Sum (Fin 1) (Fin 3)) Complex Lorentz.complexCo.V.carrier

-- Source: PhysLean (LorentzGroup.generalizedBoost_inv)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_generalizedboost_inv : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem),
--   Eq (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv (LorentzGroup.generalizedBoost u v))
--     (LorentzGroup.generalizedBoost v u)

-- Source: PhysLean (SpaceTime.properTime_zero_ofSpaceLike)
-- [complex signature, not re-axiomatized]
-- spacetime_propertime_zero_ofspacelike : ∀ {d : Nat} (q p : SpaceTime d),
--   Eq (Lorentz.Vector.causalCharacter (instHSub.hSub p q)) Lorentz.Vector.CausalCharacter.spaceLike →
--     Eq (q.properTime p) 0

-- Source: PhysLean (Lorentz.CoVector.basis_repr_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_basis_repr_apply : ∀ {d : Nat} (p : Lorentz.CoVector d) (μ : Sum (Fin 1) (Fin d)),
--   Eq (Finsupp.instFunLike.coe (EquivLike.toFunLike.coe Lorentz.CoVector.basis.repr p) μ) (p μ)

-- Source: PhysLean (Lorentz.contrContrContractField)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield : {d : Nat} →
--   LinearMap (RingHom.id Real) (TensorProduct Real (Lorentz.Contr d).V.carrier (Lorentz.Contr d).V.carrier) Real

-- Source: PhysLean (complexLorentzTensor.rightMetric_contr_altRightMetric)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_rightmetric_contr_altrightmetric : Eq
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.contrT 2 1 2 ⋯)
--     (LinearMap.instFunLike.coe
--       (LinearMap.instFunLike.coe TensorSpecies.Tensor.prodT
--         (EquivLike.toFunLike.coe
--           (TensorSpecies.Tensorial.self complexLorentzTensor
--               (Matrix.vecCons complexLorentzTensor.Color.upR
--                 (Matrix.vecCons complexLorentzTensor.Color.upR Matrix.vecEmpty))).toTensor
--           complexLorentzTensor.rightMetric))
--       (EquivLike.toFunLike.coe
--         (TensorSpecies.Tensorial.self complexLorentzTensor
--             (Matrix.vecCons complexLorentzTensor.Color.downR
--               (Matrix.vecCons complexLorentzTensor.Color.downR Matrix.vecEmpty))).toTensor
--         complexLorentzTensor.altRightMetric)))
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT (Matrix.vecCons 0 (Matrix.vecCons 1 Matrix.vecEmpty)) ⋯)
--     (EquivLike.toFunLike.coe
--       (TensorSpecies.Tensorial.self complexLorentzTensor
--           (Matrix.vecCons complexLorentzTensor.Color.upR
--             (Matrix.vecCons complexLorentzTensor.Color.downR Matrix.vecEmpty))).toTensor
--       complexLorentzTensor.rightAltRightUnit))

-- Source: PhysLean (Lorentz.SL2C.toSelfAdjointMap')
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_toselfadjointmap' : Matrix (Fin 2) (Fin 2) Complex →
--   LinearMap (RingHom.id Real) (Subtype fun x => SetLike.instMembership.mem Lorentz.ℍ₂ x)
--     (Subtype fun x => SetLike.instMembership.mem Lorentz.ℍ₂ x)

-- Source: PhysLean (realLorentzTensor.Color.toCtorIdx)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_color_toctoridx : realLorentzTensor.Color → Nat

-- Source: PhysLean (complexLorentzTensor.Color.up.elim)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_color_up_elim : {motive : complexLorentzTensor.Color → Sort u} →
--   (t : complexLorentzTensor.Color) → Eq t.ctorIdx 4 → motive complexLorentzTensor.Color.up → motive t

-- Source: PhysLean (LorentzGroup.comm_minkowskiMatrix)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_comm_minkowskimatrix : ∀ {d : Nat} {Λ : (LorentzGroup d).Elem},
--   Eq (instHMul.hMul Λ.val minkowskiMatrix)
--     (instHMul.hMul minkowskiMatrix (LorentzGroup.transpose (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ)).val)

-- Source: PhysLean (Lorentz.contrContrToMatrix_ρ)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrtomatrix_ρ : ∀ (v : (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexContr).V.carrier)
--   (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (EquivLike.toFunLike.coe Lorentz.contrContrToMatrix
--       (LinearMap.instFunLike.coe
--         (TensorProduct.map (MonoidHom.instFunLike.coe Lorentz.complexContr.ρ M)
--           (MonoidHom.instFunLike.coe Lorentz.complexContr.ρ M))
--         v))
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--         (MonoidHom.instFunLike.coe LorentzGroup.toComplex (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M))
--         (EquivLike.toFunLike.coe Lorentz.contrContrToMatrix v))
--       (MonoidHom.instFunLike.coe LorentzGroup.toComplex
--           (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M)).transpose)

-- Source: PhysLean (Lorentz.Vector.causallyFollows.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causallyfollows_eq_1 : ∀ {d : Nat} (p q : Lorentz.Vector d),
--   Eq (p.causallyFollows q)
--     (Or (Set.instMembership.mem p.interiorFutureLightCone q) (Set.instMembership.mem p.futureLightConeBoundary q))

-- Source: PhysLean (Lorentz.contrMetric_apply_one)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmetric_apply_one : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexContr).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.contrMetric.hom) 1)
--   Lorentz.contrMetricVal

-- Source: PhysLean (Lorentz.contrContrContractField.symm)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_symm : ∀ {d : Nat} (x y : (Lorentz.Contr d).V.carrier),
--   Eq (LinearMap.instFunLike.coe Lorentz.contrContrContractField (TensorProduct.tmul Real x y))
--     (LinearMap.instFunLike.coe Lorentz.contrContrContractField (TensorProduct.tmul Real y x))

-- Source: PhysLean (LorentzGroup.smul_timeComponent_eq_toVector_minkowskiProduct)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_smul_timecomponent_eq_tovector_minkowskiproduct : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem) (v : Lorentz.Vector d),
--   Eq (instHSMul.hSMul Λ v).timeComponent
--     (ContinuousLinearMap.funLike.coe
--       (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct
--         (LorentzGroup.toVector (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ)))
--       v)

-- Source: PhysLean (Lorentz.CoVector.tensor_basis_repr_toTensor_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_tensor_basis_repr_totensor_apply : ∀ {d : Nat} (p : Lorentz.CoVector d)
--   (μ : TensorSpecies.Tensor.ComponentIdx (Matrix.vecCons realLorentzTensor.Color.down Matrix.vecEmpty)),
--   Eq
--     (Finsupp.instFunLike.coe
--       (EquivLike.toFunLike.coe
--         (TensorSpecies.Tensor.basis (Matrix.vecCons realLorentzTensor.Color.down Matrix.vecEmpty)).repr
--         (EquivLike.toFunLike.coe Lorentz.CoVector.tensorial.toTensor p))
--       μ)
--     (p (EquivLike.toFunLike.coe Lorentz.CoVector.indexEquiv μ))

-- Source: PhysLean (Lorentz.coCoToMatrix_ρ)
-- [complex signature, not re-axiomatized]
-- lorentz_cocotomatrix_ρ : ∀ (v : (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexCo).V.carrier)
--   (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (EquivLike.toFunLike.coe Lorentz.coCoToMatrix
--       (LinearMap.instFunLike.coe
--         (TensorProduct.map (MonoidHom.instFunLike.coe Lorentz.complexCo.ρ M)
--           (MonoidHom.instFunLike.coe Lorentz.complexCo.ρ M))
--         v))
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--         (Matrix.inv.inv
--             (MonoidHom.instFunLike.coe LorentzGroup.toComplex
--               (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M))).transpose
--         (EquivLike.toFunLike.coe Lorentz.coCoToMatrix v))
--       (Matrix.inv.inv
--         (MonoidHom.instFunLike.coe LorentzGroup.toComplex (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M))))

-- Source: PhysLean (Lorentz.CoℂModule.toFin13ℂ)
-- [complex signature, not re-axiomatized]
-- lorentz_coℂmodule_tofin13ℂ : Lorentz.CoℂModule → Sum (Fin 1) (Fin 3) → Complex

-- Source: PhysLean (Lorentz.Vector.coord_continuous)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_coord_continuous : ∀ {d : Nat} (i : Sum (Fin 1) (Fin d)), Continuous fun v => v i

-- Source: PhysLean (realLorentzTensor.derivative.eq_1)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_derivative_eq_1 : ∀ {d n m : Nat} {cm : Fin m → realLorentzTensor.Color} {cn : Fin n → realLorentzTensor.Color}
--   (f : (realLorentzTensor d).Tensor cm → (realLorentzTensor d).Tensor cn) (y : (realLorentzTensor d).Tensor cm),
--   Eq (realLorentzTensor.derivative f y)
--     (EquivLike.toFunLike.coe
--       (TensorSpecies.Tensor.basis (Fin.append (fun i => (realLorentzTensor d).τ (cm i)) cn)).repr.toEquiv.symm
--       (EquivLike.toFunLike.coe Finsupp.equivFunOnFinite.symm fun b =>
--         ContinuousLinearMap.funLike.coe
--           (fderiv Real (realLorentzTensor.mapToBasis f)
--             (EquivLike.toFunLike.coe Finsupp.equivFunOnFinite
--               (EquivLike.toFunLike.coe (TensorSpecies.Tensor.basis cm).repr y)))
--           (Finsupp.instFunLike.coe
--             (Finsupp.single
--               (fun i => Fin.cast ⋯ ((EquivLike.toFunLike.coe TensorSpecies.Tensor.ComponentIdx.prodEquiv b).fst i)) 1))
--           (EquivLike.toFunLike.coe TensorSpecies.Tensor.ComponentIdx.prodEquiv b).snd))

-- Source: PhysLean (Lorentz.preContrCoUnit_apply_one)
-- [complex signature, not re-axiomatized]
-- lorentz_precontrcounit_apply_one : ∀ {d : Nat},
--   Eq
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V
--           (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom (Lorentz.preContrCoUnit d).hom) 1)
--     (Lorentz.preContrCoUnitVal d)

-- Source: PhysLean (Lorentz.preContrCoUnitVal.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_precontrcounitval_eq_1 : ∀ (d : Nat), Eq (Lorentz.preContrCoUnitVal d) (EquivLike.toFunLike.coe Lorentz.contrCoToMatrixRe.symm 1)

-- Source: PhysLean (Lorentz.contrContrToMatrix_symm_expand_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrtomatrix_symm_expand_tmul : ∀ (M : Matrix (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3)) Complex),
--   Eq (EquivLike.toFunLike.coe Lorentz.contrContrToMatrix.symm M)
--     (Finset.univ.sum fun i =>
--       Finset.univ.sum fun j =>
--         instHSMul.hSMul (M i j)
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasis i)
--             (Module.Basis.instFunLike.coe Lorentz.complexContrBasis j)))

-- Source: PhysLean (SpaceTime.instSMulCommClassRealElemMatrixSumFinOfNatNatLorentzGroupDistribution)
-- [complex signature, not re-axiomatized]
-- spacetime_instsmulcommclassrealelemmatrixsumfinofnatnatlorentzgroupdistribution : ∀ {n d : Nat} {c : Fin n → realLorentzTensor.Color} {M : Type} [inst : NormedAddCommGroup M]
--   [inst_1 : NormedSpace Real M] [inst_2 : (realLorentzTensor d).Tensorial c M] [inst_3 : T2Space M],
--   SMulCommClass Real (LorentzGroup d).Elem (Distribution Real (SpaceTime d) M)

-- Source: PhysLean (Lorentz.complexContrBasisFin4.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcontrbasisfin4_eq_1 : Eq Lorentz.complexContrBasisFin4 (Lorentz.complexContrBasis.reindex finSumFinEquiv)

-- Source: PhysLean (Lorentz.preCoContrUnit_symm)
-- [complex signature, not re-axiomatized]
-- lorentz_precocontrunit_symm : ∀ {d : Nat},
--   Eq
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V
--           (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom (Lorentz.preCoContrUnit d).hom) 1)
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)).V
--           (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom
--         (Action.instMonoidalCategory.whiskerLeft (Lorentz.Co d) (Action.instCategory.id (Lorentz.Contr d))).hom)
--       (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)).V
--             (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)).V).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom
--           ((Action.instBraidedCategory (ModuleCat Real) (LorentzGroup d).Elem).braiding (Lorentz.Contr d)
--                 (Lorentz.Co d)).hom.hom)
--         (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V
--               (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)).V).coe
--           ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom (Lorentz.preContrCoUnit d).hom) 1)))

-- Source: PhysLean (LorentzGroup.isProper_iff)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_isproper_iff : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Iff (LorentzGroup.IsProper Λ) (Eq (MonoidHom.instFunLike.coe LorentzGroup.detRep Λ) 1)

-- Source: PhysLean (CliffordAlgebra.induction)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_induction : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   {Q : QuadraticForm R M} {C : CliffordAlgebra Q → Prop},
--   (∀ (r : R), C (RingHom.instFunLike.coe (algebraMap R (CliffordAlgebra Q)) r)) →
--     (∀ (x : M), C (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) x)) →
--       (∀ (a b : CliffordAlgebra Q), C a → C b → C (instHMul.hMul a b)) →
--         (∀ (a b : CliffordAlgebra Q), C a → C b → C (instHAdd.hAdd a b)) → ∀ (a : CliffordAlgebra Q), C a

-- Source: PhysLean (Lorentz.ContrℂModule.toFin13ℂ)
-- [complex signature, not re-axiomatized]
-- lorentz_contrℂmodule_tofin13ℂ : Lorentz.ContrℂModule → Sum (Fin 1) (Fin 3) → Complex

-- Source: PhysLean (LorentzGroup.minkowskiMatrix_comm)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_minkowskimatrix_comm : ∀ {d : Nat} {Λ : (LorentzGroup d).Elem},
--   Eq (instHMul.hMul minkowskiMatrix Λ.val)
--     (instHMul.hMul (LorentzGroup.transpose (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ)).val minkowskiMatrix)

-- Source: PhysLean (Lorentz.CoℂModule.lorentzGroupRep)
-- [complex signature, not re-axiomatized]
-- lorentz_coℂmodule_lorentzgrouprep : Representation Complex (LorentzGroup 3).Elem Lorentz.CoℂModule

-- Source: PhysLean (Lorentz.ContrMod.toFin1dℝFun)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_tofin1dℝfun : {d : Nat} → Equiv (Lorentz.ContrMod d) (Sum (Fin 1) (Fin d) → Real)

-- Source: PhysLean (Lorentz.ContrMod.toFin1dℝ)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_tofin1dℝ : {d : Nat} → Lorentz.ContrMod d → Sum (Fin 1) (Fin d) → Real

-- Source: PhysLean (Lorentz.complexCoBasisFin4)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcobasisfin4 : Module.Basis (Fin 4) Complex Lorentz.complexCo.V.carrier

-- Source: PhysLean (Lorentz.Velocity.timeComponent_pos)
-- [complex signature, not re-axiomatized]
-- lorentz_velocity_timecomponent_pos : ∀ {d : Nat} (v : (Lorentz.Velocity d).Elem), Real.instLT.lt 0 v.val.timeComponent

-- Source: PhysLean (complexLorentzTensor.altLeftLeftUnit_eq_basis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altleftleftunit_eq_basis : Eq complexLorentzTensor.altLeftLeftUnit
--   (Finset.univ.sum fun i =>
--     Module.Basis.instFunLike.coe
--       (TensorSpecies.Tensor.basis
--         (Matrix.vecCons complexLorentzTensor.Color.downL
--           (Matrix.vecCons complexLorentzTensor.Color.upL Matrix.vecEmpty)))
--       fun x =>
--       complexLorentzTensor.coContrUnit_eq_basis.match_1
--         (fun x =>
--           Fin
--             (complexLorentzTensor.repDim
--               (Matrix.vecCons complexLorentzTensor.Color.downL
--                 (Matrix.vecCons complexLorentzTensor.Color.upL Matrix.vecEmpty) x)))
--         x (fun _ => i) fun _ => i)

-- Source: PhysLean (Lorentz.Vector.toTensor_symm_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_totensor_symm_apply : ∀ {d : Nat} (p : (realLorentzTensor d).Tensor (Matrix.vecCons realLorentzTensor.Color.up Matrix.vecEmpty)),
--   Eq (EquivLike.toFunLike.coe Lorentz.Vector.tensorial.toTensor.symm p)
--     (EquivLike.toFunLike.coe (Equiv.piCongrLeft' (fun a => Real) Lorentz.Vector.indexEquiv)
--       (EquivLike.toFunLike.coe Finsupp.equivFunOnFinite
--         (EquivLike.toFunLike.coe
--           (TensorSpecies.Tensor.basis (Matrix.vecCons realLorentzTensor.Color.up Matrix.vecEmpty)).repr p)))

-- Source: PhysLean (LorentzGroup.orthochronoustoVelocity.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_orthochronoustovelocity_eq_1 : ∀ {d : Nat} {Λ : (LorentzGroup d).Elem} (h : LorentzGroup.IsOrthochronous Λ),
--   Eq (LorentzGroup.orthochronoustoVelocity h) ⟨LorentzGroup.toVector Λ, ⋯⟩

-- Source: PhysLean (realLorentzTensor.evalT_toComplex)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_evalt_tocomplex : InformalLemma

-- Source: PhysLean (Lorentz.Vector.indexEquiv.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_indexequiv_eq_1 : ∀ {d : Nat},
--   Eq Lorentz.Vector.indexEquiv
--     ({ toFun := fun f => Fin.cast ⋯ (f 0), invFun := fun x j => Fin.cast ⋯ x, left_inv := ⋯, right_inv := ⋯ }.trans
--       finSumFinEquiv.symm)

-- Source: PhysLean (Lorentz.Vector.apply_smul)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_apply_smul : ∀ {d : Nat} (c : Real) (v : Lorentz.Vector d) (i : Sum (Fin 1) (Fin d)),
--   Eq (instHSMul.hSMul c v i) (instHMul.hMul c (v i))

-- Source: PhysLean (Lorentz.Vector.basis_inner)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_basis_inner : ∀ {d : Nat} (μ : Sum (Fin 1) (Fin d)) (p : Lorentz.Vector d),
--   Eq ((Lorentz.Vector.instInnerReal d).inner Real (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ) p) (p μ)

-- Source: PhysLean (SpaceTime.toTimeAndSpace_basis_inl)
-- [complex signature, not re-axiomatized]
-- spacetime_totimeandspace_basis_inl : ∀ {d : Nat} {c : SpeedOfLight},
--   Eq
--     (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c)
--       (Module.Basis.instFunLike.coe Lorentz.Vector.basis (Sum.inl 0)))
--     { fst := { val := instHDiv.hDiv 1 c.val }, snd := 0 }

-- Source: PhysLean (Lorentz.Vector.fderiv_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_fderiv_apply : ∀ {d : Nat} {α : Type u_1} [inst : NormedAddCommGroup α] [inst_1 : NormedSpace Real α] (f : α → Lorentz.Vector d),
--   Differentiable Real f →
--     ∀ (x dt : α) (ν : Sum (Fin 1) (Fin d)),
--       Eq (ContinuousLinearMap.funLike.coe (fderiv Real f x) dt ν)
--         (ContinuousLinearMap.funLike.coe (fderiv Real (fun y => f y ν) x) dt)

-- Source: PhysLean (SpaceTime.timeSpaceBasis)
-- [complex signature, not re-axiomatized]
-- spacetime_timespacebasis : {d : Nat} → optParam SpeedOfLight 1 → Module.Basis (Sum (Fin 1) (Fin d)) Real (SpaceTime d)

-- Source: PhysLean (Lorentz.contrCoToMatrix)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcotomatrix : LinearEquiv (RingHom.id Complex)
--   (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo).V.carrier
--   (Matrix (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3)) Complex)

-- Source: PhysLean (LorentzGroup.boost_zero_inl_0_inr_nat_succ)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_zero_inl_0_inr_nat_succ : ∀ {d : Nat} {β : Real} (hβ : Real.instLT.lt (abs β) 1) (i : Nat)
--   (h : instLTNat.lt (instHAdd.hAdd i 1) (instHAdd.hAdd d 1)),
--   Eq ((LorentzGroup.boost 0 β hβ).val (Sum.inl 0) (Sum.inr ⟨instHAdd.hAdd i 1, h⟩)) 0

-- Source: PhysLean (LorentzGroup.toBoostRotation)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_toboostrotation : {d : Nat} →
--   Homeomorph (Subtype fun x => SetLike.instMembership.mem (LorentzGroup.restricted d) x)
--     (Prod (Lorentz.Velocity d).Elem
--       (Subtype fun x => SetLike.instMembership.mem (Matrix.specialOrthogonalGroup (Fin d) Real) x))

-- Source: PhysLean (Lorentz.coBasisFin)
-- [complex signature, not re-axiomatized]
-- lorentz_cobasisfin : (d : optParam Nat 3) → Module.Basis (Fin (instHAdd.hAdd 1 d)) Real (Lorentz.Co d).V.carrier

-- Source: PhysLean (CliffordAlgebra.range_lift)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_range_lift : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   {Q : QuadraticForm R M} {A : Type u_3} [inst_3 : Semiring A] [inst_4 : Algebra R A] (f : LinearMap (RingHom.id R) M A)
--   (cond :
--     ∀ (m : M),
--       Eq (instHMul.hMul (LinearMap.instFunLike.coe f m) (LinearMap.instFunLike.coe f m))
--         (RingHom.instFunLike.coe (algebraMap R A) (QuadraticMap.instFunLike.coe Q m))),
--   Eq (EquivLike.toFunLike.coe (CliffordAlgebra.lift Q) ⟨f, cond⟩).range
--     (Algebra.adjoin R (Set.range (LinearMap.instFunLike.coe f)))

-- Source: PhysLean (complexLorentzTensor.termδ)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_termδ : Lean.ParserDescr

-- Source: PhysLean (complexLorentzTensor.coContrUnit_eq_fromConstPair)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cocontrunit_eq_fromconstpair : Eq complexLorentzTensor.coContrUnit (TensorSpecies.Tensor.fromConstPair Lorentz.coContrUnit)

-- Source: PhysLean (complexLorentzTensor.contr_basis_ratComplexNum)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contr_basis_ratcomplexnum : ∀ {c : complexLorentzTensor.Color} (i : Fin (complexLorentzTensor.repDim c))
--   (j : Fin (complexLorentzTensor.repDim (complexLorentzTensor.τ c))),
--   Eq
--     (TensorSpecies.castToField
--       (((fun X Y => LinearMap.instFunLike)
--             ((IndexNotation.OverColor.Discrete.pairτ complexLorentzTensor.FD complexLorentzTensor.τ).obj { as := c }).V
--             ((CategoryTheory.Monoidal.functorCategoryMonoidalStruct.tensorUnit
--                     (CategoryTheory.Functor (CategoryTheory.Discrete complexLorentzTensor.Color)
--                       (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))).obj
--                 { as := c }).V).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--           (complexLorentzTensor.contr.app { as := c }).hom)
--         (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe (complexLorentzTensor.basis c) i)
--           (Module.Basis.instFunLike.coe (complexLorentzTensor.basis (complexLorentzTensor.τ c)) j))))
--     (RingHom.instFunLike.coe RatComplexNum.toComplexNum (ite (Eq i.val j.val) 1 0))

-- Source: PhysLean (Lorentz.CoMod.rep)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_rep : {d : Nat} → Representation Real (LorentzGroup d).Elem (Lorentz.CoMod d)

-- Source: PhysLean (complexLorentzTensor.termδR)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_termδr : Lean.ParserDescr

-- Source: PhysLean (Lorentz.contrContrContractField.same_eq_det_toSelfAdjoint)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_same_eq_det_toselfadjoint : ∀ (x : Lorentz.ContrMod 3),
--   Eq (Complex.ofReal (LinearMap.instFunLike.coe Lorentz.contrContrContractField (TensorProduct.tmul Real x x)))
--     (EquivLike.toFunLike.coe Lorentz.ContrMod.toSelfAdjoint x).val.det

-- Source: PhysLean (complexLorentzTensor.leftMetric_eq_fromConstPair)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_leftmetric_eq_fromconstpair : Eq complexLorentzTensor.leftMetric (TensorSpecies.Tensor.fromConstPair Fermion.leftMetric)

-- Source: PhysLean (realLorentzTensor.toComplex_injective)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_tocomplex_injective : ∀ {n : Nat} (c : Fin n → realLorentzTensor.Color),
--   Function.Injective (LinearMap.instFunLike.coe realLorentzTensor.toComplex)

-- Source: PhysLean (LorentzGroup.generalizedBoost_continuous_snd)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_generalizedboost_continuous_snd : ∀ {d : Nat} (u : (Lorentz.Velocity d).Elem), Continuous (LorentzGroup.generalizedBoost u)

-- Source: PhysLean (LorentzGroup.toVector_neg)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_tovector_neg : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Eq (LorentzGroup.toVector (LorentzGroup.instNegElemMatrixSumFinOfNatNatReal.neg Λ))
--     (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg (LorentzGroup.toVector Λ))

-- Source: PhysLean (LorentzGroup.γ_det_not_zero)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_γ_det_not_zero : ∀ (β : Real), Real.instLT.lt (abs β) 1 → Ne (instHSub.hSub 1 (instHPow.hPow β 2)) 0

-- Source: PhysLean (realLorentzTensor.«term∂»)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_«term∂» : Lean.ParserDescr

-- Source: PhysLean (complexLorentzTensor.contrCoUnit_eq_ofRat)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrcounit_eq_ofrat : Eq complexLorentzTensor.contrCoUnit
--   (LinearMap.instFunLike.coe complexLorentzTensor.ofRat fun f => ite (Eq (f 0) (f 1)) 1 0)

-- Source: PhysLean (LorentzGroup.genBoostAux₂_self)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_genboostaux₂_self : ∀ {d : Nat} (u : (Lorentz.Velocity d).Elem),
--   Eq (LorentzGroup.genBoostAux₂ u u) (LinearMap.instNeg.neg (LorentzGroup.genBoostAux₁ u u))

-- Source: PhysLean (SpaceTime.timeSpaceBasis_apply_inl)
-- [complex signature, not re-axiomatized]
-- spacetime_timespacebasis_apply_inl : ∀ {d : Nat} (c : SpeedOfLight),
--   Eq (Module.Basis.instFunLike.coe (SpaceTime.timeSpaceBasis c) (Sum.inl 0))
--     (instHSMul.hSMul c.val (Module.Basis.instFunLike.coe Lorentz.Vector.basis (Sum.inl 0)))

-- Source: PhysLean (Lorentz.ContrMod.toSelfAdjoint_stdBasis)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_toselfadjoint_stdbasis : ∀ (i : Sum (Fin 1) (Fin 3)),
--   Eq (EquivLike.toFunLike.coe Lorentz.ContrMod.toSelfAdjoint (Module.Basis.instFunLike.coe Lorentz.ContrMod.stdBasis i))
--     (Module.Basis.instFunLike.coe PauliMatrix.pauliBasis' i)

-- Source: PhysLean (SpaceTime.timeSliceLinearEquiv.eq_1)
-- [complex signature, not re-axiomatized]
-- spacetime_timeslicelinearequiv_eq_1 : ∀ {d : Nat} {M : Type} [inst : AddCommGroup M] [inst_1 : Module Real M] (c : SpeedOfLight),
--   Eq (SpaceTime.timeSliceLinearEquiv c)
--     { toFun := EquivLike.toFunLike.coe (SpaceTime.timeSlice c), map_add' := ⋯, map_smul' := ⋯,
--       invFun := EquivLike.toFunLike.coe (SpaceTime.timeSlice c).symm, left_inv := ⋯, right_inv := ⋯ }

-- Source: PhysLean (Lorentz.continuous_contr)
-- [complex signature, not re-axiomatized]
-- lorentz_continuous_contr : ∀ {d : Nat} {T : Type} [inst : TopologicalSpace T] (f : T → (Lorentz.Contr d).V.carrier),
--   (Continuous fun i => Lorentz.ContrMod.toFin1dℝ (f i)) → Continuous f

-- Source: PhysLean (LorentzGroup.toComplex_mulVec_ofReal)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_tocomplex_mulvec_ofreal : ∀ {d : Nat} (v : Sum (Fin 1) (Fin d) → Real) (Λ : (LorentzGroup d).Elem),
--   Eq
--     ((MonoidHom.instFunLike.coe LorentzGroup.toComplex Λ).mulVec
--       (Function.comp (RingHom.instFunLike.coe Complex.ofRealHom) v))
--     (Function.comp (RingHom.instFunLike.coe Complex.ofRealHom) (Λ.val.mulVec v))

-- Source: PhysLean (Lorentz.Vector.neg_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_neg_apply : ∀ {d : Nat} (v : Lorentz.Vector d) (i : Sum (Fin 1) (Fin d)),
--   Eq (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg v i) (Real.instNeg.neg (v i))

-- Source: PhysLean (Lorentz.Vector.euclidCLE)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_euclidcle : (d : Nat) → ContinuousLinearEquiv (RingHom.id Real) (Lorentz.Vector d) (EuclideanSpace Real (Sum (Fin 1) (Fin d)))

-- Source: PhysLean (minkowskiMatrix.inl_0_inl_0)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_inl_0_inl_0 : ∀ {d : Nat}, Eq (minkowskiMatrix (Sum.inl 0) (Sum.inl 0)) 1

-- Source: PhysLean (LorentzGroup.toRotation)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_torotation : {d : Nat} →
--   (Subtype fun x => SetLike.instMembership.mem (LorentzGroup.restricted d) x) →
--     Subtype fun x => SetLike.instMembership.mem (LorentzGroup.Rotations d) x

-- Source: PhysLean (LorentzGroup.IsOrthochronous)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_isorthochronous : {d : Nat} → (LorentzGroup d).Elem → Prop

-- Source: PhysLean (Lorentz.Vector.spatialPart_basis_sum_inl)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_spatialpart_basis_sum_inl : ∀ {d : Nat} (i : Fin d), Eq ((Module.Basis.instFunLike.coe Lorentz.Vector.basis (Sum.inl 0)).spatialPart.ofLp i) 0

-- Source: PhysLean (LorentzGroup.toGL_embedding)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_togl_embedding : ∀ {d : Nat}, Topology.IsEmbedding LorentzGroup.toGL.toFun

-- Source: PhysLean (Lorentz.contrContrToMatrixRe_symm_expand_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrtomatrixre_symm_expand_tmul : ∀ {d : Nat} (M : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real),
--   Eq (EquivLike.toFunLike.coe Lorentz.contrContrToMatrixRe.symm M)
--     (Finset.univ.sum fun i =>
--       Finset.univ.sum fun j =>
--         instHSMul.hSMul (M i j)
--           (TensorProduct.tmul Real (Module.Basis.instFunLike.coe (Lorentz.contrBasis d) i)
--             (Module.Basis.instFunLike.coe (Lorentz.contrBasis d) j)))

-- Source: PhysLean (Lorentz.Vector.temporalCLM)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_temporalclm : (d : Nat) → ContinuousLinearMap (RingHom.id Real) (Lorentz.Vector d) Real

-- Source: PhysLean (LorentzGroup.boost_inr_self_inl_0)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_inr_self_inl_0 : ∀ {d : Nat} (i : Fin d) {β : Real} (hβ : Real.instLT.lt (abs β) 1),
--   Eq ((LorentzGroup.boost i β hβ).val (Sum.inr i) (Sum.inl 0)) (instHMul.hMul (Real.instNeg.neg (LorentzGroup.γ β)) β)

-- Source: PhysLean (complexLorentzTensor.rightAltRightUnit_eq_fromConstPair)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_rightaltrightunit_eq_fromconstpair : Eq complexLorentzTensor.rightAltRightUnit (TensorSpecies.Tensor.fromConstPair Fermion.rightAltRightUnit)

-- Source: PhysLean (SpaceTime.schwartzAction)
-- [complex signature, not re-axiomatized]
-- spacetime_schwartzaction : {d : Nat} →
--   MonoidHom (LorentzGroup d).Elem
--     (ContinuousLinearMap (RingHom.id Real) (SchwartzMap (SpaceTime d) Real) (SchwartzMap (SpaceTime d) Real))

-- Source: PhysLean (complexLorentzTensor.contrCoUnit_eq_fromConstPair)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrcounit_eq_fromconstpair : Eq complexLorentzTensor.contrCoUnit (TensorSpecies.Tensor.fromConstPair Lorentz.contrCoUnit)

-- Source: PhysLean (complexLorentzTensor.coMetric_eq_ofRat)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cometric_eq_ofrat : Eq complexLorentzTensor.coMetric
--   (LinearMap.instFunLike.coe complexLorentzTensor.ofRat fun f =>
--     ite (And (Eq (f 0) 0) (Eq (f 1) 0)) 1 (ite (Eq (f 0) (f 1)) (-1) 0))

-- Source: PhysLean (Lorentz.ContrMod.sub_mulVec)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_sub_mulvec : ∀ {d : Nat} (M N : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real) (v : Lorentz.ContrMod d),
--   Eq (Lorentz.ContrMod.mulVec (instHSub.hSub M N) v)
--     (instHSub.hSub (Lorentz.ContrMod.mulVec M v) (Lorentz.ContrMod.mulVec N v))

-- Source: PhysLean (Lorentz.preCoMetricVal_expand_tmul_minkowskiMatrix)
-- [complex signature, not re-axiomatized]
-- lorentz_precometricval_expand_tmul_minkowskimatrix : ∀ {d : Nat},
--   Eq (Lorentz.preCoMetricVal d)
--     (Finset.univ.sum fun i =>
--       instHSMul.hSMul (minkowskiMatrix i i)
--         (TensorProduct.tmul Real (Module.Basis.instFunLike.coe (Lorentz.coBasis d) i)
--           (Module.Basis.instFunLike.coe (Lorentz.coBasis d) i)))

-- Source: PhysLean (LorentzGroup.detContinuous_eq_zero)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_detcontinuous_eq_zero : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Iff (Eq (ContinuousMap.instFunLike.coe LorentzGroup.detContinuous Λ) (EquivLike.toFunLike.coe Additive.toMul 1))
--     (Eq Λ.val.det (-1))

-- Source: PhysLean (LorentzGroup.stepFunction_continuous)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_stepfunction_continuous : Continuous LorentzGroup.stepFunction

-- Source: PhysLean (Lorentz.SL2CRep_ρ_basis)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2crep_ρ_basis : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex) (i : Sum (Fin 1) (Fin 3)),
--   Eq
--     (LinearMap.instFunLike.coe (MonoidHom.instFunLike.coe Lorentz.complexContr.ρ M)
--       (Module.Basis.instFunLike.coe Lorentz.complexContrBasis i))
--     (Finset.univ.sum fun j =>
--       instHSMul.hSMul ((MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M).val j i)
--         (Module.Basis.instFunLike.coe Lorentz.complexContrBasis j))

-- Source: PhysLean (Lorentz.CoVector.isNormedAddCommGroup)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_isnormedaddcommgroup : (d : Nat) → NormedAddCommGroup (Lorentz.CoVector d)

-- Source: PhysLean (LorentzGroup.boost_zero_inr_0_inr_succ)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_zero_inr_0_inr_succ : ∀ {d : Nat} {β : Real} (hβ : Real.instLT.lt (abs β) 1) (i : Fin d),
--   Eq ((LorentzGroup.boost 0 β hβ).val (Sum.inr 0) (Sum.inr i.succ)) 0

-- Source: PhysLean (CliffordAlgebra.ι_comp_lift)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_ι_comp_lift : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   {Q : QuadraticForm R M} {A : Type u_3} [inst_3 : Semiring A] [inst_4 : Algebra R A] (f : LinearMap (RingHom.id R) M A)
--   (cond :
--     ∀ (m : M),
--       Eq (instHMul.hMul (LinearMap.instFunLike.coe f m) (LinearMap.instFunLike.coe f m))
--         (RingHom.instFunLike.coe (algebraMap R A) (QuadraticMap.instFunLike.coe Q m))),
--   Eq ((EquivLike.toFunLike.coe (CliffordAlgebra.lift Q) ⟨f, cond⟩).toLinearMap.comp (CliffordAlgebra.ι Q)) f

-- Source: PhysLean (Lorentz.coContrUnitVal)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrunitval : (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr).V.carrier

-- Source: PhysLean (Lorentz.Vector.sum_inl_inr_basis_eq_zero_iff)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_sum_inl_inr_basis_eq_zero_iff : ∀ {d : Nat} (f₀ : Real) (f : Fin d → Real),
--   Iff
--     (Eq
--       (instHAdd.hAdd (instHSMul.hSMul f₀ (Module.Basis.instFunLike.coe Lorentz.Vector.basis (Sum.inl 0)))
--         (Finset.univ.sum fun i =>
--           instHSMul.hSMul (f i) (Module.Basis.instFunLike.coe Lorentz.Vector.basis (Sum.inr i))))
--       0)
--     (And (Eq f₀ 0) (∀ (i : Fin d), Eq (f i) 0))

-- Source: PhysLean (Lorentz.contrContrContractField.dual_mulVec_right)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_dual_mulvec_right : ∀ {d : Nat} (x y : (Lorentz.Contr d).V.carrier) {Λ : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real},
--   Eq
--     (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--       (TensorProduct.tmul Real x (Lorentz.ContrMod.mulVec (minkowskiMatrix.dual Λ) y)))
--     (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--       (TensorProduct.tmul Real (Lorentz.ContrMod.mulVec Λ x) y))

-- Source: PhysLean (Lorentz.Vector.time_component_ne_zero_of_timelike)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_time_component_ne_zero_of_timelike : ∀ {d : Nat} {v : Lorentz.Vector d}, Eq v.causalCharacter Lorentz.Vector.CausalCharacter.timeLike → Ne (v (Sum.inl 0)) 0

-- Source: PhysLean (Lorentz.Vector.minkowskiProduct_symm)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproduct_symm : ∀ {d : Nat} (p q : Lorentz.Vector d),
--   Eq (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct p) q)
--     (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct q) p)

-- Source: PhysLean (Lorentz.Vector.spatialCLM)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_spatialclm : (d : Nat) → ContinuousLinearMap (RingHom.id Real) (Lorentz.Vector d) (EuclideanSpace Real (Fin d))

-- Source: PhysLean (Lorentz.CoVector.actionCLM_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_actionclm_apply : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem) (p : Lorentz.CoVector d),
--   Eq (ContinuousLinearMap.funLike.coe (Lorentz.CoVector.actionCLM Λ) p) (instHSMul.hSMul Λ p)

-- Source: PhysLean (SpaceTime.space.eq_1)
-- [complex signature, not re-axiomatized]
-- spacetime_space_eq_1 : ∀ {d : Nat},
--   Eq SpaceTime.space
--     { toFun := fun x => { val := (Lorentz.Vector.spatialPart x).ofLp }, map_add' := ⋯, map_smul' := ⋯, cont := ⋯ }

-- Source: PhysLean (LorentzGroup.orthochronoustoVelocity.congr_simp)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_orthochronoustovelocity_congr_simp : ∀ {d : Nat} {Λ Λ_1 : (LorentzGroup d).Elem} (e_Λ : Eq Λ Λ_1) (h : LorentzGroup.IsOrthochronous Λ),
--   Eq (LorentzGroup.orthochronoustoVelocity h) (LorentzGroup.orthochronoustoVelocity ⋯)

-- Source: PhysLean (Lorentz.ContrMod.instTopologicalSpace)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_insttopologicalspace : {d : Nat} → TopologicalSpace (Lorentz.ContrMod d)

-- Source: PhysLean (realLorentzTensor.Color.up.sizeOf_spec)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_color_up_sizeof_spec : Eq (realLorentzTensor.Color._sizeOf_inst.sizeOf realLorentzTensor.Color.up) 1

-- Source: PhysLean (complexLorentzTensor.Color.downL.elim)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_color_downl_elim : {motive : complexLorentzTensor.Color → Sort u} →
--   (t : complexLorentzTensor.Color) → Eq t.ctorIdx 1 → motive complexLorentzTensor.Color.downL → motive t

-- Source: PhysLean (LorentzGroup.genBoostAux₁_add_genBoostAux₂_minkowskiProduct)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_genboostaux₁_add_genboostaux₂_minkowskiproduct : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem) (μ ν : Sum (Fin 1) (Fin d)),
--   Eq
--     (ContinuousLinearMap.funLike.coe
--       (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct
--         (instHAdd.hAdd
--           (LinearMap.instFunLike.coe (LorentzGroup.genBoostAux₁ u v)
--             (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ))
--           (LinearMap.instFunLike.coe (LorentzGroup.genBoostAux₂ u v)
--             (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ))))
--       (instHAdd.hAdd
--         (LinearMap.instFunLike.coe (LorentzGroup.genBoostAux₁ u v)
--           (Module.Basis.instFunLike.coe Lorentz.Vector.basis ν))
--         (LinearMap.instFunLike.coe (LorentzGroup.genBoostAux₂ u v)
--           (Module.Basis.instFunLike.coe Lorentz.Vector.basis ν))))
--     (instHMul.hMul (instHMul.hMul (instHMul.hMul 2 (minkowskiMatrix μ μ)) (minkowskiMatrix ν ν))
--       (instHAdd.hAdd
--         (instHAdd.hAdd
--           (instHSub.hSub (instHMul.hMul (Real.instNeg.neg (u.val μ)) (instHAdd.hAdd (u.val ν) (v.val ν)))
--             (instHMul.hMul (u.val ν) (instHAdd.hAdd (u.val μ) (v.val μ))))
--           (instHMul.hMul (instHMul.hMul (instHAdd.hAdd (u.val μ) (v.val μ)) (instHAdd.hAdd (u.val ν) (v.val ν)))
--             (Real.instInv.inv
--               (instHAdd.hAdd 1
--                 (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct u.val)
--                   v.val)))))
--         (instHMul.hMul (instHMul.hMul 2 (u.val μ)) (u.val ν))))

-- Source: PhysLean (LorentzGroup.mem_iff_dual_mul_self)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_mem_iff_dual_mul_self : ∀ {d : Nat} {Λ : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real},
--   Iff (Set.instMembership.mem (LorentzGroup d) Λ)
--     (Eq (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (minkowskiMatrix.dual Λ) Λ) 1)

-- Source: PhysLean (Lorentz.complexContrBasis_of_real)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcontrbasis_of_real : ∀ (i : Sum (Fin 1) (Fin 3)),
--   Eq (Module.Basis.instFunLike.coe Lorentz.complexContrBasis i)
--     (LinearMap.instFunLike.coe Lorentz.inclCongrRealLorentz (Module.Basis.instFunLike.coe Lorentz.ContrMod.stdBasis i))

-- Source: PhysLean (LorentzGroup.orthchroMapReal_on_IsOrthochronous)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_orthchromapreal_on_isorthochronous : ∀ {d : Nat} {Λ : (LorentzGroup d).Elem},
--   LorentzGroup.IsOrthochronous Λ → Eq (ContinuousMap.instFunLike.coe LorentzGroup.orthchroMapReal Λ) 1

-- Source: PhysLean (Lorentz.Vector.instCoeFunForallSumFinOfNatNatReal)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_instcoefunforallsumfinofnatnatreal : {d : Nat} → CoeFun (Lorentz.Vector d) fun x => Sum (Fin 1) (Fin d) → Real

-- Source: PhysLean (SpaceTime.distTensorDeriv)
-- [complex signature, not re-axiomatized]
-- spacetime_disttensorderiv : {M : Type} →
--   {d : Nat} →
--     [inst : NormedAddCommGroup M] →
--       [inst_1 : InnerProductSpace Real M] →
--         [FiniteDimensional Real M] →
--           LinearMap (RingHom.id Real) (Distribution Real (SpaceTime d) M)
--             (Distribution Real (SpaceTime d) (TensorProduct Real (Lorentz.CoVector d) M))

-- Source: PhysLean (Lorentz.Vector.minkowskiProduct_eq_zero_forall_iff)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproduct_eq_zero_forall_iff : ∀ {d : Nat} (p : Lorentz.Vector d),
--   Iff
--     (∀ (q : Lorentz.Vector d),
--       Eq (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct p) q) 0)
--     (Eq p 0)

-- Source: PhysLean (SpaceTime.timeSpaceBasis_apply_inr)
-- [complex signature, not re-axiomatized]
-- spacetime_timespacebasis_apply_inr : ∀ {d : Nat} (c : SpeedOfLight) (i : Fin d),
--   Eq (Module.Basis.instFunLike.coe (SpaceTime.timeSpaceBasis c) (Sum.inr i))
--     (Module.Basis.instFunLike.coe Lorentz.Vector.basis (Sum.inr i))

-- Source: PhysLean (realLorentzTensor.toComplex.eq_1)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_tocomplex_eq_1 : ∀ {n : Nat} {c : Fin n → realLorentzTensor.Color},
--   Eq realLorentzTensor.toComplex
--     {
--       toFun := fun v =>
--         Finset.univ.sum fun i =>
--           instHSMul.hSMul (Finsupp.instFunLike.coe (EquivLike.toFunLike.coe (TensorSpecies.Tensor.basis c).repr v) i)
--             (Module.Basis.instFunLike.coe
--               (TensorSpecies.Tensor.basis (Function.comp realLorentzTensor.colorToComplex c))
--               (EquivLike.toFunLike.coe TensorSpecies.Tensor.ComponentIdx.complexify i)),
--       map_add' := ⋯, map_smul' := ⋯ }

-- Source: PhysLean (Lorentz.Velocity.mem_iff)
-- [complex signature, not re-axiomatized]
-- lorentz_velocity_mem_iff : ∀ {d : Nat} {v : Lorentz.Vector d},
--   Iff (Set.instMembership.mem (Lorentz.Velocity d) v)
--     (And (Eq (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct v) v) 1)
--       (Real.instLT.lt 0 v.timeComponent))

-- Source: PhysLean (complexLorentzTensor.rightAltRightUnit_eq_ofRat)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_rightaltrightunit_eq_ofrat : Eq complexLorentzTensor.rightAltRightUnit
--   (LinearMap.instFunLike.coe complexLorentzTensor.ofRat fun f => ite (Eq (f 0) (f 1)) 1 0)

-- Source: PhysLean (Lorentz.ContrMod.ext)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_ext : ∀ {d : Nat} {ψ ψ' : Lorentz.ContrMod d}, Eq ψ.val ψ'.val → Eq ψ ψ'

-- Source: PhysLean (complexLorentzTensor.rightAltRightUnit_eq_basis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_rightaltrightunit_eq_basis : Eq complexLorentzTensor.rightAltRightUnit
--   (Finset.univ.sum fun i =>
--     Module.Basis.instFunLike.coe
--       (TensorSpecies.Tensor.basis
--         (Matrix.vecCons complexLorentzTensor.Color.upR
--           (Matrix.vecCons complexLorentzTensor.Color.downR Matrix.vecEmpty)))
--       fun x =>
--       complexLorentzTensor.coContrUnit_eq_basis.match_1
--         (fun x =>
--           Fin
--             (complexLorentzTensor.repDim
--               (Matrix.vecCons complexLorentzTensor.Color.upR
--                 (Matrix.vecCons complexLorentzTensor.Color.downR Matrix.vecEmpty) x)))
--         x (fun _ => i) fun _ => i)

-- Source: PhysLean (LorentzGroup.boost_zero_inr_nat_succ_inr_0)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_zero_inr_nat_succ_inr_0 : ∀ {d : Nat} {β : Real} (hβ : Real.instLT.lt (abs β) 1) (i : Nat)
--   (h : instLTNat.lt (instHAdd.hAdd i 1) (instHAdd.hAdd d 1)),
--   Eq ((LorentzGroup.boost 0 β hβ).val (Sum.inr ⟨instHAdd.hAdd i 1, h⟩) (Sum.inr 0)) 0

-- Source: PhysLean (complexLorentzTensor.leftMetric_contr_altLeftMetric)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_leftmetric_contr_altleftmetric : Eq
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.contrT 2 1 2 ⋯)
--     (LinearMap.instFunLike.coe
--       (LinearMap.instFunLike.coe TensorSpecies.Tensor.prodT
--         (EquivLike.toFunLike.coe
--           (TensorSpecies.Tensorial.self complexLorentzTensor
--               (Matrix.vecCons complexLorentzTensor.Color.upL
--                 (Matrix.vecCons complexLorentzTensor.Color.upL Matrix.vecEmpty))).toTensor
--           complexLorentzTensor.leftMetric))
--       (EquivLike.toFunLike.coe
--         (TensorSpecies.Tensorial.self complexLorentzTensor
--             (Matrix.vecCons complexLorentzTensor.Color.downL
--               (Matrix.vecCons complexLorentzTensor.Color.downL Matrix.vecEmpty))).toTensor
--         complexLorentzTensor.altLeftMetric)))
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT (Matrix.vecCons 0 (Matrix.vecCons 1 Matrix.vecEmpty)) ⋯)
--     (EquivLike.toFunLike.coe
--       (TensorSpecies.Tensorial.self complexLorentzTensor
--           (Matrix.vecCons complexLorentzTensor.Color.upL
--             (Matrix.vecCons complexLorentzTensor.Color.downL Matrix.vecEmpty))).toTensor
--       complexLorentzTensor.leftAltLeftUnit))

-- Source: PhysLean (complexLorentzTensor.basis_downL_eq)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_basis_downl_eq : ∀ {i : Fin 2},
--   Eq (Module.Basis.instFunLike.coe (complexLorentzTensor.basis complexLorentzTensor.Color.downL) i)
--     (Module.Basis.instFunLike.coe Fermion.altLeftBasis i)

-- Source: PhysLean (realLorentzTensor.repDim_up)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_repdim_up : ∀ {d : Nat}, Eq ((realLorentzTensor d).repDim realLorentzTensor.Color.up) (instHAdd.hAdd 1 d)

-- Source: PhysLean (Lorentz.CoVector.instAddCommGroup)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_instaddcommgroup : {d : Nat} → AddCommGroup (Lorentz.CoVector d)

-- Source: PhysLean (complexLorentzTensor.termεR')
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_termεr' : Lean.ParserDescr

-- Source: PhysLean (LorentzGroup.genBoostAux₂_apply_basis)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_genboostaux₂_apply_basis : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem) (μ : Sum (Fin 1) (Fin d)),
--   Eq (LinearMap.instFunLike.coe (LorentzGroup.genBoostAux₂ u v) (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ))
--     (instHSMul.hSMul
--       (Real.instNeg.neg
--         (instHDiv.hDiv (instHMul.hMul (minkowskiMatrix μ μ) (instHAdd.hAdd (u.val μ) (v.val μ)))
--           (instHAdd.hAdd 1
--             (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct u.val)
--               v.val))))
--       (instHAdd.hAdd u.val v.val))

-- Source: PhysLean (Lorentz.CoVector.actionCLM)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_actionclm : {d : Nat} → (LorentzGroup d).Elem → ContinuousLinearMap (RingHom.id Real) (Lorentz.CoVector d) (Lorentz.CoVector d)

-- Source: PhysLean (Lorentz.Vector.instModuleReal)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_instmodulereal : {d : Nat} → Module Real (Lorentz.Vector d)

-- Source: PhysLean (CliffordAlgebra.equivOfIsometry)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_equivofisometry : {R : Type u_1} →
--   [inst : CommRing R] →
--     {M₁ : Type u_4} →
--       {M₂ : Type u_5} →
--         [inst_1 : AddCommGroup M₁] →
--           [inst_2 : AddCommGroup M₂] →
--             [inst_3 : Module R M₁] →
--               [inst_4 : Module R M₂] →
--                 {Q₁ : QuadraticForm R M₁} →
--                   {Q₂ : QuadraticForm R M₂} →
--                     QuadraticMap.IsometryEquiv Q₁ Q₂ → AlgEquiv R (CliffordAlgebra Q₁) (CliffordAlgebra Q₂)

-- Source: PhysLean (Lorentz.CoVector.smul_eq_mulVec)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_smul_eq_mulvec : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem) (p : Lorentz.CoVector d),
--   Eq (instHSMul.hSMul Λ p)
--     ((LorentzGroup.transpose (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ)).val.mulVec p)

-- Source: PhysLean (SpaceTime.schwartzAction_apply)
-- [complex signature, not re-axiomatized]
-- spacetime_schwartzaction_apply : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem) (η : SchwartzMap (SpaceTime d) Real) (x : SpaceTime d),
--   Eq
--     (SchwartzMap.instFunLike.coe
--       (ContinuousLinearMap.funLike.coe (MonoidHom.instFunLike.coe SpaceTime.schwartzAction Λ) η) x)
--     (SchwartzMap.instFunLike.coe η (instHSMul.hSMul (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ) x))

-- Source: PhysLean (LorentzGroup.genBoostAux₁_toMatrix_apply)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_genboostaux₁_tomatrix_apply : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem) (μ ν : Sum (Fin 1) (Fin d)),
--   Eq
--     (EquivLike.toFunLike.coe (LinearMap.toMatrix Lorentz.Vector.basis Lorentz.Vector.basis)
--       (LorentzGroup.genBoostAux₁ u v) μ ν)
--     (instHMul.hMul (minkowskiMatrix ν ν) (instHMul.hMul (instHMul.hMul 2 (u.val ν)) (v.val μ)))

-- Source: PhysLean (Lorentz.preContrCoUnitVal)
-- [complex signature, not re-axiomatized]
-- lorentz_precontrcounitval : (d : optParam Nat 3) → (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)).V.carrier

-- Source: PhysLean (Lorentz.SL2C.toSelfAdjointMap_basis)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_toselfadjointmap_basis : ∀ {M : Matrix.SpecialLinearGroup (Fin 2) Complex} (i : Sum (Fin 1) (Fin 3)),
--   Eq
--     (LinearMap.instFunLike.coe (Lorentz.SL2C.toSelfAdjointMap M)
--       (Module.Basis.instFunLike.coe PauliMatrix.pauliBasis' i))
--     (Finset.univ.sum fun j =>
--       instHSMul.hSMul ((MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M).val j i)
--         (Module.Basis.instFunLike.coe PauliMatrix.pauliBasis' j))

-- Source: PhysLean (Lorentz.Velocity.isPathConnected)
-- [complex signature, not re-axiomatized]
-- lorentz_velocity_ispathconnected : ∀ {d : Nat}, IsPathConnected Set.univ

-- Source: PhysLean (complexLorentzTensor.coMetric_eq_complexCoBasis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cometric_eq_complexcobasis : Eq complexLorentzTensor.coMetric
--   (instHSub.hSub
--     (instHSub.hSub
--       (instHSub.hSub
--         (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inl 0))
--             (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inl 0))))
--         (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 0))
--             (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 0)))))
--       (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--         (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 1))
--           (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 1)))))
--     (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 2))
--         (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 2)))))

-- Source: PhysLean (LorentzGroup.coe_inv)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_coe_inv : ∀ {d : Nat} {Λ : (LorentzGroup d).Elem},
--   Eq (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ).val (Matrix.inv.inv Λ.val)

-- Source: PhysLean (Lorentz.contrCoContract_hom_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcocontract_hom_tmul : ∀ {d : Nat} (ψ : (Lorentz.Contr d).V.carrier) (φ : (Lorentz.Co d).V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom Lorentz.contrCoContract.hom)
--       (TensorProduct.tmul Real ψ φ))
--     (dotProduct (Lorentz.ContrMod.toFin1dℝ ψ) (Lorentz.CoMod.toFin1dℝ φ))

-- Source: PhysLean (Lorentz.CoVector.map_apply_eq_basis_mulVec)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_map_apply_eq_basis_mulvec : ∀ {d : Nat} (f : LinearMap (RingHom.id Real) (Lorentz.CoVector d) (Lorentz.CoVector d)) (p : Lorentz.CoVector d),
--   Eq (LinearMap.instFunLike.coe f p)
--     ((EquivLike.toFunLike.coe (LinearMap.toMatrix Lorentz.CoVector.basis Lorentz.CoVector.basis) f).mulVec p)

-- Source: PhysLean (Lorentz.Vector.boost_time_eq)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_boost_time_eq : ∀ {d : Nat} (i : Fin d) (β : Real) (hβ : Real.instLT.lt (abs β) 1) (p : Lorentz.Vector d),
--   Eq (instHSMul.hSMul (LorentzGroup.boost i β hβ) p (Sum.inl 0))
--     (instHMul.hMul (LorentzGroup.γ β) (instHSub.hSub (p (Sum.inl 0)) (instHMul.hMul β (p (Sum.inr i)))))

-- Source: PhysLean (Lorentz.Vector.actionCLM)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_actionclm : {d : Nat} → (LorentzGroup d).Elem → ContinuousLinearMap (RingHom.id Real) (Lorentz.Vector d) (Lorentz.Vector d)

-- Source: PhysLean (Lorentz.contrContrContractField.matrix_eq_iff_eq_forall')
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_matrix_eq_iff_eq_forall' : ∀ {d : Nat} {Λ Λ' : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real},
--   Iff (∀ (v : (Lorentz.Contr d).V.carrier), Eq (Lorentz.ContrMod.mulVec Λ v) (Lorentz.ContrMod.mulVec Λ' v))
--     (∀ (w v : (Lorentz.Contr d).V.carrier),
--       Eq
--         (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--           (TensorProduct.tmul Real v (Lorentz.ContrMod.mulVec Λ w)))
--         (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--           (TensorProduct.tmul Real v (Lorentz.ContrMod.mulVec Λ' w))))

-- Source: PhysLean (Lorentz.Vector.causalCharacter_zero)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causalcharacter_zero : ∀ {d : Nat}, Eq (Lorentz.Vector.causalCharacter 0) Lorentz.Vector.CausalCharacter.lightLike

-- Source: PhysLean (LorentzGroup.isOrthochronous_mul)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_isorthochronous_mul : ∀ {d : Nat} {Λ Λ' : (LorentzGroup d).Elem},
--   LorentzGroup.IsOrthochronous Λ → LorentzGroup.IsOrthochronous Λ' → LorentzGroup.IsOrthochronous (instHMul.hMul Λ Λ')

-- Source: PhysLean (complexLorentzTensor.actionT_altLeftMetric)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_actiont_altleftmetric : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (instHSMul.hSMul g complexLorentzTensor.altLeftMetric) complexLorentzTensor.altLeftMetric

-- Source: PhysLean (Lorentz.contrBasis_toFin1dℝ)
-- [complex signature, not re-axiomatized]
-- lorentz_contrbasis_tofin1dℝ : ∀ {d : Nat} (i : Sum (Fin 1) (Fin d)),
--   Eq (Lorentz.ContrMod.toFin1dℝ (Module.Basis.instFunLike.coe (Lorentz.contrBasis d) i)) (Pi.single i 1)

-- Source: PhysLean (SpaceTime.timeSliceLinearEquiv_symm_apply)
-- [complex signature, not re-axiomatized]
-- spacetime_timeslicelinearequiv_symm_apply : ∀ {d : Nat} {M : Type} [inst : AddCommGroup M] [inst_1 : Module Real M] (c : SpeedOfLight) (f : Time → Space d → M),
--   Eq (EquivLike.toFunLike.coe (SpaceTime.timeSliceLinearEquiv c).symm f)
--     (EquivLike.toFunLike.coe (SpaceTime.timeSlice c).symm f)

-- Source: PhysLean (LorentzGroup.boost_zero_inr_0_inr_nat_succ)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_zero_inr_0_inr_nat_succ : ∀ {d : Nat} {β : Real} (hβ : Real.instLT.lt (abs β) 1) (i : Nat)
--   (h : instLTNat.lt (instHAdd.hAdd i 1) (instHAdd.hAdd d 1)),
--   Eq ((LorentzGroup.boost 0 β hβ).val (Sum.inr 0) (Sum.inr ⟨instHAdd.hAdd i 1, h⟩)) 0

-- Source: PhysLean (complexLorentzTensor.leftAltLeftUnit_eq_basis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_leftaltleftunit_eq_basis : Eq complexLorentzTensor.leftAltLeftUnit
--   (Finset.univ.sum fun i =>
--     Module.Basis.instFunLike.coe
--       (TensorSpecies.Tensor.basis
--         (Matrix.vecCons complexLorentzTensor.Color.upL
--           (Matrix.vecCons complexLorentzTensor.Color.downL Matrix.vecEmpty)))
--       fun x =>
--       complexLorentzTensor.coContrUnit_eq_basis.match_1
--         (fun x =>
--           Fin
--             (complexLorentzTensor.repDim
--               (Matrix.vecCons complexLorentzTensor.Color.upL
--                 (Matrix.vecCons complexLorentzTensor.Color.downL Matrix.vecEmpty) x)))
--         x (fun _ => i) fun _ => i)

-- Source: PhysLean (complexLorentzTensor.leftMetric_eq_leftBasis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_leftmetric_eq_leftbasis : Eq complexLorentzTensor.leftMetric
--   (instHAdd.hAdd
--     (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg
--       (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--         (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.leftBasis 0)
--           (Module.Basis.instFunLike.coe Fermion.leftBasis 1))))
--     (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.leftBasis 1)
--         (Module.Basis.instFunLike.coe Fermion.leftBasis 0))))

-- Source: PhysLean (Lorentz.Vector.minkowskiProductMap.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproductmap_eq_1 : ∀ {d : Nat} (p q : Lorentz.Vector d),
--   Eq (p.minkowskiProductMap q)
--     (LinearMap.instFunLike.coe TensorSpecies.Tensor.toField
--       (LinearMap.instFunLike.coe (TensorSpecies.Tensor.contrT 0 0 1 ⋯)
--         (LinearMap.instFunLike.coe
--           (LinearMap.instFunLike.coe TensorSpecies.Tensor.prodT
--             (LinearMap.instFunLike.coe (TensorSpecies.Tensor.contrT 1 0 2 ⋯)
--               (LinearMap.instFunLike.coe
--                 (LinearMap.instFunLike.coe TensorSpecies.Tensor.prodT
--                   (EquivLike.toFunLike.coe
--                     (TensorSpecies.Tensorial.self (realLorentzTensor d)
--                         (Matrix.vecCons realLorentzTensor.Color.down
--                           (Matrix.vecCons realLorentzTensor.Color.down Matrix.vecEmpty))).toTensor
--                     (realLorentzTensor.coMetric d)))
--                 (EquivLike.toFunLike.coe Lorentz.Vector.tensorial.toTensor p))))
--           (EquivLike.toFunLike.coe Lorentz.Vector.tensorial.toTensor q))))

-- Source: PhysLean (complexLorentzTensor.altRightMetric_eq_ofRat)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altrightmetric_eq_ofrat : Eq complexLorentzTensor.altRightMetric
--   (LinearMap.instFunLike.coe complexLorentzTensor.ofRat fun f =>
--     ite (And (Eq (f 0) 0) (Eq (f 1) 1)) 1 (ite (And (Eq (f 1) 0) (Eq (f 0) 1)) (-1) 0))

-- Source: PhysLean (LorentzGroup.boost_zero_inr_nat_succ_inl_0)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_zero_inr_nat_succ_inl_0 : ∀ {d : Nat} {β : Real} (hβ : Real.instLT.lt (abs β) 1) (i : Nat)
--   (h : instLTNat.lt (instHAdd.hAdd i 1) (instHAdd.hAdd d 1)),
--   Eq ((LorentzGroup.boost 0 β hβ).val (Sum.inr ⟨instHAdd.hAdd i 1, h⟩) (Sum.inl 0)) 0

-- Source: PhysLean (complexLorentzTensor.altLeftLeftUnit)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altleftleftunit : complexLorentzTensor.Tensor
--   (Matrix.vecCons complexLorentzTensor.Color.downL (Matrix.vecCons complexLorentzTensor.Color.upL Matrix.vecEmpty))

-- Source: PhysLean (Lorentz.«term_*ᵥ__1»)
-- [complex signature, not re-axiomatized]
-- lorentz_«term_*ᵥ__1» : Lean.TrailingParserDescr

-- Source: PhysLean (LorentzGroup.lorentzGroup_notation)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_lorentzgroup_notation : Lean.ParserDescr

-- Source: PhysLean (Lorentz.Vector.lightConeBoundary)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_lightconeboundary : {d : Nat} → Lorentz.Vector d → Set (Lorentz.Vector d)

-- Source: PhysLean (CliffordAlgebra.equivOfIsometry_refl)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_equivofisometry_refl : ∀ {R : Type u_1} [inst : CommRing R] {M₁ : Type u_4} [inst_1 : AddCommGroup M₁] [inst_2 : Module R M₁]
--   {Q₁ : QuadraticForm R M₁}, Eq (CliffordAlgebra.equivOfIsometry (QuadraticMap.IsometryEquiv.refl Q₁)) AlgEquiv.refl

-- Source: PhysLean (realLorentzTensor.τ_down_eq_up)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_τ_down_eq_up : ∀ {d : Nat}, Eq ((realLorentzTensor d).τ realLorentzTensor.Color.down) realLorentzTensor.Color.up

-- Source: PhysLean (SpaceTime.distDeriv)
-- [complex signature, not re-axiomatized]
-- spacetime_distderiv : {M : Type} →
--   {d : Nat} →
--     [inst : NormedAddCommGroup M] →
--       [inst_1 : NormedSpace Real M] →
--         Sum (Fin 1) (Fin d) →
--           LinearMap (RingHom.id Real) (Distribution Real (SpaceTime d) M) (Distribution Real (SpaceTime d) M)

-- Source: PhysLean (realLorentzTensor.Color.ctorElim)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_color_ctorelim : {motive : realLorentzTensor.Color → Sort u} →
--   (ctorIdx : Nat) →
--     (t : realLorentzTensor.Color) → Eq ctorIdx t.ctorIdx → realLorentzTensor.Color.ctorElimType ctorIdx → motive t

-- Source: PhysLean (Lorentz.Vector.isPastDirected)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_ispastdirected : {d : Nat} → Lorentz.Vector d → Prop

-- Source: PhysLean (Lorentz.coCoToMatrixRe_symm_expand_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_cocotomatrixre_symm_expand_tmul : ∀ {d : Nat} (M : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real),
--   Eq (EquivLike.toFunLike.coe Lorentz.coCoToMatrixRe.symm M)
--     (Finset.univ.sum fun i =>
--       Finset.univ.sum fun j =>
--         instHSMul.hSMul (M i j)
--           (TensorProduct.tmul Real (Module.Basis.instFunLike.coe (Lorentz.coBasis d) i)
--             (Module.Basis.instFunLike.coe (Lorentz.coBasis d) j)))

-- Source: PhysLean (LorentzGroup.detContinuous_eq_one)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_detcontinuous_eq_one : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Iff (Eq (ContinuousMap.instFunLike.coe LorentzGroup.detContinuous Λ) (EquivLike.toFunLike.coe Additive.toMul 0))
--     (Eq Λ.val.det 1)

-- Source: PhysLean (Lorentz.Vector.timeComponent_basis_sum_inr)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_timecomponent_basis_sum_inr : ∀ {d : Nat} (i : Fin d), Eq (Module.Basis.instFunLike.coe Lorentz.Vector.basis (Sum.inr i)).timeComponent 0

-- Source: PhysLean (CliffordAlgebra.ι_sq_scalar)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_ι_sq_scalar : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   (Q : QuadraticForm R M) (m : M),
--   Eq
--     (instHMul.hMul (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) m)
--       (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) m))
--     (RingHom.instFunLike.coe (algebraMap R (CliffordAlgebra Q)) (QuadraticMap.instFunLike.coe Q m))

-- Source: PhysLean (complexLorentzTensor.Color.downL.sizeOf_spec)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_color_downl_sizeof_spec : Eq (complexLorentzTensor.Color._sizeOf_inst.sizeOf complexLorentzTensor.Color.downL) 1

-- Source: PhysLean (SpaceTime.distDeriv.eq_1)
-- [complex signature, not re-axiomatized]
-- spacetime_distderiv_eq_1 : ∀ {M : Type} {d : Nat} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] (μ : Sum (Fin 1) (Fin d)),
--   Eq (SpaceTime.distDeriv μ)
--     {
--       toFun := fun f =>
--         have ev :=
--           { toFun := fun v => ContinuousLinearMap.funLike.coe v (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ),
--             map_add' := ⋯, map_smul' := ⋯, cont := ⋯ };
--         ev.comp (LinearMap.instFunLike.coe (Distribution.fderivD Real) f),
--       map_add' := ⋯, map_smul' := ⋯ }

-- Source: PhysLean (complexLorentzTensor.termδ')
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_termδ' : Lean.ParserDescr

-- Source: PhysLean (Lorentz.ContrMod.instModuleReal)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_instmodulereal : {d : Nat} → Module Real (Lorentz.ContrMod d)

-- Source: PhysLean (LorentzGroup.mul_minkowskiMatrix_mul_transpose)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_mul_minkowskimatrix_mul_transpose : ∀ {d : Nat} {Λ : (LorentzGroup d).Elem},
--   Eq (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (instHMul.hMul Λ.val minkowskiMatrix) Λ.val.transpose)
--     minkowskiMatrix

-- Source: PhysLean (SpaceTime.coord)
-- [complex signature, not re-axiomatized]
-- spacetime_coord : {d : Nat} → Fin (instHAdd.hAdd 1 d) → LinearMap (RingHom.id Real) (SpaceTime d) Real

-- Source: PhysLean (Lorentz.Vector.smul_add)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_smul_add : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem) (p q : Lorentz.Vector d),
--   Eq (instHSMul.hSMul Λ (instHAdd.hAdd p q)) (instHAdd.hAdd (instHSMul.hSMul Λ p) (instHSMul.hSMul Λ q))

-- Source: PhysLean (Lorentz.preContrCoUnitVal_expand_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_precontrcounitval_expand_tmul : ∀ {d : Nat},
--   Eq (Lorentz.preContrCoUnitVal d)
--     (Finset.univ.sum fun i =>
--       TensorProduct.tmul Real (Module.Basis.instFunLike.coe (Lorentz.contrBasis d) i)
--         (Module.Basis.instFunLike.coe (Lorentz.coBasis d) i))

-- Source: PhysLean (LorentzGroup.stepFunction)
/-- An auxiliary function used in the definition of `orthchroMapReal`.
This function takes all elements of `ℝ` less than `-1` to `-1`,
all elements of `R` greater than `1` to `1` and preserves all other elements.  -/
axiom lorentzgroup_stepfunction :
  Real → Real

-- Source: PhysLean (Lorentz.coBasisFin_repr_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_cobasisfin_repr_apply : ∀ {d : Nat} (p : (Lorentz.Co d).V.carrier) (i : Fin (instHAdd.hAdd 1 d)),
--   Eq (Finsupp.instFunLike.coe (EquivLike.toFunLike.coe (Lorentz.coBasisFin d).repr p) i)
--     (p.val (EquivLike.toFunLike.coe finSumFinEquiv.symm i))

-- Source: PhysLean (Lorentz.Vector.coord_differentiableAt)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_coord_differentiableat : ∀ {d : Nat} (i : Sum (Fin 1) (Fin d)) (v : Lorentz.Vector d), DifferentiableAt Real (fun v => v i) v

-- Source: PhysLean (complexLorentzTensor.altRightRightUnit_eq_ofRat)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altrightrightunit_eq_ofrat : Eq complexLorentzTensor.altRightRightUnit
--   (LinearMap.instFunLike.coe complexLorentzTensor.ofRat fun f => ite (Eq (f 0) (f 1)) 1 0)

-- Source: PhysLean (complexLorentzTensor.leftMetric)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_leftmetric : complexLorentzTensor.Tensor
--   (Matrix.vecCons complexLorentzTensor.Color.upL (Matrix.vecCons complexLorentzTensor.Color.upL Matrix.vecEmpty))

-- Source: PhysLean (LorentzGroup.toVelocity.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_tovelocity_eq_1 : ∀ {d : Nat} (Λ : Subtype fun x => SetLike.instMembership.mem (LorentzGroup.restricted d) x),
--   Eq (LorentzGroup.toVelocity Λ) ⟨LorentzGroup.toVector Λ.val, ⋯⟩

-- Source: PhysLean (Lorentz.Vector.timelike_time_component_ne_zero)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_timelike_time_component_ne_zero : ∀ {d : Nat} {v : Lorentz.Vector d}, Eq v.causalCharacter Lorentz.Vector.CausalCharacter.timeLike → Ne v.timeComponent 0

-- Source: PhysLean (Lorentz.coCoToMatrix_symm_expand_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_cocotomatrix_symm_expand_tmul : ∀ (M : Matrix (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3)) Complex),
--   Eq (EquivLike.toFunLike.coe Lorentz.coCoToMatrix.symm M)
--     (Finset.univ.sum fun i =>
--       Finset.univ.sum fun j =>
--         instHSMul.hSMul (M i j)
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexCoBasis i)
--             (Module.Basis.instFunLike.coe Lorentz.complexCoBasis j)))

-- Source: PhysLean (LorentzGroup.toProd_eq_transpose_η)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_toprod_eq_transpose_η : ∀ {d : Nat} {Λ : (LorentzGroup d).Elem},
--   Eq (MonoidHom.instFunLike.coe LorentzGroup.toProd Λ)
--     { fst := Λ.val, snd := MulOpposite.op (minkowskiMatrix.dual Λ.val) }

-- Source: PhysLean (CliffordAlgebra.hom_ext_iff)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_hom_ext_iff : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   {Q : QuadraticForm R M} {A : Type u_4} [inst_3 : Semiring A] [inst_4 : Algebra R A]
--   {f g : AlgHom R (CliffordAlgebra Q) A},
--   Iff (Eq f g) (Eq (f.toLinearMap.comp (CliffordAlgebra.ι Q)) (g.toLinearMap.comp (CliffordAlgebra.ι Q)))

-- Source: PhysLean (LorentzGroup.generalizedBoost_apply_mul_one_plus_contr)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_generalizedboost_apply_mul_one_plus_contr : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem) (x : Lorentz.Vector d),
--   Eq
--     (instHSMul.hSMul
--       (instHAdd.hAdd 1
--         (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct u.val) v.val))
--       (instHSMul.hSMul (LorentzGroup.generalizedBoost u v) x))
--     (instHSub.hSub
--       (instHAdd.hAdd
--         (instHSMul.hSMul
--           (instHAdd.hAdd 1
--             (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct u.val)
--               v.val))
--           x)
--         (instHSMul.hSMul
--           (instHMul.hMul
--             (instHMul.hMul 2
--               (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct x)
--                 u.val))
--             (instHAdd.hAdd 1
--               (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct u.val)
--                 v.val)))
--           v.val))
--       (instHSMul.hSMul
--         (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct x)
--           (instHAdd.hAdd u.val v.val))
--         (instHAdd.hAdd u.val v.val)))

-- Source: PhysLean (Lorentz.CoMod.instModuleReal)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_instmodulereal : {d : Nat} → Module Real (Lorentz.CoMod d)

-- Source: PhysLean (SpaceTime.distTimeSlice_distDeriv_inr)
-- [complex signature, not re-axiomatized]
-- spacetime_disttimeslice_distderiv_inr : ∀ {M : Type} {d : Nat} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] {c : SpeedOfLight} (i : Fin d)
--   (f : Distribution Real (SpaceTime d) M),
--   Eq
--     (EquivLike.toFunLike.coe (SpaceTime.distTimeSlice c)
--       (LinearMap.instFunLike.coe (SpaceTime.distDeriv (Sum.inr i)) f))
--     (LinearMap.instFunLike.coe (Space.distSpaceDeriv i) (EquivLike.toFunLike.coe (SpaceTime.distTimeSlice c) f))

-- Source: PhysLean (SpaceTime.distTensorDeriv_toTensor_basis_repr)
-- [complex signature, not re-axiomatized]
-- spacetime_disttensorderiv_totensor_basis_repr : ∀ {n d : Nat} {c : Fin n → realLorentzTensor.Color} {M : Type} [inst : NormedAddCommGroup M]
--   [inst_1 : InnerProductSpace Real M] [inst_2 : FiniteDimensional Real M] [inst_3 : (realLorentzTensor d).Tensorial c M]
--   {f : Distribution Real (SpaceTime d) M} (ε : SchwartzMap (SpaceTime d) Real)
--   (b : TensorSpecies.Tensor.ComponentIdx (Fin.append (Matrix.vecCons realLorentzTensor.Color.down Matrix.vecEmpty) c)),
--   Eq
--     (Finsupp.instFunLike.coe
--       (EquivLike.toFunLike.coe
--         (TensorSpecies.Tensor.basis (Fin.append (Matrix.vecCons realLorentzTensor.Color.down Matrix.vecEmpty) c)).repr
--         (EquivLike.toFunLike.coe TensorSpecies.Tensorial.prod.toTensor
--           (ContinuousLinearMap.funLike.coe (LinearMap.instFunLike.coe SpaceTime.distTensorDeriv f) ε)))
--       b)
--     (Finsupp.instFunLike.coe
--       (EquivLike.toFunLike.coe (TensorSpecies.Tensor.basis c).repr
--         (EquivLike.toFunLike.coe inst_3.toTensor
--           (ContinuousLinearMap.funLike.coe
--             (LinearMap.instFunLike.coe
--               (SpaceTime.distDeriv
--                 (EquivLike.toFunLike.coe Lorentz.CoVector.indexEquiv
--                   (EquivLike.toFunLike.coe TensorSpecies.Tensor.ComponentIdx.prodEquiv b).fst))
--               f)
--             ε)))
--       (EquivLike.toFunLike.coe TensorSpecies.Tensor.ComponentIdx.prodEquiv b).snd)

-- Source: PhysLean (LorentzGroup.coeForℤ₂_apply)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_coeforℤ₂_apply : ∀ (x : (Set.instInsert.insert (-1) (Set.instSingletonSet.singleton 1)).Elem),
--   Eq (ContinuousMap.instFunLike.coe LorentzGroup.coeForℤ₂ x)
--     (ite (Eq x ⟨1, LorentzGroup.coeForℤ₂._proof_1⟩) 1 (EquivLike.toFunLike.coe Additive.toMul 1))

-- Source: PhysLean (Lorentz.SL2C.toLorentzGroup_inl_inl)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_tolorentzgroup_inl_inl : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq ((MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M).val (Sum.inl 0) (Sum.inl 0))
--     (instHDiv.hDiv
--       (instHAdd.hAdd
--         (instHAdd.hAdd
--           (instHAdd.hAdd (instHPow.hPow (Complex.instNorm.norm (M.val 0 0)) 2)
--             (instHPow.hPow (Complex.instNorm.norm (M.val 0 1)) 2))
--           (instHPow.hPow (Complex.instNorm.norm (M.val 1 0)) 2))
--         (instHPow.hPow (Complex.instNorm.norm (M.val 1 1)) 2))
--       2)

-- Source: PhysLean (complexLorentzTensor.actionT_altRightRightUnit)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_actiont_altrightrightunit : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (instHSMul.hSMul g complexLorentzTensor.altRightRightUnit) complexLorentzTensor.altRightRightUnit

-- Source: PhysLean (complexLorentzTensor.contrCoUnit_eq_fromPairT)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrcounit_eq_frompairt : Eq complexLorentzTensor.contrCoUnit (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT Lorentz.contrCoUnitVal)

-- Source: PhysLean (complexLorentzTensor.altRightMetric_eq_fromConstPair)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altrightmetric_eq_fromconstpair : Eq complexLorentzTensor.altRightMetric (TensorSpecies.Tensor.fromConstPair Fermion.altRightMetric)

-- Source: PhysLean (realLorentzTensor.Color.down.sizeOf_spec)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_color_down_sizeof_spec : Eq (realLorentzTensor.Color._sizeOf_inst.sizeOf realLorentzTensor.Color.down) 1

-- Source: PhysLean (Lorentz.contrContrContractField.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_eq_1 : ∀ {d : Nat}, Eq Lorentz.contrContrContractField (ModuleCat.Hom.hom Lorentz.contrContrContract.hom)

-- Source: PhysLean (LorentzGroup.ofSpecialOrthogonal_symm_continuous)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_ofspecialorthogonal_symm_continuous : ∀ {d : Nat}, Continuous (EquivLike.toFunLike.coe LorentzGroup.ofSpecialOrthogonal.symm)

-- Source: PhysLean (complexLorentzTensor.contrBispinorUp)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrbispinorup : complexLorentzTensor.Tensor (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty) →
--   complexLorentzTensor.Tensor
--     (Matrix.vecCons complexLorentzTensor.Color.upL (Matrix.vecCons complexLorentzTensor.Color.upR Matrix.vecEmpty))

-- Source: PhysLean (minkowskiMatrix.mulVec_inr_i)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_mulvec_inr_i : ∀ {d : Nat} (v : Sum (Fin 1) (Fin d) → Real) (i : Fin d),
--   Eq (minkowskiMatrix.mulVec v (Sum.inr i)) (Real.instNeg.neg (v (Sum.inr i)))

-- Source: PhysLean (Lorentz.CoℂModule.toFin13ℂEquiv)
-- [complex signature, not re-axiomatized]
-- lorentz_coℂmodule_tofin13ℂequiv : LinearEquiv (RingHom.id Complex) Lorentz.CoℂModule (Sum (Fin 1) (Fin 3) → Complex)

-- Source: PhysLean (Lorentz.preContrMetric_apply_one)
-- [complex signature, not re-axiomatized]
-- lorentz_precontrmetric_apply_one : ∀ {d : Nat},
--   Eq
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V
--           (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Contr d)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom (Lorentz.preContrMetric d).hom) 1)
--     (Lorentz.preContrMetricVal d)

-- Source: PhysLean (complexLorentzTensor.contrT_ofRat_eq_sum_dropPairSection)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrt_ofrat_eq_sum_droppairsection : ∀ {n : Nat} {c : Fin (instHAdd.hAdd (instHAdd.hAdd n 1) 1) → complexLorentzTensor.Color}
--   {i j : Fin (instHAdd.hAdd (instHAdd.hAdd n 1) 1)} {h : And (Ne i j) (Eq (complexLorentzTensor.τ (c i)) (c j))}
--   (f : TensorSpecies.Tensor.ComponentIdx c → RatComplexNum),
--   Eq
--     (LinearMap.instFunLike.coe (TensorSpecies.Tensor.contrT n i j h)
--       (LinearMap.instFunLike.coe complexLorentzTensor.ofRat f))
--     (LinearMap.instFunLike.coe complexLorentzTensor.ofRat fun b =>
--       Finset.univ.sum fun x => instHMul.hMul (f x.val) (ite (Eq (x.val i).val (x.val j).val) 1 0))

-- Source: PhysLean (LorentzGroup.detContinuous_eq_iff_det_eq)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_detcontinuous_eq_iff_det_eq : ∀ {d : Nat} (Λ Λ' : (LorentzGroup d).Elem),
--   Iff
--     (Eq (ContinuousMap.instFunLike.coe LorentzGroup.detContinuous Λ)
--       (ContinuousMap.instFunLike.coe LorentzGroup.detContinuous Λ'))
--     (Eq Λ.val.det Λ'.val.det)

-- Source: PhysLean (complexLorentzTensor.altRightRightUnit_symm)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altrightrightunit_symm : Eq
--   (EquivLike.toFunLike.coe
--     (TensorSpecies.Tensorial.self complexLorentzTensor
--         (Matrix.vecCons complexLorentzTensor.Color.downR
--           (Matrix.vecCons complexLorentzTensor.Color.upR Matrix.vecEmpty))).toTensor
--     complexLorentzTensor.altRightRightUnit)
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT (Matrix.vecCons 1 (Matrix.vecCons 0 Matrix.vecEmpty)) ⋯)
--     (EquivLike.toFunLike.coe
--       (TensorSpecies.Tensorial.self complexLorentzTensor
--           (Matrix.vecCons complexLorentzTensor.Color.upR
--             (Matrix.vecCons complexLorentzTensor.Color.downR Matrix.vecEmpty))).toTensor
--       complexLorentzTensor.rightAltRightUnit))

-- Source: PhysLean (SpaceTime.instDistribMulActionElemMatrixSumFinOfNatNatRealLorentzGroupDistribution)
-- [complex signature, not re-axiomatized]
-- spacetime_instdistribmulactionelemmatrixsumfinofnatnatreallorentzgroupdistribution : {n d : Nat} →
--   {c : Fin n → realLorentzTensor.Color} →
--     {M : Type} →
--       [inst : NormedAddCommGroup M] →
--         [inst_1 : NormedSpace Real M] →
--           [(realLorentzTensor d).Tensorial c M] →
--             [T2Space M] → DistribMulAction (LorentzGroup d).Elem (Distribution Real (SpaceTime d) M)

-- Source: PhysLean (Lorentz.CoVector.indexEquiv.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_indexequiv_eq_1 : ∀ {d : Nat},
--   Eq Lorentz.CoVector.indexEquiv
--     ({ toFun := fun f => Fin.cast ⋯ (f 0), invFun := fun x j => Fin.cast ⋯ x, left_inv := ⋯, right_inv := ⋯ }.trans
--       finSumFinEquiv.symm)

-- Source: PhysLean (Lorentz.preContrCoUnit_symm)
-- [complex signature, not re-axiomatized]
-- lorentz_precontrcounit_symm : ∀ {d : Nat},
--   Eq
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V
--           (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom (Lorentz.preContrCoUnit d).hom) 1)
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)).V
--           (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom
--         (Action.instMonoidalCategory.whiskerLeft (Lorentz.Contr d) (Action.instCategory.id (Lorentz.Co d))).hom)
--       (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)).V
--             (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)).V).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom
--           ((Action.instBraidedCategory (ModuleCat Real) (LorentzGroup d).Elem).braiding (Lorentz.Co d)
--                 (Lorentz.Contr d)).hom.hom)
--         (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V
--               (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)).V).coe
--           ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom (Lorentz.preCoContrUnit d).hom) 1)))

-- Source: PhysLean (Lorentz.Vector.lightLike_iff_norm_sq_zero)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_lightlike_iff_norm_sq_zero : ∀ {d : Nat} (p : Lorentz.Vector d),
--   Iff (Eq p.causalCharacter Lorentz.Vector.CausalCharacter.lightLike)
--     (Eq (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct p) p) 0)

-- Source: PhysLean (Lorentz.Vector.spatialPart)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_spatialpart : {d : Nat} → Lorentz.Vector d → EuclideanSpace Real (Fin d)

-- Source: PhysLean (SpaceTime.instIsAddHaarMeasureVolume)
-- [complex signature, not re-axiomatized]
-- spacetime_instisaddhaarmeasurevolume : ∀ {d : Nat}, SpaceTime.instMeasureSpace.volume.IsAddHaarMeasure

-- Source: PhysLean (SpaceTime.instDistribMulActionElemMatrixSumFinOfNatNatRealLorentzGroupDistribution.congr_simp)
-- [complex signature, not re-axiomatized]
-- spacetime_instdistribmulactionelemmatrixsumfinofnatnatreallorentzgroupdistribution_congr_simp : ∀ {n d : Nat} {c : Fin n → realLorentzTensor.Color} {M : Type} [inst : NormedAddCommGroup M]
--   [inst_1 : NormedSpace Real M] [inst_2 : (realLorentzTensor d).Tensorial c M] [inst_3 : T2Space M],
--   Eq SpaceTime.instDistribMulActionElemMatrixSumFinOfNatNatRealLorentzGroupDistribution
--     SpaceTime.instDistribMulActionElemMatrixSumFinOfNatNatRealLorentzGroupDistribution

-- Source: PhysLean (Lorentz.SL2C.toSelfAdjointMap_similar_det)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_toselfadjointmap_similar_det : ∀ (M N : Matrix (Fin 2) (Fin 2) Complex) [Invertible M],
--   Eq
--     (MonoidHom.instFunLike.coe LinearMap.det
--       (Lorentz.SL2C.toSelfAdjointMap'
--         (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul M N)
--           (Matrix.inv.inv M))))
--     (MonoidHom.instFunLike.coe LinearMap.det (Lorentz.SL2C.toSelfAdjointMap' N))

-- Source: PhysLean (CliffordAlgebra.map)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_map : {R : Type u_1} →
--   [inst : CommRing R] →
--     {M₁ : Type u_4} →
--       {M₂ : Type u_5} →
--         [inst_1 : AddCommGroup M₁] →
--           [inst_2 : AddCommGroup M₂] →
--             [inst_3 : Module R M₁] →
--               [inst_4 : Module R M₂] →
--                 {Q₁ : QuadraticForm R M₁} →
--                   {Q₂ : QuadraticForm R M₂} →
--                     QuadraticMap.Isometry Q₁ Q₂ → AlgHom R (CliffordAlgebra Q₁) (CliffordAlgebra Q₂)

-- Source: PhysLean (LorentzGroup.detRep)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_detrep : {d : Nat} → MonoidHom (LorentzGroup d).Elem (Multiplicative (ZMod 2))

-- Source: PhysLean (CliffordAlgebra.ι.eq_1)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_ι_eq_1 : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   (Q : QuadraticForm R M),
--   Eq (CliffordAlgebra.ι Q) ((RingQuot.mkAlgHom R (CliffordAlgebra.Rel Q)).toLinearMap.comp (TensorAlgebra.ι R))

-- Source: PhysLean (Lorentz.Vector.timeComponent_squared_pos_of_timelike)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_timecomponent_squared_pos_of_timelike : ∀ {d : Nat} {v : Lorentz.Vector d},
--   Eq v.causalCharacter Lorentz.Vector.CausalCharacter.timeLike → Real.instLT.lt 0 (instHPow.hPow v.timeComponent 2)

-- Source: PhysLean (Lorentz.«_aux_PhysLean_Relativity_SL2C_SelfAdjoint___macroRules_Lorentz_termℂ²ˣ²_1»)
-- [complex signature, not re-axiomatized]
-- lorentz_«_aux_physlean_relativity_sl2c_selfadjoint___macrorules_lorentz_termℂ²ˣ²_1» : Lean.Macro

-- Source: PhysLean (LorentzGroup.boost_transpose_eq_self)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_transpose_eq_self : ∀ {d : Nat} (i : Fin d) {β : Real} (hβ : Real.instLT.lt (abs β) 1),
--   Eq (LorentzGroup.transpose (LorentzGroup.boost i β hβ)) (LorentzGroup.boost i β hβ)

-- Source: PhysLean (Lorentz.coContrToMatrixRe_ρ)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrtomatrixre_ρ : ∀ {d : Nat} (v : (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)).V.carrier)
--   (M : (LorentzGroup d).Elem),
--   Eq
--     (EquivLike.toFunLike.coe Lorentz.coContrToMatrixRe
--       (LinearMap.instFunLike.coe
--         (TensorProduct.map (MonoidHom.instFunLike.coe (Lorentz.Co d).ρ M)
--           (MonoidHom.instFunLike.coe (Lorentz.Contr d).ρ M))
--         v))
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.inv.inv M.val).transpose
--         (EquivLike.toFunLike.coe Lorentz.coContrToMatrixRe v))
--       M.val.transpose)

-- Source: PhysLean (realLorentzTensor.contrMetric.eq_1)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_contrmetric_eq_1 : ∀ (d : Nat), Eq (realLorentzTensor.contrMetric d) (TensorSpecies.metricTensor realLorentzTensor.Color.up)

-- Source: PhysLean (Lorentz.CoMod.ctorIdx)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_ctoridx : {d : Nat} → Lorentz.CoMod d → Nat

-- Source: PhysLean (Lorentz.contrCoToMatrix_ρ_symm)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcotomatrix_ρ_symm : ∀ (v : Matrix (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3)) Complex) (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (LinearMap.instFunLike.coe
--       (TensorProduct.map (MonoidHom.instFunLike.coe Lorentz.complexContr.ρ M)
--         (MonoidHom.instFunLike.coe Lorentz.complexCo.ρ M))
--       (EquivLike.toFunLike.coe Lorentz.contrCoToMatrix.symm v))
--     (EquivLike.toFunLike.coe Lorentz.contrCoToMatrix.symm
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--         (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--           (MonoidHom.instFunLike.coe LorentzGroup.toComplex (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M))
--           v)
--         (Matrix.inv.inv
--           (MonoidHom.instFunLike.coe LorentzGroup.toComplex
--             (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M)))))

-- Source: PhysLean (Lorentz.contrContrContractField.on_basis)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_on_basis : ∀ {d : Nat} (μ ν : Sum (Fin 1) (Fin d)),
--   Eq
--     (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--       (TensorProduct.tmul Real (Module.Basis.instFunLike.coe Lorentz.ContrMod.stdBasis μ)
--         (Module.Basis.instFunLike.coe Lorentz.ContrMod.stdBasis ν)))
--     (minkowskiMatrix μ ν)

-- Source: PhysLean (SpaceTime.term𝔁)
-- [complex signature, not re-axiomatized]
-- spacetime_term𝔁 : Lean.ParserDescr

-- Source: PhysLean (complexLorentzTensor.ofRat)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_ofrat : {n : Nat} →
--   {c : Fin n → complexLorentzTensor.Color} →
--     LinearMap RatComplexNum.toComplexNum (TensorSpecies.Tensor.ComponentIdx c → RatComplexNum)
--       (complexLorentzTensor.Tensor c)

-- Source: PhysLean (Lorentz.coBasis)
-- [complex signature, not re-axiomatized]
-- lorentz_cobasis : (d : optParam Nat 3) → Module.Basis (Sum (Fin 1) (Fin d)) Real (Lorentz.Co d).V.carrier

-- Source: PhysLean (complexLorentzTensor.basis_down_eq)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_basis_down_eq : ∀ {i : Fin 4},
--   Eq (Module.Basis.instFunLike.coe (complexLorentzTensor.basis complexLorentzTensor.Color.down) i)
--     (Module.Basis.instFunLike.coe Lorentz.complexCoBasisFin4 i)

-- Source: PhysLean (Lorentz.Vector.instAddCommGroup)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_instaddcommgroup : {d : Nat} → AddCommGroup (Lorentz.Vector d)

-- Source: PhysLean (Lorentz.Velocity.timeComponent_abs)
-- [complex signature, not re-axiomatized]
-- lorentz_velocity_timecomponent_abs : ∀ {d : Nat} (v : (Lorentz.Velocity d).Elem), Eq (abs v.val.timeComponent) v.val.timeComponent

-- Source: PhysLean (LorentzGroup.genBoostAux₂)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_genboostaux₂ : {d : Nat} →
--   (Lorentz.Velocity d).Elem →
--     (Lorentz.Velocity d).Elem → LinearMap (RingHom.id Real) (Lorentz.Vector d) (Lorentz.Vector d)

-- Source: PhysLean (Lorentz.ContrMod.one_mulVec)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_one_mulvec : ∀ {d : Nat} (v : Lorentz.ContrMod d), Eq (Lorentz.ContrMod.mulVec 1 v) v

-- Source: PhysLean (LorentzGroup.inv_neg)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_inv_neg : ∀ {d : Nat} {Λ : (LorentzGroup d).Elem},
--   Eq (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv (LorentzGroup.instNegElemMatrixSumFinOfNatNatReal.neg Λ))
--     (LorentzGroup.instNegElemMatrixSumFinOfNatNatReal.neg (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ))

-- Source: PhysLean (Lorentz.contr_preContrCoUnit)
-- [complex signature, not re-axiomatized]
-- lorentz_contr_precontrcounit : ∀ {d : Nat} (x : (Lorentz.Co d).V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj
--               (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)) (Lorentz.Co d)).V
--           (Lorentz.Co d).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom
--         (Action.instMonoidalCategory.leftUnitor (Lorentz.Co d)).hom.hom)
--       (((fun X Y => LinearMap.instFunLike)
--             (Action.instMonoidalCategory.tensorObj
--                 (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)) (Lorentz.Co d)).V
--             (Action.instMonoidalCategory.tensorObj
--                 (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)) (Lorentz.Co d)).V).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom
--           (Action.instMonoidalCategory.whiskerRight Lorentz.coContrContract (Lorentz.Co d)).hom)
--         (((fun X Y => LinearMap.instFunLike)
--               (Action.instMonoidalCategory.tensorObj (Lorentz.Co d)
--                   (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d))).V
--               (Action.instMonoidalCategory.tensorObj
--                   (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)) (Lorentz.Co d)).V).coe
--           ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom
--             (Action.instMonoidalCategory.associator (Lorentz.Co d) (Lorentz.Contr d) (Lorentz.Co d)).inv.hom)
--           (TensorProduct.tmul Real x
--             (((fun X Y => LinearMap.instFunLike)
--                   (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V
--                   (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)).V).coe
--               ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom (Lorentz.preContrCoUnit d).hom) 1)))))
--     x

-- Source: PhysLean (Lorentz.contrCoContract)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcocontract : {d : Nat} →
--   Action.instCategory.Hom (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d))
--     (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem))

-- Source: PhysLean (Lorentz.preCoContrUnit_apply_one)
-- [complex signature, not re-axiomatized]
-- lorentz_precocontrunit_apply_one : ∀ {d : Nat},
--   Eq
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V
--           (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom (Lorentz.preCoContrUnit d).hom) 1)
--     (Lorentz.preCoContrUnitVal d)

-- Source: PhysLean (complexLorentzTensor.altRightRightUnit_eq_fromConstPair)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altrightrightunit_eq_fromconstpair : Eq complexLorentzTensor.altRightRightUnit (TensorSpecies.Tensor.fromConstPair Fermion.altRightRightUnit)

-- Source: PhysLean (complexLorentzTensor.ofRat.eq_1)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_ofrat_eq_1 : ∀ {n : Nat} {c : Fin n → complexLorentzTensor.Color},
--   Eq complexLorentzTensor.ofRat
--     {
--       toFun := fun f =>
--         EquivLike.toFunLike.coe (TensorSpecies.Tensor.basis c).repr.symm
--           (EquivLike.toFunLike.coe
--             (Finsupp.linearEquivFunOnFinite Complex Complex
--                 ((j : Fin n) → Fin (complexLorentzTensor.repDim (c j)))).symm
--             fun j => RingHom.instFunLike.coe RatComplexNum.toComplexNum (f j)),
--       map_add' := ⋯, map_smul' := ⋯ }

-- Source: PhysLean (LorentzGroup.basis_minkowskiProduct_genBoostAux₁_add_genBoostAux₂)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_basis_minkowskiproduct_genboostaux₁_add_genboostaux₂ : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem) (μ ν : Sum (Fin 1) (Fin d)),
--   Eq
--     (ContinuousLinearMap.funLike.coe
--       (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct
--         (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ))
--       (instHAdd.hAdd
--         (LinearMap.instFunLike.coe (LorentzGroup.genBoostAux₁ u v)
--           (Module.Basis.instFunLike.coe Lorentz.Vector.basis ν))
--         (LinearMap.instFunLike.coe (LorentzGroup.genBoostAux₂ u v)
--           (Module.Basis.instFunLike.coe Lorentz.Vector.basis ν))))
--     (instHMul.hMul (instHMul.hMul (minkowskiMatrix μ μ) (minkowskiMatrix ν ν))
--       (instHSub.hSub (instHMul.hMul (instHMul.hMul 2 (u.val ν)) (v.val μ))
--         (instHMul.hMul (instHMul.hMul (instHAdd.hAdd (u.val μ) (v.val μ)) (instHAdd.hAdd (u.val ν) (v.val ν)))
--           (Real.instInv.inv
--             (instHAdd.hAdd 1
--               (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct u.val)
--                 v.val))))))

-- Source: PhysLean (Lorentz.ContrℂModule.toFin13ℂEquiv)
-- [complex signature, not re-axiomatized]
-- lorentz_contrℂmodule_tofin13ℂequiv : LinearEquiv (RingHom.id Complex) Lorentz.ContrℂModule (Sum (Fin 1) (Fin 3) → Complex)

-- Source: PhysLean (Lorentz.CoMod.stdBasis_toFin1dℝEquiv_apply_same)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_stdbasis_tofin1dℝequiv_apply_same : ∀ {d : Nat} (μ : Sum (Fin 1) (Fin d)),
--   Eq (EquivLike.toFunLike.coe Lorentz.CoMod.toFin1dℝEquiv (Module.Basis.instFunLike.coe Lorentz.CoMod.stdBasis μ) μ) 1

-- Source: PhysLean (Lorentz.Vector.neg_smul)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_neg_smul : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem) (p : Lorentz.Vector d),
--   Eq (instHSMul.hSMul (LorentzGroup.instNegElemMatrixSumFinOfNatNatReal.neg Λ) p)
--     (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg (instHSMul.hSMul Λ p))

-- Source: PhysLean (SpaceTime.properTime_pos_ofTimeLike)
-- [complex signature, not re-axiomatized]
-- spacetime_propertime_pos_oftimelike : ∀ {d : Nat} (q p : SpaceTime d),
--   Eq (Lorentz.Vector.causalCharacter (instHSub.hSub p q)) Lorentz.Vector.CausalCharacter.timeLike →
--     Real.instLT.lt 0 (q.properTime p)

-- Source: PhysLean (LorentzGroup.transpose_mem_rotations)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_transpose_mem_rotations : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Iff (SetLike.instMembership.mem (LorentzGroup.Rotations d) (LorentzGroup.transpose Λ))
--     (SetLike.instMembership.mem (LorentzGroup.Rotations d) Λ)

-- Source: PhysLean (Lorentz.Contr)
-- [complex signature, not re-axiomatized]
-- lorentz_contr : (d : Nat) → Rep Real (LorentzGroup d).Elem

-- Source: PhysLean (Lorentz.Vector.interiorFutureLightCone)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_interiorfuturelightcone : {d : Nat} → Lorentz.Vector d → Set (Lorentz.Vector d)

-- Source: PhysLean (Lorentz.Vector.CausalCharacter.ctorElimType)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causalcharacter_ctorelimtype : {motive : Lorentz.Vector.CausalCharacter → Sort u} → Nat → Sort (max 1 u)

-- Source: PhysLean (Lorentz.ContrMod.toSelfAdjoint_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_toselfadjoint_apply : ∀ (x : Lorentz.ContrMod 3),
--   Eq (EquivLike.toFunLike.coe Lorentz.ContrMod.toSelfAdjoint x)
--     (instHSub.hSub
--       (instHSub.hSub
--         (instHSub.hSub (instHSMul.hSMul (x.toFin1dℝ (Sum.inl 0)) ⟨PauliMatrix.pauliMatrix (Sum.inl 0), ⋯⟩)
--           (instHSMul.hSMul (x.toFin1dℝ (Sum.inr 0)) ⟨PauliMatrix.pauliMatrix (Sum.inr 0), ⋯⟩))
--         (instHSMul.hSMul (x.toFin1dℝ (Sum.inr 1)) ⟨PauliMatrix.pauliMatrix (Sum.inr 1), ⋯⟩))
--       (instHSMul.hSMul (x.toFin1dℝ (Sum.inr 2)) ⟨PauliMatrix.pauliMatrix (Sum.inr 2), ⋯⟩))

-- Source: PhysLean (Lorentz.CoMod.mulVec_val)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_mulvec_val : ∀ {d : Nat} (M : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real) (v : Lorentz.CoMod d),
--   Eq (Lorentz.CoMod.mulVec M v).val (M.mulVec v.val)

-- Source: PhysLean (complexLorentzTensor.complexLorentzTensorSyntax)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_complexlorentztensorsyntax : Lean.ParserDescr

-- Source: PhysLean (LorentzGroup.boost_zero_inr_succ_inr_0)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_zero_inr_succ_inr_0 : ∀ {d : Nat} {β : Real} (hβ : Real.instLT.lt (abs β) 1) (i : Fin d),
--   Eq ((LorentzGroup.boost 0 β hβ).val (Sum.inr i.succ) (Sum.inr 0)) 0

-- Source: PhysLean (Lorentz.Vector.CausalCharacter.ofNat_ctorIdx)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causalcharacter_ofnat_ctoridx : ∀ (x : Lorentz.Vector.CausalCharacter), Eq (Lorentz.Vector.CausalCharacter.ofNat x.ctorIdx) x

-- Source: PhysLean (complexLorentzTensor.contrMetric_eq_complexContrBasis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrmetric_eq_complexcontrbasis : Eq complexLorentzTensor.contrMetric
--   (instHSub.hSub
--     (instHSub.hSub
--       (instHSub.hSub
--         (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inl 0))
--             (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inl 0))))
--         (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 0))
--             (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 0)))))
--       (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--         (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 1))
--           (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 1)))))
--     (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 2))
--         (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 2)))))

-- Source: PhysLean (LorentzGroup.orthchroMap)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_orthchromap : {d : Nat} → ContinuousMap (LorentzGroup d).Elem (Multiplicative (ZMod 2))

-- Source: PhysLean (Lorentz.Vector.CausalCharacter.ctorIdx)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causalcharacter_ctoridx : Lorentz.Vector.CausalCharacter → Nat

-- Source: PhysLean (minkowskiMatrix.dual_eta)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_dual_eta : ∀ {d : Nat}, Eq (minkowskiMatrix.dual minkowskiMatrix) minkowskiMatrix

-- Source: PhysLean (Lorentz.contrContrContractField.ge_abs_inner_product)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_ge_abs_inner_product : ∀ {d : Nat} (v w : (Lorentz.Contr d).V.carrier),
--   Real.instLE.le
--     (instHSub.hSub (instHMul.hMul (v.val (Sum.inl 0)) (w.val (Sum.inl 0)))
--       (Real.norm.norm
--         ((PiLp.innerProductSpace fun x => Real).inner Real (Lorentz.ContrMod.toSpace v) (Lorentz.ContrMod.toSpace w))))
--     (LinearMap.instFunLike.coe Lorentz.contrContrContractField (TensorProduct.tmul Real v w))

-- Source: PhysLean (LorentzGroup.γ)
/-- The Lorentz factor (aka gamma factor or Lorentz term).  -/
axiom lorentzgroup_γ :
  Real → Real

-- Source: PhysLean (LorentzGroup.transpose.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_transpose_eq_1 : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem), Eq (LorentzGroup.transpose Λ) ⟨Λ.val.transpose, ⋯⟩

-- Source: PhysLean (Lorentz.CoVector.apply_sub)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_apply_sub : ∀ {d : Nat} (v w : Lorentz.CoVector d) (i : Sum (Fin 1) (Fin d)), Eq (instHSub.hSub v w i) (instHSub.hSub (v i) (w i))

-- Source: PhysLean (SpaceTime.spaceTime_integral_eq_time_space_integral)
-- [complex signature, not re-axiomatized]
-- spacetime_spacetime_integral_eq_time_space_integral : ∀ {M : Type u_1} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] {d : Nat} (c : SpeedOfLight)
--   (f : SpaceTime d → M),
--   Eq (MeasureTheory.integral SpaceTime.instMeasureSpace.volume fun x => f x)
--     (instHSMul.hSMul c.val
--       (MeasureTheory.integral (measureSpaceOfInnerProductSpace.volume.prod measureSpaceOfInnerProductSpace.volume)
--         fun tx => f (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c).symm tx)))

-- Source: PhysLean (Lorentz.ContrMod.norm)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_norm : {d : Nat} → NormedAddCommGroup (Lorentz.ContrMod d)

-- Source: PhysLean (LorentzGroup.isOrthochronous_iff_not_neg)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_isorthochronous_iff_not_neg : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Iff (LorentzGroup.IsOrthochronous Λ)
--     (Not (LorentzGroup.IsOrthochronous (LorentzGroup.instNegElemMatrixSumFinOfNatNatReal.neg Λ)))

-- Source: PhysLean (LorentzGroup.toVelocity)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_tovelocity : {d : Nat} → (Subtype fun x => SetLike.instMembership.mem (LorentzGroup.restricted d) x) → (Lorentz.Velocity d).Elem

-- Source: PhysLean (Lorentz.ContrMod.ctorIdx)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_ctoridx : {d : Nat} → Lorentz.ContrMod d → Nat

-- Source: PhysLean (LorentzGroup.toRotation.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_torotation_eq_1 : ∀ {d : Nat} (Λ : Subtype fun x => SetLike.instMembership.mem (LorentzGroup.restricted d) x),
--   Eq (LorentzGroup.toRotation Λ)
--     ⟨instHMul.hMul
--         (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv
--           (LorentzGroup.generalizedBoost 0 (LorentzGroup.toVelocity Λ)))
--         Λ.val,
--       ⋯⟩

-- Source: PhysLean (Lorentz.Vector.spatialCLM.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_spatialclm_eq_1 : ∀ (d : Nat),
--   Eq (Lorentz.Vector.spatialCLM d)
--     { toFun := fun v => { ofLp := fun i => v (Sum.inr i) }, map_add' := ⋯, map_smul' := ⋯, cont := ⋯ }

-- Source: PhysLean (Lorentz.Vector.minkowskiProduct_eq_timeComponent_spatialPart)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproduct_eq_timecomponent_spatialpart : ∀ {d : Nat} (p q : Lorentz.Vector d),
--   Eq (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct p) q)
--     (instHSub.hSub (instHMul.hMul p.timeComponent q.timeComponent)
--       ((PiLp.innerProductSpace fun x => Real).inner Real p.spatialPart q.spatialPart))

-- Source: PhysLean (Lorentz.CoVector.instModuleReal)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_instmodulereal : {d : Nat} → Module Real (Lorentz.CoVector d)

-- Source: PhysLean (Lorentz.SL2C.toMatrix_mem_lorentzGroup)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_tomatrix_mem_lorentzgroup : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Set.instMembership.mem (LorentzGroup 3) (MonoidHom.instFunLike.coe Lorentz.SL2C.toMatrix M)

-- Source: PhysLean (Lorentz.Vector.norm_eq_equivEuclid)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_norm_eq_equiveuclid : ∀ (d : Nat) (v : Lorentz.Vector d),
--   Eq ((Lorentz.Vector.instNorm d).norm v)
--     ((PiLp.instNorm 2 fun x => Real).norm (EquivLike.toFunLike.coe (Lorentz.Vector.equivEuclid d) v))

-- Source: PhysLean (complexLorentzTensor.contrCoUnit)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrcounit : complexLorentzTensor.Tensor
--   (Matrix.vecCons complexLorentzTensor.Color.up (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty))

-- Source: PhysLean (complexLorentzTensor.instFintypeLeftColorMkFin)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_instfintypeleftcolormkfin : {n : Nat} → {c : Fin n → complexLorentzTensor.Color} → Fintype (IndexNotation.OverColor.mk c).left

-- Source: PhysLean (LorentzGroup.ofSpecialOrthogonal)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_ofspecialorthogonal : {d : Nat} →
--   MulEquiv (Subtype fun x => SetLike.instMembership.mem (Matrix.specialOrthogonalGroup (Fin d) Real) x)
--     (Subtype fun x => SetLike.instMembership.mem (LorentzGroup.Rotations d) x)

-- Source: PhysLean (Lorentz.inclCongrRealLorentz.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_inclcongrreallorentz_eq_1 : Eq Lorentz.inclCongrRealLorentz
--   { toFun := fun v => { val := Function.comp Complex.ofReal v.toFin1dℝ },
--     map_add' := Lorentz.inclCongrRealLorentz._proof_1, map_smul' := Lorentz.inclCongrRealLorentz._proof_2 }

-- Source: PhysLean (realLorentzTensor.coMetric.eq_1)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_cometric_eq_1 : ∀ (d : Nat), Eq (realLorentzTensor.coMetric d) (TensorSpecies.metricTensor realLorentzTensor.Color.down)

-- Source: PhysLean (complexLorentzTensor.rightMetric_eq_fromConstPair)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_rightmetric_eq_fromconstpair : Eq complexLorentzTensor.rightMetric (TensorSpecies.Tensor.fromConstPair Fermion.rightMetric)

-- Source: PhysLean (Lorentz.contrMetric)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmetric : Action.instCategory.Hom
--   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--   (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexContr)

-- Source: PhysLean (Lorentz.contrContrContractField.as_sum_toSpace)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_as_sum_tospace : ∀ {d : Nat} (x y : (Lorentz.Contr d).V.carrier),
--   Eq (LinearMap.instFunLike.coe Lorentz.contrContrContractField (TensorProduct.tmul Real x y))
--     (instHSub.hSub (instHMul.hMul (x.val (Sum.inl 0)) (y.val (Sum.inl 0)))
--       ((PiLp.innerProductSpace fun x => Real).inner Real (Lorentz.ContrMod.toSpace x) (Lorentz.ContrMod.toSpace y)))

-- Source: PhysLean (Lorentz.contr_contrCoUnit)
-- [complex signature, not re-axiomatized]
-- lorentz_contr_contrcounit : ∀ (x : Lorentz.complexCo.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj
--               (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--               Lorentz.complexCo).V
--           Lorentz.complexCo.V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--         (Action.instMonoidalCategory.leftUnitor Lorentz.complexCo).hom.hom)
--       (((fun X Y => LinearMap.instFunLike)
--             (Action.instMonoidalCategory.tensorObj
--                 (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr) Lorentz.complexCo).V
--             (Action.instMonoidalCategory.tensorObj
--                 (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--                 Lorentz.complexCo).V).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--           (Action.instMonoidalCategory.whiskerRight Lorentz.coContrContraction Lorentz.complexCo).hom)
--         (((fun X Y => LinearMap.instFunLike)
--               (Action.instMonoidalCategory.tensorObj Lorentz.complexCo
--                   (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo)).V
--               (Action.instMonoidalCategory.tensorObj
--                   (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr)
--                   Lorentz.complexCo).V).coe
--           ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--             (Action.instMonoidalCategory.associator Lorentz.complexCo Lorentz.complexContr Lorentz.complexCo).inv.hom)
--           (TensorProduct.tmul Complex x
--             (((fun X Y => LinearMap.instFunLike)
--                   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                   (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo).V).coe
--               ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.contrCoUnit.hom) 1)))))
--     x

-- Source: PhysLean (Lorentz.inclCongrRealLorentz)
-- [complex signature, not re-axiomatized]
-- lorentz_inclcongrreallorentz : LinearMap Complex.ofRealHom (Lorentz.ContrMod 3) Lorentz.complexContr.V.carrier

-- Source: PhysLean (Lorentz.SL2C.toLorentzGroup_apply_coe)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_tolorentzgroup_apply_coe : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M).val (MonoidHom.instFunLike.coe Lorentz.SL2C.toMatrix M)

-- Source: PhysLean (complexLorentzTensor.altLeftMetric_contr_leftMetric)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altleftmetric_contr_leftmetric : Eq
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.contrT 2 1 2 ⋯)
--     (LinearMap.instFunLike.coe
--       (LinearMap.instFunLike.coe TensorSpecies.Tensor.prodT
--         (EquivLike.toFunLike.coe
--           (TensorSpecies.Tensorial.self complexLorentzTensor
--               (Matrix.vecCons complexLorentzTensor.Color.downL
--                 (Matrix.vecCons complexLorentzTensor.Color.downL Matrix.vecEmpty))).toTensor
--           complexLorentzTensor.altLeftMetric))
--       (EquivLike.toFunLike.coe
--         (TensorSpecies.Tensorial.self complexLorentzTensor
--             (Matrix.vecCons complexLorentzTensor.Color.upL
--               (Matrix.vecCons complexLorentzTensor.Color.upL Matrix.vecEmpty))).toTensor
--         complexLorentzTensor.leftMetric)))
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT (Matrix.vecCons 0 (Matrix.vecCons 1 Matrix.vecEmpty)) ⋯)
--     (EquivLike.toFunLike.coe
--       (TensorSpecies.Tensorial.self complexLorentzTensor
--           (Matrix.vecCons complexLorentzTensor.Color.downL
--             (Matrix.vecCons complexLorentzTensor.Color.upL Matrix.vecEmpty))).toTensor
--       complexLorentzTensor.altLeftLeftUnit))

-- Source: PhysLean (minkowskiMatrix.as_diagonal)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_as_diagonal : ∀ {d : Nat}, Eq minkowskiMatrix (Matrix.diagonal (Sum.elim 1 (-1)))

-- Source: PhysLean (Lorentz.ContrℂModule.instModuleComplex)
-- [complex signature, not re-axiomatized]
-- lorentz_contrℂmodule_instmodulecomplex : Module Complex Lorentz.ContrℂModule

-- Source: PhysLean (complexLorentzTensor.Color.downR.sizeOf_spec)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_color_downr_sizeof_spec : Eq (complexLorentzTensor.Color._sizeOf_inst.sizeOf complexLorentzTensor.Color.downR) 1

-- Source: PhysLean (LorentzGroup.not_isOrthochronous_iff_le_zero)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_not_isorthochronous_iff_le_zero : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Iff (Not (LorentzGroup.IsOrthochronous Λ)) (Real.instLE.le (Λ.val (Sum.inl 0) (Sum.inl 0)) 0)

-- Source: PhysLean (Lorentz.ContrMod.stdBasis_repr_symm_apply_val)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_stdbasis_repr_symm_apply_val : ∀ {d : Nat} (a : Finsupp (Sum (Fin 1) (Fin d)) Real) (a_1 : Sum (Fin 1) (Fin d)),
--   Eq ((EquivLike.toFunLike.coe Lorentz.ContrMod.stdBasis.repr.symm a).val a_1) (Finsupp.instFunLike.coe a a_1)

-- Source: PhysLean (Lorentz.ContrMod.stdBasis)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_stdbasis : {d : Nat} → Module.Basis (Sum (Fin 1) (Fin d)) Real (Lorentz.ContrMod d)

-- Source: PhysLean (LorentzGroup.timeCompCont)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_timecompcont : {d : Nat} → ContinuousMap (LorentzGroup d).Elem Real

-- Source: PhysLean (Lorentz.coContrContraction)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrcontraction : Action.instCategory.Hom (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr)
--   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))

-- Source: PhysLean (LorentzGroup.transpose_inv)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_transpose_inv : ∀ {d : Nat} {Λ : (LorentzGroup d).Elem},
--   Eq (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv (LorentzGroup.transpose Λ))
--     (LorentzGroup.transpose (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ))

-- Source: PhysLean (realLorentzTensor.actionT_coMetric)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_actiont_cometric : ∀ {d : Nat} (g : (LorentzGroup d).Elem),
--   Eq (instHSMul.hSMul g (realLorentzTensor.coMetric d)) (realLorentzTensor.coMetric d)

-- Source: PhysLean (Lorentz.CoMod.val)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_val : {d : Nat} → Lorentz.CoMod d → Sum (Fin 1) (Fin d) → Real

-- Source: PhysLean (Lorentz.CoVector.indexEquiv)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_indexequiv : {d : Nat} →
--   Equiv (TensorSpecies.Tensor.ComponentIdx (Matrix.vecCons realLorentzTensor.Color.down Matrix.vecEmpty))
--     (Sum (Fin 1) (Fin d))

-- Source: PhysLean (Lorentz.preContrMetricVal)
-- [complex signature, not re-axiomatized]
-- lorentz_precontrmetricval : (d : optParam Nat 3) → (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Contr d)).V.carrier

-- Source: PhysLean (Lorentz.complexContrBasisFin4_apply_three)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcontrbasisfin4_apply_three : Eq (Module.Basis.instFunLike.coe Lorentz.complexContrBasisFin4 3)
--   (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 2))

-- Source: PhysLean (complexLorentzTensor.coMetric_eq_fromConstPair)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cometric_eq_fromconstpair : Eq complexLorentzTensor.coMetric (TensorSpecies.Tensor.fromConstPair Lorentz.coMetric)

-- Source: PhysLean (LorentzGroup.isOrthochronous_iff_of_orthchroMap_eq)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_isorthochronous_iff_of_orthchromap_eq : ∀ {d : Nat} {Λ Λ' : (LorentzGroup d).Elem},
--   Eq (ContinuousMap.instFunLike.coe LorentzGroup.orthchroMap Λ)
--       (ContinuousMap.instFunLike.coe LorentzGroup.orthchroMap Λ') →
--     Iff (LorentzGroup.IsOrthochronous Λ) (LorentzGroup.IsOrthochronous Λ')

-- Source: PhysLean (Lorentz.CoVector.toTensor_symm_basis)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_totensor_symm_basis : ∀ {d : Nat} (μ : Sum (Fin 1) (Fin d)),
--   Eq
--     (EquivLike.toFunLike.coe Lorentz.CoVector.tensorial.toTensor.symm
--       (Module.Basis.instFunLike.coe
--         (TensorSpecies.Tensor.basis (Matrix.vecCons realLorentzTensor.Color.down Matrix.vecEmpty))
--         (EquivLike.toFunLike.coe Lorentz.CoVector.indexEquiv.symm μ)))
--     (Module.Basis.instFunLike.coe Lorentz.CoVector.basis μ)

-- Source: PhysLean (LorentzGroup.transpose_mul)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_transpose_mul : ∀ {d : Nat} {Λ Λ' : (LorentzGroup d).Elem},
--   Eq (LorentzGroup.transpose (instHMul.hMul Λ Λ'))
--     (instHMul.hMul (LorentzGroup.transpose Λ') (LorentzGroup.transpose Λ))

-- Source: PhysLean (realLorentzTensor.«termℝT(_,_)»)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_«termℝt(_,_)» : Lean.ParserDescr

-- Source: PhysLean (Lorentz.contrCoContraction)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcocontraction : Action.instCategory.Hom (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo)
--   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))

-- Source: PhysLean (Lorentz.Vector.minkowskiProduct_toCoord_minkowskiMatrix)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproduct_tocoord_minkowskimatrix : ∀ {d : Nat} (p q : Lorentz.Vector d),
--   Eq (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct p) q)
--     (Finset.univ.sum fun μ => instHMul.hMul (instHMul.hMul (minkowskiMatrix μ μ) (p μ)) (q μ))

-- Source: PhysLean (complexLorentzTensor.contrMetric_eq_basis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrmetric_eq_basis : Eq complexLorentzTensor.contrMetric
--   (instHSub.hSub
--     (instHSub.hSub
--       (instHSub.hSub
--         (Module.Basis.instFunLike.coe
--           (TensorSpecies.Tensor.basis
--             (Matrix.vecCons complexLorentzTensor.Color.up
--               (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty)))
--           fun x =>
--           complexLorentzTensor.coMetric_eq_basis.match_1
--             (fun x =>
--               Fin
--                 (complexLorentzTensor.repDim
--                   (Matrix.vecCons complexLorentzTensor.Color.up
--                     (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty) x)))
--             x (fun _ => 0) fun _ => 0)
--         (Module.Basis.instFunLike.coe
--           (TensorSpecies.Tensor.basis
--             (Matrix.vecCons complexLorentzTensor.Color.up
--               (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty)))
--           fun x =>
--           complexLorentzTensor.coMetric_eq_basis.match_1
--             (fun x =>
--               Fin
--                 (complexLorentzTensor.repDim
--                   (Matrix.vecCons complexLorentzTensor.Color.up
--                     (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty) x)))
--             x (fun _ => 1) fun _ => 1))
--       (Module.Basis.instFunLike.coe
--         (TensorSpecies.Tensor.basis
--           (Matrix.vecCons complexLorentzTensor.Color.up (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty)))
--         fun x =>
--         complexLorentzTensor.coMetric_eq_basis.match_1
--           (fun x =>
--             Fin
--               (complexLorentzTensor.repDim
--                 (Matrix.vecCons complexLorentzTensor.Color.up
--                   (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty) x)))
--           x (fun _ => 2) fun _ => 2))
--     (Module.Basis.instFunLike.coe
--       (TensorSpecies.Tensor.basis
--         (Matrix.vecCons complexLorentzTensor.Color.up (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty)))
--       fun x =>
--       complexLorentzTensor.coMetric_eq_basis.match_1
--         (fun x =>
--           Fin
--             (complexLorentzTensor.repDim
--               (Matrix.vecCons complexLorentzTensor.Color.up
--                 (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty) x)))
--         x (fun _ => 3) fun _ => 3))

-- Source: PhysLean (Lorentz.Vector.minkowskiProductMap)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproductmap : {d : Nat} → Lorentz.Vector d → Lorentz.Vector d → Real

-- Source: PhysLean (Lorentz.CoℂModule.val)
-- [complex signature, not re-axiomatized]
-- lorentz_coℂmodule_val : Lorentz.CoℂModule → Sum (Fin 1) (Fin 3) → Complex

-- Source: PhysLean (LorentzGroup.mem_iff_self_mul_dual)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_mem_iff_self_mul_dual : ∀ {d : Nat} {Λ : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real},
--   Iff (Set.instMembership.mem (LorentzGroup d) Λ)
--     (Eq (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul Λ (minkowskiMatrix.dual Λ)) 1)

-- Source: PhysLean (LorentzGroup.generalizedBoost_apply_eq_toCoord)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_generalizedboost_apply_eq_tocoord : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem) (μ ν : Sum (Fin 1) (Fin d)),
--   Eq ((LorentzGroup.generalizedBoost u v).val μ ν)
--     (instHSub.hSub
--       (instHAdd.hAdd (1 μ ν)
--         (instHMul.hMul (instHMul.hMul (instHMul.hMul 2 (minkowskiMatrix ν ν)) (u.val ν)) (v.val μ)))
--       (instHDiv.hDiv
--         (instHMul.hMul (instHMul.hMul (minkowskiMatrix ν ν) (instHAdd.hAdd (u.val μ) (v.val μ)))
--           (instHAdd.hAdd (u.val ν) (v.val ν)))
--         (instHAdd.hAdd 1
--           (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct u.val)
--             v.val))))

-- Source: PhysLean (Lorentz.ContrMod.toFin1dℝEquiv)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_tofin1dℝequiv : {d : Nat} → LinearEquiv (RingHom.id Real) (Lorentz.ContrMod d) (Sum (Fin 1) (Fin d) → Real)

-- Source: PhysLean (Lorentz.ContrMod.stdBasis_inl_apply_inr)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_stdbasis_inl_apply_inr : ∀ {d : Nat} (i : Fin d), Eq ((Module.Basis.instFunLike.coe Lorentz.ContrMod.stdBasis (Sum.inl 0)).val (Sum.inr i)) 0

-- Source: PhysLean (LorentzGroup.toComplex_inv)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_tocomplex_inv : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Eq (Matrix.inv.inv (MonoidHom.instFunLike.coe LorentzGroup.toComplex Λ))
--     (MonoidHom.instFunLike.coe LorentzGroup.toComplex (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ))

-- Source: PhysLean (SpaceTime.fderiv_vector)
-- [complex signature, not re-axiomatized]
-- spacetime_fderiv_vector : ∀ {d : Nat} (f : SpaceTime d → Lorentz.Vector d),
--   Differentiable Real f →
--     ∀ (y dt : SpaceTime d) (ν : Sum (Fin 1) (Fin d)),
--       Eq (ContinuousLinearMap.funLike.coe (fderiv Real f y) dt ν)
--         (ContinuousLinearMap.funLike.coe (fderiv Real (fun x => f x ν) y) dt)

-- Source: PhysLean (LorentzGroup.toVelocity_continuous)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_tovelocity_continuous : ∀ {d : Nat}, Continuous LorentzGroup.toVelocity

-- Source: PhysLean (LorentzGroup.toVector_continuous)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_tovector_continuous : ∀ {d : Nat}, Continuous LorentzGroup.toVector

-- Source: PhysLean (complexLorentzTensor.actionT_coMetric)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_actiont_cometric : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (instHSMul.hSMul g complexLorentzTensor.coMetric) complexLorentzTensor.coMetric

-- Source: PhysLean (Lorentz.Velocity.pathFromZero)
-- [complex signature, not re-axiomatized]
-- lorentz_velocity_pathfromzero : {d : Nat} → (u : (Lorentz.Velocity d).Elem) → Path Lorentz.Velocity.zero u

-- Source: PhysLean (Lorentz.Vector.map_apply_eq_basis_mulVec)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_map_apply_eq_basis_mulvec : ∀ {d : Nat} (f : LinearMap (RingHom.id Real) (Lorentz.Vector d) (Lorentz.Vector d)) (p : Lorentz.Vector d),
--   Eq (LinearMap.instFunLike.coe f p)
--     ((EquivLike.toFunLike.coe (LinearMap.toMatrix Lorentz.Vector.basis Lorentz.Vector.basis) f).mulVec p)

-- Source: PhysLean (Lorentz.ContrMod.toFin1dℝEquiv_isInducing)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_tofin1dℝequiv_isinducing : ∀ {d : Nat}, Topology.IsInducing (EquivLike.toFunLike.coe Lorentz.ContrMod.toFin1dℝEquiv)

-- Source: PhysLean (complexLorentzTensor.coContrUnit)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cocontrunit : complexLorentzTensor.Tensor
--   (Matrix.vecCons complexLorentzTensor.Color.down (Matrix.vecCons complexLorentzTensor.Color.up Matrix.vecEmpty))

-- Source: PhysLean (Lorentz.contrContrContractField.stdBasis_inl)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_stdbasis_inl : ∀ {d : Nat},
--   Eq
--     (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--       (TensorProduct.tmul Real (Module.Basis.instFunLike.coe Lorentz.ContrMod.stdBasis (Sum.inl 0))
--         (Module.Basis.instFunLike.coe Lorentz.ContrMod.stdBasis (Sum.inl 0))))
--     1

-- Source: PhysLean (SpaceTime.schwartzAction_mul_apply)
-- [complex signature, not re-axiomatized]
-- spacetime_schwartzaction_mul_apply : ∀ {d : Nat} (Λ₁ Λ₂ : (LorentzGroup d).Elem) (η : SchwartzMap (SpaceTime d) Real),
--   Eq
--     (ContinuousLinearMap.funLike.coe (MonoidHom.instFunLike.coe SpaceTime.schwartzAction Λ₂)
--       (ContinuousLinearMap.funLike.coe (MonoidHom.instFunLike.coe SpaceTime.schwartzAction Λ₁) η))
--     (ContinuousLinearMap.funLike.coe (MonoidHom.instFunLike.coe SpaceTime.schwartzAction (instHMul.hMul Λ₂ Λ₁)) η)

-- Source: PhysLean (complexLorentzTensor.altLeftMetric_eq_fromConstPair)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altleftmetric_eq_fromconstpair : Eq complexLorentzTensor.altLeftMetric (TensorSpecies.Tensor.fromConstPair Fermion.altLeftMetric)

-- Source: PhysLean (SpaceTime.distDeriv_comp_lorentz_action)
-- [complex signature, not re-axiomatized]
-- spacetime_distderiv_comp_lorentz_action : ∀ {n d : Nat} {c : Fin n → realLorentzTensor.Color} {M : Type} [inst : NormedAddCommGroup M]
--   [inst_1 : NormedSpace Real M] [inst_2 : (realLorentzTensor d).Tensorial c M] [inst_3 : T2Space M]
--   {μ : Sum (Fin 1) (Fin d)} (Λ : (LorentzGroup d).Elem) (f : Distribution Real (SpaceTime d) M),
--   Eq (LinearMap.instFunLike.coe (SpaceTime.distDeriv μ) (instHSMul.hSMul Λ f))
--     (Finset.univ.sum fun ν =>
--       instHSMul.hSMul ((DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ).val ν μ)
--         (instHSMul.hSMul Λ (LinearMap.instFunLike.coe (SpaceTime.distDeriv ν) f)))

-- Source: PhysLean (minkowskiMatrix.inr_i_inr_i)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_inr_i_inr_i : ∀ {d : Nat} (i : Fin d), Eq (minkowskiMatrix (Sum.inr i) (Sum.inr i)) (-1)

-- Source: PhysLean (Lorentz.ContrℂModule.instAddCommGroup)
-- [complex signature, not re-axiomatized]
-- lorentz_contrℂmodule_instaddcommgroup : AddCommGroup Lorentz.ContrℂModule

-- Source: PhysLean (complexLorentzTensor.termεL')
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_termεl' : Lean.ParserDescr

-- Source: PhysLean (Lorentz.Vector.minkowskiProductMap_smul_fst)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_minkowskiproductmap_smul_fst : ∀ {d : Nat} (c : Real) (p q : Lorentz.Vector d),
--   Eq ((instHSMul.hSMul c p).minkowskiProductMap q) (instHMul.hMul c (p.minkowskiProductMap q))

-- Source: PhysLean (Lorentz.Vector.lightConeBoundary.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_lightconeboundary_eq_1 : ∀ {d : Nat} (p : Lorentz.Vector d),
--   Eq p.lightConeBoundary
--     (setOf fun q => Eq (instHSub.hSub q p).causalCharacter Lorentz.Vector.CausalCharacter.lightLike)

-- Source: PhysLean (SpaceTime.distTensorDeriv_equivariant)
-- [complex signature, not re-axiomatized]
-- spacetime_disttensorderiv_equivariant : ∀ {n d : Nat} {c : Fin n → realLorentzTensor.Color} {M : Type} [inst : NormedAddCommGroup M]
--   [inst_1 : InnerProductSpace Real M] [inst_2 : FiniteDimensional Real M] [inst_3 : (realLorentzTensor d).Tensorial c M]
--   (f : Distribution Real (SpaceTime d) M) (Λ : (LorentzGroup d).Elem),
--   Eq (LinearMap.instFunLike.coe SpaceTime.distTensorDeriv (instHSMul.hSMul Λ f))
--     (instHSMul.hSMul Λ (LinearMap.instFunLike.coe SpaceTime.distTensorDeriv f))

-- Source: PhysLean (LorentzGroup.generalizedBoost_mem_restricted)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_generalizedboost_mem_restricted : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem),
--   SetLike.instMembership.mem (LorentzGroup.restricted d) (LorentzGroup.generalizedBoost u v)

-- Source: PhysLean (SpaceTime.instBorelSpace)
-- [complex signature, not re-axiomatized]
-- spacetime_instborelspace : ∀ {d : Nat}, BorelSpace (SpaceTime d)

-- Source: PhysLean (Lorentz.contrCoUnitVal)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcounitval : (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo).V.carrier

-- Source: PhysLean (Lorentz.Vector.adjoint)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_adjoint : {d : Nat} →
--   LinearMap (RingHom.id Real) (Lorentz.Vector d) (Lorentz.Vector d) →
--     LinearMap (RingHom.id Real) (Lorentz.Vector d) (Lorentz.Vector d)

-- Source: PhysLean (Lorentz.Vector.inner_eq_equivEuclid)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_inner_eq_equiveuclid : ∀ (d : Nat) (v w : Lorentz.Vector d),
--   Eq ((Lorentz.Vector.instInnerReal d).inner Real v w)
--     ((PiLp.innerProductSpace fun x => Real).inner Real (EquivLike.toFunLike.coe (Lorentz.Vector.equivEuclid d) v)
--       (EquivLike.toFunLike.coe (Lorentz.Vector.equivEuclid d) w))

-- Source: PhysLean (LorentzGroup.isOrthochronous_on_connected_component)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_isorthochronous_on_connected_component : ∀ {d : Nat} {Λ Λ' : (LorentzGroup d).Elem},
--   Set.instMembership.mem (connectedComponent Λ) Λ' →
--     Iff (LorentzGroup.IsOrthochronous Λ) (LorentzGroup.IsOrthochronous Λ')

-- Source: PhysLean (Lorentz.Vector.asSmoothManifold)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_assmoothmanifold : (d : Nat) → ModelWithCorners Real (Lorentz.Vector d) (Lorentz.Vector d)

-- Source: PhysLean (SpaceTime.space_toTimeAndSpace_symm)
-- [complex signature, not re-axiomatized]
-- spacetime_space_totimeandspace_symm : ∀ {d : Nat} {c : SpeedOfLight} (t : Time) (s : Space d),
--   Eq
--     (ContinuousLinearMap.funLike.coe SpaceTime.space
--       (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c).symm { fst := t, snd := s }))
--     s

-- Source: PhysLean (Lorentz.Vector.temporalCLM_basis_sum_inl)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_temporalclm_basis_sum_inl : ∀ {d : Nat},
--   Eq
--     (ContinuousLinearMap.funLike.coe (Lorentz.Vector.temporalCLM d)
--       (Module.Basis.instFunLike.coe Lorentz.Vector.basis (Sum.inl 0)))
--     1

-- Source: PhysLean (SpaceTime.distTensorDeriv.congr_simp)
-- [complex signature, not re-axiomatized]
-- spacetime_disttensorderiv_congr_simp : ∀ {M : Type} {d : Nat} [inst : NormedAddCommGroup M] [inst_1 : InnerProductSpace Real M]
--   [inst_2 : FiniteDimensional Real M], Eq SpaceTime.distTensorDeriv SpaceTime.distTensorDeriv

-- Source: PhysLean (SpaceTime.instSMulElemMatrixSumFinOfNatNatRealLorentzGroupDistribution)
-- [complex signature, not re-axiomatized]
-- spacetime_instsmulelemmatrixsumfinofnatnatreallorentzgroupdistribution : {n d : Nat} →
--   {c : Fin n → realLorentzTensor.Color} →
--     {M : Type} →
--       [inst : NormedAddCommGroup M] →
--         [inst_1 : NormedSpace Real M] →
--           [(realLorentzTensor d).Tensorial c M] →
--             [T2Space M] → SMul (LorentzGroup d).Elem (Distribution Real (SpaceTime d) M)

-- Source: PhysLean (Lorentz.Vector.isNormedSpace)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_isnormedspace : (d : Nat) → NormedSpace Real (Lorentz.Vector d)

-- Source: PhysLean (complexLorentzTensor.coBispinorDown)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cobispinordown : complexLorentzTensor.Tensor (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty) →
--   complexLorentzTensor.Tensor
--     (Matrix.vecCons complexLorentzTensor.Color.downL (Matrix.vecCons complexLorentzTensor.Color.downR Matrix.vecEmpty))

-- Source: PhysLean (Lorentz.Vector.equivPi)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_equivpi : (d : Nat) → ContinuousLinearEquiv (RingHom.id Real) (Lorentz.Vector d) (Sum (Fin 1) (Fin d) → Real)

-- Source: PhysLean (LorentzGroup.γ_zero)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_γ_zero : Eq (LorentzGroup.γ 0) 1

-- Source: PhysLean (Lorentz.Vector.coordCLM.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_coordclm_eq_1 : ∀ {d : Nat} (i : Sum (Fin 1) (Fin d)),
--   Eq (Lorentz.Vector.coordCLM i)
--     (EquivLike.toFunLike.coe LinearMap.toContinuousLinearMap { toFun := fun v => v i, map_add' := ⋯, map_smul' := ⋯ })

-- Source: PhysLean (Lorentz.coBasis.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_cobasis_eq_1 : ∀ (d : Nat), Eq (Lorentz.coBasis d) (Module.Basis.ofEquivFun Lorentz.CoMod.toFin1dℝEquiv)

-- Source: PhysLean (SpaceTime.lorentzGroup_smul_dist_apply)
-- [complex signature, not re-axiomatized]
-- spacetime_lorentzgroup_smul_dist_apply : ∀ {n d : Nat} {c : Fin n → realLorentzTensor.Color} {M : Type} [inst : NormedAddCommGroup M]
--   [inst_1 : NormedSpace Real M] [inst_2 : (realLorentzTensor d).Tensorial c M] [inst_3 : T2Space M]
--   (Λ : (LorentzGroup d).Elem) (f : Distribution Real (SpaceTime d) M) (η : SchwartzMap (SpaceTime d) Real),
--   Eq (ContinuousLinearMap.funLike.coe (instHSMul.hSMul Λ f) η)
--     (instHSMul.hSMul Λ
--       (ContinuousLinearMap.funLike.coe f
--         (ContinuousLinearMap.funLike.coe
--           (MonoidHom.instFunLike.coe SpaceTime.schwartzAction (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ))
--           η)))

-- Source: PhysLean (SpaceTime.tensorDeriv)
-- [complex signature, not re-axiomatized]
-- spacetime_tensorderiv : {d : Nat} →
--   {M : Type} →
--     [inst : NormedAddCommGroup M] →
--       [inst_1 : NormedSpace Real M] → (SpaceTime d → M) → SpaceTime d → TensorProduct Real (Lorentz.CoVector d) M

-- Source: PhysLean (Lorentz.CoVector.instFiniteDimensionalReal)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_instfinitedimensionalreal : ∀ {d : Nat}, FiniteDimensional Real (Lorentz.CoVector d)

-- Source: PhysLean (minkowskiMatrix.dual_apply_minkowskiMatrix)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_dual_apply_minkowskimatrix : ∀ {d : Nat} (Λ : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real) (μ ν : Sum (Fin 1) (Fin d)),
--   Eq (instHMul.hMul (minkowskiMatrix.dual Λ μ ν) (minkowskiMatrix ν ν)) (instHMul.hMul (minkowskiMatrix μ μ) (Λ ν μ))

-- Source: PhysLean (complexLorentzTensor.basis_downR_eq)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_basis_downr_eq : ∀ {i : Fin 2},
--   Eq (Module.Basis.instFunLike.coe (complexLorentzTensor.basis complexLorentzTensor.Color.downR) i)
--     (Module.Basis.instFunLike.coe Fermion.altRightBasis i)

-- Source: PhysLean (Lorentz.ContrℂModule.toFin13ℂEquiv_symm_apply_val)
-- [complex signature, not re-axiomatized]
-- lorentz_contrℂmodule_tofin13ℂequiv_symm_apply_val : ∀ (a : Sum (Fin 1) (Fin 3) → Complex) (a_1 : Sum (Fin 1) (Fin 3)),
--   Eq ((EquivLike.toFunLike.coe Lorentz.ContrℂModule.toFin13ℂEquiv.symm a).val a_1) (a a_1)

-- Source: PhysLean (Lorentz.inclCongrRealLorentz_ρ)
-- [complex signature, not re-axiomatized]
-- lorentz_inclcongrreallorentz_ρ : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex) (v : Lorentz.ContrMod 3),
--   Eq
--     (LinearMap.instFunLike.coe (MonoidHom.instFunLike.coe Lorentz.complexContr.ρ M)
--       (LinearMap.instFunLike.coe Lorentz.inclCongrRealLorentz v))
--     (LinearMap.instFunLike.coe Lorentz.inclCongrRealLorentz
--       (LinearMap.instFunLike.coe
--         (MonoidHom.instFunLike.coe (Lorentz.Contr 3).ρ (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M)) v))

-- Source: PhysLean (Lorentz.coBasisFin_toFin1dℝ)
-- [complex signature, not re-axiomatized]
-- lorentz_cobasisfin_tofin1dℝ : ∀ {d : Nat} (i : Fin (instHAdd.hAdd 1 d)),
--   Eq (Lorentz.CoMod.toFin1dℝ (Module.Basis.instFunLike.coe (Lorentz.coBasisFin d) i))
--     (Pi.single (EquivLike.toFunLike.coe finSumFinEquiv.symm i) 1)

-- Source: PhysLean (Lorentz.ContrMod.mulVec_add)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_mulvec_add : ∀ {d : Nat} (M : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real) (v w : Lorentz.ContrMod d),
--   Eq (Lorentz.ContrMod.mulVec M (instHAdd.hAdd v w))
--     (instHAdd.hAdd (Lorentz.ContrMod.mulVec M v) (Lorentz.ContrMod.mulVec M w))

-- Source: PhysLean (Lorentz.coBasis_ρ_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_cobasis_ρ_apply : ∀ {d : Nat} (M : (LorentzGroup d).Elem) (i j : Sum (Fin 1) (Fin d)),
--   Eq
--     (EquivLike.toFunLike.coe (LinearMap.toMatrix (Lorentz.coBasis d) (Lorentz.coBasis d))
--       (MonoidHom.instFunLike.coe (Lorentz.Co d).ρ M) i j)
--     ((Matrix.inv.inv M.val).transpose i j)

-- Source: PhysLean (complexLorentzTensor.contrBispinorUp_eq_metric_contr_contrBispinorDown)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrbispinorup_eq_metric_contr_contrbispinordown : InformalLemma

-- Source: PhysLean (Lorentz.CoVector.apply_smul)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_apply_smul : ∀ {d : Nat} (c : Real) (v : Lorentz.CoVector d) (i : Sum (Fin 1) (Fin d)),
--   Eq (instHSMul.hSMul c v i) (instHMul.hMul c (v i))

-- Source: PhysLean (Lorentz.coContrUnit.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrunit_eq_1 : Eq Lorentz.coContrUnit
--   {
--     hom :=
--       ModuleCat.ofHom
--         {
--           toFun := fun a =>
--             have a' := a;
--             instHSMul.hSMul a' Lorentz.coContrUnitVal,
--           map_add' := Lorentz.coContrUnit._proof_1, map_smul' := Lorentz.coContrUnit._proof_2 },
--     comm := Lorentz.coContrUnit._proof_3 }

-- Source: PhysLean (SpaceTime.instMeasureSpace)
-- [complex signature, not re-axiomatized]
-- spacetime_instmeasurespace : {d : Nat} → MeasureTheory.MeasureSpace (SpaceTime d)

-- Source: PhysLean (Lorentz.preCoMetricVal_expand_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_precometricval_expand_tmul : ∀ {d : Nat},
--   Eq (Lorentz.preCoMetricVal d)
--     (instHSub.hSub
--       (TensorProduct.tmul Real (Module.Basis.instFunLike.coe (Lorentz.coBasis d) (Sum.inl 0))
--         (Module.Basis.instFunLike.coe (Lorentz.coBasis d) (Sum.inl 0)))
--       (Finset.univ.sum fun i =>
--         TensorProduct.tmul Real (Module.Basis.instFunLike.coe (Lorentz.coBasis d) (Sum.inr i))
--           (Module.Basis.instFunLike.coe (Lorentz.coBasis d) (Sum.inr i))))

-- Source: PhysLean (Lorentz.contr_continuous)
-- [complex signature, not re-axiomatized]
-- lorentz_contr_continuous : ∀ {d : Nat} {T : Type} [inst : TopologicalSpace T] (f : (Lorentz.Contr d).V.carrier → T),
--   Continuous (Function.comp f (EquivLike.toFunLike.coe Lorentz.ContrMod.toFin1dℝEquiv.symm)) → Continuous f

-- Source: PhysLean (Lorentz.ContrℂModule.ext)
-- [complex signature, not re-axiomatized]
-- lorentz_contrℂmodule_ext : ∀ (ψ ψ' : Lorentz.ContrℂModule), Eq ψ.val ψ'.val → Eq ψ ψ'

-- Source: PhysLean (complexLorentzTensor.actionT_altRightMetric)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_actiont_altrightmetric : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (instHSMul.hSMul g complexLorentzTensor.altRightMetric) complexLorentzTensor.altRightMetric

-- Source: PhysLean (Lorentz.contrCoToMatrix.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcotomatrix_eq_1 : Eq Lorentz.contrCoToMatrix
--   (((Lorentz.complexContrBasis.tensorProduct Lorentz.complexCoBasis).repr.trans
--         (Finsupp.linearEquivFunOnFinite Complex Complex (Prod (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3))))).trans
--     (LinearEquiv.curry Complex Complex (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3))))

-- Source: PhysLean (LorentzGroup.genBoostAux₂_basis_minkowskiProduct)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_genboostaux₂_basis_minkowskiproduct : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem) (μ ν : Sum (Fin 1) (Fin d)),
--   Eq
--     (ContinuousLinearMap.funLike.coe
--       (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct
--         (LinearMap.instFunLike.coe (LorentzGroup.genBoostAux₂ u v)
--           (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ)))
--       (LinearMap.instFunLike.coe (LorentzGroup.genBoostAux₂ u v) (Module.Basis.instFunLike.coe Lorentz.Vector.basis ν)))
--     (instHMul.hMul
--       (instHMul.hMul
--         (instHMul.hMul (instHMul.hMul (instHMul.hMul 2 (minkowskiMatrix μ μ)) (minkowskiMatrix ν ν))
--           (instHAdd.hAdd (u.val μ) (v.val μ)))
--         (instHAdd.hAdd (u.val ν) (v.val ν)))
--       (Real.instInv.inv
--         (instHAdd.hAdd 1
--           (ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct u.val)
--             v.val))))

-- Source: PhysLean (realLorentzTensor.coMetric_eq_fromPairT)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_cometric_eq_frompairt : ∀ {d : Nat},
--   Eq (realLorentzTensor.coMetric d)
--     (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT (Lorentz.preCoMetricVal d))

-- Source: PhysLean (Lorentz.Vector.instFiniteDimensionalReal)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_instfinitedimensionalreal : ∀ {d : Nat}, FiniteDimensional Real (Lorentz.Vector d)

-- Source: PhysLean (Lorentz.«_aux_PhysLean_Relativity_Tensors_RealTensor_Vector_Pre_Modules___macroRules_Lorentz_term_*ᵥ__1_1»)
-- [complex signature, not re-axiomatized]
-- lorentz_«_aux_physlean_relativity_tensors_realtensor_vector_pre_modules___macrorules_lorentz_term_*ᵥ__1_1» : Lean.Macro

-- Source: PhysLean (LorentzGroup.boost_inl_0_inl_0)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_inl_0_inl_0 : ∀ {d : Nat} (i : Fin d) {β : Real} (hβ : Real.instLT.lt (abs β) 1),
--   Eq ((LorentzGroup.boost i β hβ).val (Sum.inl 0) (Sum.inl 0)) (LorentzGroup.γ β)

-- Source: PhysLean (Lorentz.SL2C.toSelfAdjointEquiv)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_toselfadjointequiv : (M : Matrix (Fin 2) (Fin 2) Complex) →
--   [Invertible M] →
--     LinearEquiv (RingHom.id Real) (Subtype fun x => SetLike.instMembership.mem Lorentz.ℍ₂ x)
--       (Subtype fun x => SetLike.instMembership.mem Lorentz.ℍ₂ x)

-- Source: PhysLean (Lorentz.contrCoUnit.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcounit_eq_1 : Eq Lorentz.contrCoUnit
--   {
--     hom :=
--       ModuleCat.ofHom
--         {
--           toFun := fun a =>
--             have a' := a;
--             instHSMul.hSMul a' Lorentz.contrCoUnitVal,
--           map_add' := Lorentz.contrCoUnit._proof_1, map_smul' := Lorentz.contrCoUnit._proof_2 },
--     comm := Lorentz.contrCoUnit._proof_3 }

-- Source: PhysLean (Lorentz.ContrMod.toFin1dℝ.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_tofin1dℝ_eq_1 : ∀ {d : Nat} (ψ : Lorentz.ContrMod d), Eq ψ.toFin1dℝ (EquivLike.toFunLike.coe Lorentz.ContrMod.toFin1dℝEquiv ψ)

-- Source: PhysLean (SpaceTime.contDiff_vector)
-- [complex signature, not re-axiomatized]
-- spacetime_contdiff_vector : ∀ {n : WithTop ENat} {d : Nat} (f : SpaceTime d → Lorentz.Vector d),
--   Iff (∀ (ν : Sum (Fin 1) (Fin d)), ContDiff Real n fun x => f x ν) (ContDiff Real n f)

-- Source: PhysLean (complexLorentzTensor.basis_contr)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_basis_contr : ∀ (c : complexLorentzTensor.Color) (i : Fin (complexLorentzTensor.repDim c))
--   (j : Fin (complexLorentzTensor.repDim (complexLorentzTensor.τ c))),
--   Eq
--     (TensorSpecies.castToField
--       (((fun X Y => LinearMap.instFunLike)
--             ((IndexNotation.OverColor.Discrete.pairτ complexLorentzTensor.FD complexLorentzTensor.τ).obj { as := c }).V
--             ((CategoryTheory.Monoidal.functorCategoryMonoidalStruct.tensorUnit
--                     (CategoryTheory.Functor (CategoryTheory.Discrete complexLorentzTensor.Color)
--                       (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))).obj
--                 { as := c }).V).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--           (complexLorentzTensor.contr.app { as := c }).hom)
--         (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe (complexLorentzTensor.basis c) i)
--           (Module.Basis.instFunLike.coe (complexLorentzTensor.basis (complexLorentzTensor.τ c)) j))))
--     (ite (Eq i.val j.val) 1 0)

-- Source: PhysLean (realLorentzTensor.colorToComplex)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_colortocomplex : realLorentzTensor.Color → complexLorentzTensor.Color

-- Source: PhysLean (Lorentz.complexContrBasisFin4_apply_one)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcontrbasisfin4_apply_one : Eq (Module.Basis.instFunLike.coe Lorentz.complexContrBasisFin4 1)
--   (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 0))

-- Source: PhysLean (Lorentz.ContrMod.mulVec_sub)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_mulvec_sub : ∀ {d : Nat} (M : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real) (v w : Lorentz.ContrMod d),
--   Eq (Lorentz.ContrMod.mulVec M (instHSub.hSub v w))
--     (instHSub.hSub (Lorentz.ContrMod.mulVec M v) (Lorentz.ContrMod.mulVec M w))

-- Source: PhysLean (Lorentz.SL2C.toSelfAdjointMap_pauliBasis)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_toselfadjointmap_paulibasis : ∀ {M : Matrix.SpecialLinearGroup (Fin 2) Complex} (i : Sum (Fin 1) (Fin 3)),
--   Eq
--     (LinearMap.instFunLike.coe (Lorentz.SL2C.toSelfAdjointMap M)
--       (Module.Basis.instFunLike.coe PauliMatrix.pauliBasis i))
--     (Finset.univ.sum fun j =>
--       instHSMul.hSMul
--         ((MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup (Matrix.SpecialLinearGroup.hasInv.inv M)).val i j)
--         (Module.Basis.instFunLike.coe PauliMatrix.pauliBasis j))

-- Source: PhysLean (SpaceTime.distTimeSlice_distDeriv_inl)
-- [complex signature, not re-axiomatized]
-- spacetime_disttimeslice_distderiv_inl : ∀ {M : Type} {d : Nat} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] {c : SpeedOfLight}
--   (f : Distribution Real (SpaceTime d) M),
--   Eq
--     (EquivLike.toFunLike.coe (SpaceTime.distTimeSlice c)
--       (LinearMap.instFunLike.coe (SpaceTime.distDeriv (Sum.inl 0)) f))
--     (instHSMul.hSMul (instHDiv.hDiv 1 c.val)
--       (LinearMap.instFunLike.coe Space.distTimeDeriv (EquivLike.toFunLike.coe (SpaceTime.distTimeSlice c) f)))

-- Source: PhysLean (Lorentz.CoMod.mulVec)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_mulvec : {d : Nat} → Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real → Lorentz.CoMod d → Lorentz.CoMod d

-- Source: PhysLean (Lorentz.contrContrContractField.right_parity)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_right_parity : ∀ {d : Nat} (x y : (Lorentz.Contr d).V.carrier),
--   Eq
--     (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--       (TensorProduct.tmul Real x
--         (LinearMap.instFunLike.coe (MonoidHom.instFunLike.coe (Lorentz.Contr d).ρ LorentzGroup.parity) y)))
--     (Finset.univ.sum fun i => instHMul.hMul (x.val i) (y.val i))

-- Source: PhysLean (Lorentz.CoVector.inner_eq_equivEuclid)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_inner_eq_equiveuclid : ∀ (d : Nat) (v w : Lorentz.CoVector d),
--   Eq ((Lorentz.CoVector.instInnerReal d).inner Real v w)
--     ((PiLp.innerProductSpace fun x => Real).inner Real (EquivLike.toFunLike.coe (Lorentz.CoVector.equivEuclid d) v)
--       (EquivLike.toFunLike.coe (Lorentz.CoVector.equivEuclid d) w))

-- Source: PhysLean (Lorentz.Vector.CausalCharacter.ctorElim)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causalcharacter_ctorelim : {motive : Lorentz.Vector.CausalCharacter → Sort u} →
--   (ctorIdx : Nat) →
--     (t : Lorentz.Vector.CausalCharacter) →
--       Eq ctorIdx t.ctorIdx → Lorentz.Vector.CausalCharacter.ctorElimType ctorIdx → motive t

-- Source: PhysLean (LorentzGroup.boost_inr_inr_other)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_inr_inr_other : ∀ {d : Nat} {i j k : Fin d} {β : Real} (hβ : Real.instLT.lt (abs β) 1),
--   Ne j i → Eq ((LorentzGroup.boost i β hβ).val (Sum.inr k) (Sum.inr j)) (ite (Eq j k) 1 0)

-- Source: PhysLean (complexLorentzTensor.rightMetric_eq_fromPairT)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_rightmetric_eq_frompairt : Eq complexLorentzTensor.rightMetric (LinearMap.instFunLike.coe TensorSpecies.Tensor.fromPairT Fermion.rightMetricVal)

-- Source: PhysLean (minkowskiMatrix.dual.eq_1)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_dual_eq_1 : ∀ {d : Nat} (Λ : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real),
--   Eq (minkowskiMatrix.dual Λ) (instHMul.hMul (instHMul.hMul minkowskiMatrix Λ.transpose) minkowskiMatrix)

-- Source: PhysLean (Lorentz.contrCoContraction_basis)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcocontraction_basis : ∀ (i j : Fin 4),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.contrCoContraction.hom)
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasisFin4 i)
--         (Module.Basis.instFunLike.coe Lorentz.complexCoBasisFin4 j)))
--     (ite (Eq i.val j.val) 1 0)

-- Source: PhysLean (Lorentz.CoVector.smul_basis)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_smul_basis : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem) (μ : Sum (Fin 1) (Fin d)),
--   Eq (instHSMul.hSMul Λ (Module.Basis.instFunLike.coe Lorentz.CoVector.basis μ))
--     (Finset.univ.sum fun ν =>
--       instHSMul.hSMul ((DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv Λ).val μ ν)
--         (Module.Basis.instFunLike.coe Lorentz.CoVector.basis ν))

-- Source: PhysLean (SpaceTime.distTimeSlice.eq_1)
-- [complex signature, not re-axiomatized]
-- spacetime_disttimeslice_eq_1 : ∀ {M : Type} {d : Nat} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] (c : SpeedOfLight),
--   Eq (SpaceTime.distTimeSlice c)
--     {
--       toFun := fun f =>
--         ContinuousLinearMap.comp f (SchwartzMap.compCLMOfContinuousLinearEquiv Real (SpaceTime.toTimeAndSpace c)),
--       map_add' := ⋯, map_smul' := ⋯,
--       invFun := fun f =>
--         ContinuousLinearMap.comp f (SchwartzMap.compCLMOfContinuousLinearEquiv Real (SpaceTime.toTimeAndSpace c).symm),
--       left_inv := ⋯, right_inv := ⋯, continuous_toFun := ⋯, continuous_invFun := ⋯ }

-- Source: PhysLean (Lorentz.ContrℂModule.toFin13ℂFun)
-- [complex signature, not re-axiomatized]
-- lorentz_contrℂmodule_tofin13ℂfun : Equiv Lorentz.ContrℂModule (Sum (Fin 1) (Fin 3) → Complex)

-- Source: PhysLean (Lorentz.complexCo)
/-- The representation of `SL(2, ℂ)` on complex vectors corresponding to contravariant
Lorentz vectors. In index notation these have a down index `ψⁱ`.  -/
axiom lorentz_complexco :
  Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)

-- Source: PhysLean (CliffordAlgebra.forall_mul_self_eq_iff)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_forall_mul_self_eq_iff : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   {Q : QuadraticForm R M} {A : Type u_4} [inst_3 : Ring A] [inst_4 : Algebra R A],
--   IsUnit 2 →
--     ∀ (f : LinearMap (RingHom.id R) M A),
--       Iff
--         (∀ (x : M),
--           Eq (instHMul.hMul (LinearMap.instFunLike.coe f x) (LinearMap.instFunLike.coe f x))
--             (RingHom.instFunLike.coe (algebraMap R A) (QuadraticMap.instFunLike.coe Q x)))
--         (Eq (instHAdd.hAdd (((LinearMap.mul R A).compl₂ f).comp f) (((LinearMap.mul R A).flip.compl₂ f).comp f))
--           (LinearMap.compr₂ (QuadraticMap.polarBilin Q) (Algebra.linearMap R A)))

-- Source: PhysLean (Lorentz.Vector.basis_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_basis_apply : ∀ {d : Nat} (μ ν : Sum (Fin 1) (Fin d)), Eq (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ ν) (ite (Eq μ ν) 1 0)

-- Source: PhysLean (Lorentz.ContrMod.toFin1dℝ_eq_val)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_tofin1dℝ_eq_val : ∀ {d : Nat} (ψ : Lorentz.ContrMod d), Eq ψ.toFin1dℝ ψ.val

-- Source: PhysLean (LorentzGroup.restricted_normal_subgroup)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_restricted_normal_subgroup : ∀ {d : Nat}, (LorentzGroup.restricted d).Normal

-- Source: PhysLean (Lorentz.Vector.boost_inr_self_eq)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_boost_inr_self_eq : ∀ {d : Nat} (i : Fin d) (β : Real) (hβ : Real.instLT.lt (abs β) 1) (p : Lorentz.Vector d),
--   Eq (instHSMul.hSMul (LorentzGroup.boost i β hβ) p (Sum.inr i))
--     (instHMul.hMul (LorentzGroup.γ β) (instHSub.hSub (p (Sum.inr i)) (instHMul.hMul β (p (Sum.inl 0)))))

-- Source: PhysLean (Lorentz.CoMod.toFin1dℝFun)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_tofin1dℝfun : {d : Nat} → Equiv (Lorentz.CoMod d) (Sum (Fin 1) (Fin d) → Real)

-- Source: PhysLean (Lorentz.Vector.abs_component_le_norm)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_abs_component_le_norm : ∀ {d : Nat} (v : Lorentz.Vector d) (i : Sum (Fin 1) (Fin d)),
--   Real.instLE.le (abs (v i)) ((Lorentz.Vector.instNorm d).norm v)

-- Source: PhysLean (Lorentz.ContrMod.val_add)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_val_add : ∀ {d : Nat} (ψ ψ' : Lorentz.ContrMod d), Eq (instHAdd.hAdd ψ ψ').val (instHAdd.hAdd ψ.val ψ'.val)

-- Source: PhysLean (complexLorentzTensor.rightMetric_antisymm)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_rightmetric_antisymm : Eq
--   (EquivLike.toFunLike.coe
--     (TensorSpecies.Tensorial.self complexLorentzTensor
--         (Matrix.vecCons complexLorentzTensor.Color.upR
--           (Matrix.vecCons complexLorentzTensor.Color.upR Matrix.vecEmpty))).toTensor
--     complexLorentzTensor.rightMetric)
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT (Matrix.vecCons 1 (Matrix.vecCons 0 Matrix.vecEmpty)) ⋯)
--     (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg
--       (EquivLike.toFunLike.coe
--         (TensorSpecies.Tensorial.self complexLorentzTensor
--             (Matrix.vecCons complexLorentzTensor.Color.upR
--               (Matrix.vecCons complexLorentzTensor.Color.upR Matrix.vecEmpty))).toTensor
--         complexLorentzTensor.rightMetric)))

-- Source: PhysLean (Lorentz.contrContrContractField.nondegenerate)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_nondegenerate : ∀ {d : Nat} (y : (Lorentz.Contr d).V.carrier),
--   Iff
--     (∀ (x : (Lorentz.Contr d).V.carrier),
--       Eq (LinearMap.instFunLike.coe Lorentz.contrContrContractField (TensorProduct.tmul Real x y)) 0)
--     (Eq y 0)

-- Source: PhysLean (Lorentz.contrContrContractField.matrix_eq_iff_eq_forall)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_matrix_eq_iff_eq_forall : ∀ {d : Nat} {Λ Λ' : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real},
--   Iff (Eq Λ Λ')
--     (∀ (w v : (Lorentz.Contr d).V.carrier),
--       Eq
--         (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--           (TensorProduct.tmul Real v (Lorentz.ContrMod.mulVec Λ w)))
--         (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--           (TensorProduct.tmul Real v (Lorentz.ContrMod.mulVec Λ' w))))

-- Source: PhysLean (SpaceTime.distDeriv_inr_distTimeSlice_symm)
-- [complex signature, not re-axiomatized]
-- spacetime_distderiv_inr_disttimeslice_symm : ∀ {M : Type} {d : Nat} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] {c : SpeedOfLight} (i : Fin d)
--   (f : Distribution Real (Prod Time (Space d)) M),
--   Eq
--     (LinearMap.instFunLike.coe (SpaceTime.distDeriv (Sum.inr i))
--       (EquivLike.toFunLike.coe (SpaceTime.distTimeSlice c).symm f))
--     (EquivLike.toFunLike.coe (SpaceTime.distTimeSlice c).symm (LinearMap.instFunLike.coe (Space.distSpaceDeriv i) f))

-- Source: PhysLean (Lorentz.coContrToMatrix.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrtomatrix_eq_1 : Eq Lorentz.coContrToMatrix
--   (((Lorentz.complexCoBasis.tensorProduct Lorentz.complexContrBasis).repr.trans
--         (Finsupp.linearEquivFunOnFinite Complex Complex (Prod (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3))))).trans
--     (LinearEquiv.curry Complex Complex (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3))))

-- Source: PhysLean (SpaceTime.toTimeAndSpace.eq_1)
-- [complex signature, not re-axiomatized]
-- spacetime_totimeandspace_eq_1 : ∀ {d : Nat} (c : SpeedOfLight),
--   Eq (SpaceTime.toTimeAndSpace c)
--     {
--         toFun := fun x =>
--           { fst := LinearMap.instFunLike.coe (SpaceTime.time c) x,
--             snd := ContinuousLinearMap.funLike.coe SpaceTime.space x },
--         map_add' := ⋯, map_smul' := ⋯,
--         invFun := fun tx i =>
--           SpaceTime.toTimeAndSpace.match_1 (fun i => Real) i (fun val => instHMul.hMul c.val tx.fst.val) fun i =>
--             tx.snd.val i,
--         left_inv := ⋯, right_inv := ⋯ }.toContinuousLinearEquiv

-- Source: PhysLean (Lorentz.CoMod.stdBasis_repr_apply_toFun)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_stdbasis_repr_apply_tofun : ∀ {d : Nat} (a : Lorentz.CoMod d) (a_1 : Sum (Fin 1) (Fin d)),
--   Eq (Finsupp.instFunLike.coe (EquivLike.toFunLike.coe Lorentz.CoMod.stdBasis.repr a) a_1)
--     (EquivLike.toFunLike.coe Lorentz.CoMod.toFin1dℝEquiv a a_1)

-- Source: PhysLean (Lorentz.Vector.interiorPastLightCone)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_interiorpastlightcone : {d : Nat} → Lorentz.Vector d → Set (Lorentz.Vector d)

-- Source: PhysLean (Lorentz.ContrMod.stdBasis_decomp)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_stdbasis_decomp : ∀ {d : Nat} (v : Lorentz.ContrMod d),
--   Eq v
--     (Finset.univ.sum fun i => instHSMul.hSMul (v.toFin1dℝ i) (Module.Basis.instFunLike.coe Lorentz.ContrMod.stdBasis i))

-- Source: PhysLean (LorentzGroup.boost_inverse)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_inverse : ∀ {d : Nat} (i : Fin d) {β : Real} (hβ : Real.instLT.lt (abs β) 1),
--   Eq (DivisionMonoid.toDivInvOneMonoid.toInvOneClass.inv (LorentzGroup.boost i β hβ))
--     (LorentzGroup.boost i (Real.instNeg.neg β) ⋯)

-- Source: PhysLean (Lorentz.Velocity.minkowskiProduct_continuous_fst)
-- [complex signature, not re-axiomatized]
-- lorentz_velocity_minkowskiproduct_continuous_fst : ∀ {d : Nat} (u : Lorentz.Vector d),
--   Continuous fun x =>
--     ContinuousLinearMap.funLike.coe (ContinuousLinearMap.funLike.coe Lorentz.Vector.minkowskiProduct x.val) u

-- Source: PhysLean (Lorentz.ContrMod.toSelfAdjoint.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_toselfadjoint_eq_1 : Eq Lorentz.ContrMod.toSelfAdjoint
--   ((Lorentz.ContrMod.toFin1dℝEquiv.trans (Finsupp.linearEquivFunOnFinite Real Real (Sum (Fin 1) (Fin 3))).symm).trans
--     PauliMatrix.pauliBasis'.repr.symm)

-- Source: PhysLean (Lorentz.preContrMetricVal.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_precontrmetricval_eq_1 : ∀ (d : Nat),
--   Eq (Lorentz.preContrMetricVal d) (EquivLike.toFunLike.coe Lorentz.contrContrToMatrixRe.symm minkowskiMatrix)

-- Source: PhysLean (SpaceTime.timeSlice_differentiable)
-- [complex signature, not re-axiomatized]
-- spacetime_timeslice_differentiable : ∀ {d : Nat} {M : Type} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] (c : SpeedOfLight)
--   (f : SpaceTime d → M),
--   Differentiable Real f →
--     Differentiable Real (Function.hasUncurryInduction.uncurry (EquivLike.toFunLike.coe (SpaceTime.timeSlice c) f))

-- Source: PhysLean (realLorentzTensor.contr_basis)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_contr_basis : ∀ {d : Nat} {c : realLorentzTensor.Color} (i : Fin ((realLorentzTensor d).repDim c))
--   (j : Fin ((realLorentzTensor d).repDim ((realLorentzTensor d).τ c))),
--   Eq
--     (TensorSpecies.castToField
--       (((fun X Y => LinearMap.instFunLike)
--             ((IndexNotation.OverColor.Discrete.pairτ (realLorentzTensor d).FD (realLorentzTensor d).τ).obj
--                 { as := c }).V
--             ((CategoryTheory.Monoidal.functorCategoryMonoidalStruct.tensorUnit
--                     (CategoryTheory.Functor (CategoryTheory.Discrete realLorentzTensor.Color)
--                       (Rep Real (LorentzGroup d).Elem))).obj
--                 { as := c }).V).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom ((realLorentzTensor d).contr.app { as := c }).hom)
--         (TensorProduct.tmul Real (Module.Basis.instFunLike.coe ((realLorentzTensor d).basis c) i)
--           (Module.Basis.instFunLike.coe ((realLorentzTensor d).basis ((realLorentzTensor d).τ c)) j))))
--     (ite (Eq i.val j.val) 1 0)

-- Source: PhysLean (complexLorentzTensor.rightAltRightUnit_symm)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_rightaltrightunit_symm : Eq
--   (EquivLike.toFunLike.coe
--     (TensorSpecies.Tensorial.self complexLorentzTensor
--         (Matrix.vecCons complexLorentzTensor.Color.upR
--           (Matrix.vecCons complexLorentzTensor.Color.downR Matrix.vecEmpty))).toTensor
--     complexLorentzTensor.rightAltRightUnit)
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT (Matrix.vecCons 1 (Matrix.vecCons 0 Matrix.vecEmpty)) ⋯)
--     (EquivLike.toFunLike.coe
--       (TensorSpecies.Tensorial.self complexLorentzTensor
--           (Matrix.vecCons complexLorentzTensor.Color.downR
--             (Matrix.vecCons complexLorentzTensor.Color.upR Matrix.vecEmpty))).toTensor
--       complexLorentzTensor.altRightRightUnit))

-- Source: PhysLean (SpaceTime.coordCLM.eq_1)
-- [complex signature, not re-axiomatized]
-- spacetime_coordclm_eq_1 : ∀ {d : Nat} (μ : Sum (Fin 1) (Fin d)),
--   Eq (SpaceTime.coordCLM μ) { toFun := fun x => x μ, map_add' := ⋯, map_smul' := ⋯, cont := ⋯ }

-- Source: PhysLean (SpaceTime.distTimeSlice_symm_distTimeDeriv_eq)
-- [complex signature, not re-axiomatized]
-- spacetime_disttimeslice_symm_disttimederiv_eq : ∀ {M : Type} {d : Nat} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] {c : SpeedOfLight}
--   (f : Distribution Real (Prod Time (Space d)) M),
--   Eq (EquivLike.toFunLike.coe (SpaceTime.distTimeSlice c).symm (LinearMap.instFunLike.coe Space.distTimeDeriv f))
--     (instHSMul.hSMul c.val
--       (LinearMap.instFunLike.coe (SpaceTime.distDeriv (Sum.inl 0))
--         (EquivLike.toFunLike.coe (SpaceTime.distTimeSlice c).symm f)))

-- Source: PhysLean (Lorentz.ContrMod.stdBasis_apply_same)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_stdbasis_apply_same : ∀ {d : Nat} (μ : Sum (Fin 1) (Fin d)), Eq ((Module.Basis.instFunLike.coe Lorentz.ContrMod.stdBasis μ).val μ) 1

-- Source: PhysLean (Lorentz.contrCoContraction_apply_metric)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcocontraction_apply_metric : Eq
--   (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo).V
--         (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--       ((Action.instBraidedCategory (ModuleCat Complex) (Matrix.SpecialLinearGroup (Fin 2) Complex)).braiding
--             Lorentz.complexContr Lorentz.complexCo).hom.hom)
--     (((fun X Y => LinearMap.instFunLike)
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexContr.V
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorUnit (ModuleCat Complex))
--               Lorentz.complexCo.V))
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexContr.V
--             Lorentz.complexCo.V)).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--         (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft Lorentz.complexContr.V
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.leftUnitor Lorentz.complexCo.V).hom))
--       (((fun X Y => LinearMap.instFunLike)
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexContr.V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                 (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo).V Lorentz.complexCo.V))
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexContr.V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                 (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                 Lorentz.complexCo.V))).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft Lorentz.complexContr.V
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerRight Lorentz.contrCoContraction.hom
--               Lorentz.complexCo.V)))
--         (((fun X Y => LinearMap.instFunLike)
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexContr.V
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexContr.V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexCo.V
--                     Lorentz.complexCo.V)))
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexContr.V
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexContr.V
--                     Lorentz.complexCo.V)
--                   Lorentz.complexCo.V))).coe
--           ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft Lorentz.complexContr.V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.associator Lorentz.complexContr.V
--                   Lorentz.complexCo.V Lorentz.complexCo.V).inv))
--           (((fun X Y => LinearMap.instFunLike)
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexContr.V
--                     Lorentz.complexContr.V)
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexCo.V
--                     Lorentz.complexCo.V))
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexContr.V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexContr.V
--                     (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexCo.V
--                       Lorentz.complexCo.V)))).coe
--             ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.associator Lorentz.complexContr.V
--                   Lorentz.complexContr.V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Lorentz.complexCo.V
--                     Lorentz.complexCo.V)).hom)
--             (TensorProduct.tmul Complex
--               (((fun X Y => LinearMap.instFunLike)
--                     (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                     (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexContr).V).coe
--                 ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.contrMetric.hom) 1)
--               (((fun X Y => LinearMap.instFunLike)
--                     (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                     (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexCo).V).coe
--                 ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.coMetric.hom) 1)))))))
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Lorentz.complexCo Lorentz.complexContr).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.coContrUnit.hom) 1)

-- Source: PhysLean (complexLorentzTensor.basis_upR_eq)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_basis_upr_eq : ∀ {i : Fin 2},
--   Eq (Module.Basis.instFunLike.coe (complexLorentzTensor.basis complexLorentzTensor.Color.upR) i)
--     (Module.Basis.instFunLike.coe Fermion.rightBasis i)

-- Source: PhysLean (CliffordAlgebra.map_comp_map)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_map_comp_map : ∀ {R : Type u_1} [inst : CommRing R] {M₁ : Type u_4} {M₂ : Type u_5} {M₃ : Type u_6} [inst_1 : AddCommGroup M₁]
--   [inst_2 : AddCommGroup M₂] [inst_3 : AddCommGroup M₃] [inst_4 : Module R M₁] [inst_5 : Module R M₂]
--   [inst_6 : Module R M₃] {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q₃ : QuadraticForm R M₃}
--   (f : QuadraticMap.Isometry Q₂ Q₃) (g : QuadraticMap.Isometry Q₁ Q₂),
--   Eq ((CliffordAlgebra.map f).comp (CliffordAlgebra.map g)) (CliffordAlgebra.map (f.comp g))

-- Source: PhysLean (LorentzGroup.ofSpecialOrthogonal.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_ofspecialorthogonal_eq_1 : ∀ {d : Nat},
--   Eq LorentzGroup.ofSpecialOrthogonal
--     { toFun := fun A => ⟨⟨Matrix.fromBlocks 1 0 0 A.val, ⋯⟩, ⋯⟩,
--       invFun := fun Λ => ⟨fun i j => Λ.val.val (Sum.inr i) (Sum.inr j), ⋯⟩, left_inv := ⋯, right_inv := ⋯,
--       map_mul' := ⋯ }

-- Source: PhysLean (SpaceTime.toTimeAndSpace_symm_measurePreserving)
-- [complex signature, not re-axiomatized]
-- spacetime_totimeandspace_symm_measurepreserving : ∀ {d : Nat} (c : SpeedOfLight),
--   MeasureTheory.MeasurePreserving (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c).symm)
--     (measureSpaceOfInnerProductSpace.volume.prod measureSpaceOfInnerProductSpace.volume)
--     (instHSMul.hSMul (ENNReal.ofReal (Real.instInv.inv c.val)) SpaceTime.instMeasureSpace.volume)

-- Source: PhysLean (Lorentz.complexContrBasisFin4_apply_zero)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcontrbasisfin4_apply_zero : Eq (Module.Basis.instFunLike.coe Lorentz.complexContrBasisFin4 0)
--   (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inl 0))

-- Source: PhysLean (Lorentz.contrCoUnit_apply_one)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcounit_apply_one : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Lorentz.contrCoUnit.hom) 1)
--   Lorentz.contrCoUnitVal

-- Source: PhysLean (Lorentz.Velocity.ext)
-- [complex signature, not re-axiomatized]
-- lorentz_velocity_ext : ∀ {d : Nat} {v w : (Lorentz.Velocity d).Elem}, Eq v.val w.val → Eq v w

-- Source: PhysLean (LorentzGroup.instIsTopologicalGroupElemMatrixSumFinOfNatNatReal)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_instistopologicalgroupelemmatrixsumfinofnatnatreal : ∀ {d : Nat}, IsTopologicalGroup (LorentzGroup d).Elem

-- Source: PhysLean (SpaceTime.distTimeSlice_apply)
-- [complex signature, not re-axiomatized]
-- spacetime_disttimeslice_apply : ∀ {M : Type} {d : Nat} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] (c : SpeedOfLight)
--   (f : Distribution Real (SpaceTime d) M) (κ : SchwartzMap (Prod Time (Space d)) Real),
--   Eq (ContinuousLinearMap.funLike.coe (EquivLike.toFunLike.coe (SpaceTime.distTimeSlice c) f) κ)
--     (ContinuousLinearMap.funLike.coe f
--       (ContinuousLinearMap.funLike.coe (SchwartzMap.compCLMOfContinuousLinearEquiv Real (SpaceTime.toTimeAndSpace c))
--         κ))

-- Source: PhysLean (Lorentz.Vector.toTensor_basis_eq_tensor_basis)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_totensor_basis_eq_tensor_basis : ∀ {d : Nat} (μ : Sum (Fin 1) (Fin d)),
--   Eq (EquivLike.toFunLike.coe Lorentz.Vector.tensorial.toTensor (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ))
--     (Module.Basis.instFunLike.coe
--       (TensorSpecies.Tensor.basis (Matrix.vecCons realLorentzTensor.Color.up Matrix.vecEmpty))
--       (EquivLike.toFunLike.coe Lorentz.Vector.indexEquiv.symm μ))

-- Source: PhysLean (complexLorentzTensor.altLeftLeftUnit_eq_ofRat)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altleftleftunit_eq_ofrat : Eq complexLorentzTensor.altLeftLeftUnit
--   (LinearMap.instFunLike.coe complexLorentzTensor.ofRat fun f => ite (Eq (f 0) (f 1)) 1 0)

-- Source: PhysLean (complexLorentzTensor.actionT_leftAltLeftUnit)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_actiont_leftaltleftunit : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (instHSMul.hSMul g complexLorentzTensor.leftAltLeftUnit) complexLorentzTensor.leftAltLeftUnit

-- Source: PhysLean (Lorentz.preCoMetric_apply_one)
-- [complex signature, not re-axiomatized]
-- lorentz_precometric_apply_one : ∀ {d : Nat},
--   Eq
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V
--           (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Co d)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom (Lorentz.preCoMetric d).hom) 1)
--     (Lorentz.preCoMetricVal d)

-- Source: PhysLean (Lorentz.contrCoToMatrixRe)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcotomatrixre : {d : Nat} →
--   LinearEquiv (RingHom.id Real) (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)).V.carrier
--     (Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real)

-- Source: PhysLean (LorentzGroup.boost_inr_self_inr_self)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_inr_self_inr_self : ∀ {d : Nat} (i : Fin d) {β : Real} (hβ : Real.instLT.lt (abs β) 1),
--   Eq ((LorentzGroup.boost i β hβ).val (Sum.inr i) (Sum.inr i)) (LorentzGroup.γ β)

-- Source: PhysLean (Lorentz.contrBasis.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_contrbasis_eq_1 : ∀ (d : Nat), Eq (Lorentz.contrBasis d) (Module.Basis.ofEquivFun Lorentz.ContrMod.toFin1dℝEquiv)

-- Source: PhysLean (LorentzGroup.toRotation_continuous)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_torotation_continuous : ∀ {d : Nat}, Continuous LorentzGroup.toRotation

-- Source: PhysLean (Lorentz.contrCoToMatrix_ρ)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcotomatrix_ρ : ∀ (v : (Action.instMonoidalCategory.tensorObj Lorentz.complexContr Lorentz.complexCo).V.carrier)
--   (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (EquivLike.toFunLike.coe Lorentz.contrCoToMatrix
--       (LinearMap.instFunLike.coe
--         (TensorProduct.map (MonoidHom.instFunLike.coe Lorentz.complexContr.ρ M)
--           (MonoidHom.instFunLike.coe Lorentz.complexCo.ρ M))
--         v))
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--         (MonoidHom.instFunLike.coe LorentzGroup.toComplex (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M))
--         (EquivLike.toFunLike.coe Lorentz.contrCoToMatrix v))
--       (Matrix.inv.inv
--         (MonoidHom.instFunLike.coe LorentzGroup.toComplex (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M))))

-- Source: PhysLean (Lorentz.coBasisFin.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_cobasisfin_eq_1 : ∀ (d : Nat), Eq (Lorentz.coBasisFin d) ((Lorentz.coBasis d).reindex finSumFinEquiv)

-- Source: PhysLean (LorentzGroup.toVector_eq_fun)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_tovector_eq_fun : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem), Eq (LorentzGroup.toVector Λ) fun i => Λ.val i (Sum.inl 0)

-- Source: PhysLean (Lorentz.ContrℂModule.toFin13ℂEquiv_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_contrℂmodule_tofin13ℂequiv_apply : ∀ (a : Lorentz.ContrℂModule) (a_1 : Sum (Fin 1) (Fin 3)),
--   Eq (EquivLike.toFunLike.coe Lorentz.ContrℂModule.toFin13ℂEquiv a a_1)
--     (EquivLike.toFunLike.coe Lorentz.ContrℂModule.toFin13ℂFun a a_1)

-- Source: PhysLean (Lorentz.Contr.toCo)
-- [complex signature, not re-axiomatized]
-- lorentz_contr_toco : (d : Nat) → Action.instCategory.Hom (Lorentz.Contr d) (Lorentz.Co d)

-- Source: PhysLean (Lorentz.Vector.futureLightConeBoundary)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_futurelightconeboundary : {d : Nat} → Lorentz.Vector d → Set (Lorentz.Vector d)

-- Source: PhysLean (Lorentz.coContrContract_apply_metric)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrcontract_apply_metric : ∀ {d : Nat},
--   Eq
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)).V
--           (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom
--         ((Action.instBraidedCategory (ModuleCat Real) (LorentzGroup d).Elem).braiding (Lorentz.Co d)
--               (Lorentz.Contr d)).hom.hom)
--       (((fun X Y => LinearMap.instFunLike)
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Co d).V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorUnit (ModuleCat Real))
--                 (Lorentz.Contr d).V))
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Co d).V (Lorentz.Contr d).V)).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft (Lorentz.Co d).V
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.leftUnitor (Lorentz.Contr d).V).hom))
--         (((fun X Y => LinearMap.instFunLike)
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Co d).V
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                   (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)).V (Lorentz.Contr d).V))
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Co d).V
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                   (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V (Lorentz.Contr d).V))).coe
--           ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft (Lorentz.Co d).V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerRight Lorentz.coContrContract.hom
--                 (Lorentz.Contr d).V)))
--           (((fun X Y => LinearMap.instFunLike)
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Co d).V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Co d).V
--                     (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Contr d).V
--                       (Lorentz.Contr d).V)))
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Co d).V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                     (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Co d).V
--                       (Lorentz.Contr d).V)
--                     (Lorentz.Contr d).V))).coe
--             ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft (Lorentz.Co d).V
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.associator (Lorentz.Co d).V (Lorentz.Contr d).V
--                     (Lorentz.Contr d).V).inv))
--             (((fun X Y => LinearMap.instFunLike)
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                     (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Co d).V (Lorentz.Co d).V)
--                     (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Contr d).V
--                       (Lorentz.Contr d).V))
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Co d).V
--                     (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Co d).V
--                       (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Contr d).V
--                         (Lorentz.Contr d).V)))).coe
--               ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.associator (Lorentz.Co d).V (Lorentz.Co d).V
--                     (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Contr d).V
--                       (Lorentz.Contr d).V)).hom)
--               (TensorProduct.tmul Real
--                 (((fun X Y => LinearMap.instFunLike)
--                       (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V
--                       (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Co d)).V).coe
--                   ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom (Lorentz.preCoMetric d).hom) 1)
--                 (((fun X Y => LinearMap.instFunLike)
--                       (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V
--                       (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Contr d)).V).coe
--                   ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom (Lorentz.preContrMetric d).hom) 1)))))))
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V
--           (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom (Lorentz.preContrCoUnit d).hom) 1)

-- Source: PhysLean (Lorentz.Vector.inner_basis)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_inner_basis : ∀ {d : Nat} (p : Lorentz.Vector d) (μ : Sum (Fin 1) (Fin d)),
--   Eq ((Lorentz.Vector.instInnerReal d).inner Real p (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ)) (p μ)

-- Source: PhysLean (Lorentz.contrCoToMatrixRe.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcotomatrixre_eq_1 : ∀ {d : Nat},
--   Eq Lorentz.contrCoToMatrixRe
--     ((((Lorentz.contrBasis d).tensorProduct (Lorentz.coBasis d)).repr.trans
--           (Finsupp.linearEquivFunOnFinite Real Real (Prod (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d))))).trans
--       (LinearEquiv.curry Real Real (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d))))

-- Source: PhysLean (Lorentz.Vector.coordCLM)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_coordclm : {d : Nat} → Sum (Fin 1) (Fin d) → ContinuousLinearMap (RingHom.id Real) (Lorentz.Vector d) Real

-- Source: PhysLean (SpaceTime.deriv_comp_lorentz_action)
-- [complex signature, not re-axiomatized]
-- spacetime_deriv_comp_lorentz_action : ∀ {M : Type} [inst : NormedAddCommGroup M] [inst_1 : NormedSpace Real M] {d : Nat} (μ : Sum (Fin 1) (Fin d))
--   (f : SpaceTime d → M),
--   Differentiable Real f →
--     ∀ (Λ : (LorentzGroup d).Elem) (x : SpaceTime d),
--       Eq (SpaceTime.deriv μ (fun x => f (instHSMul.hSMul Λ x)) x)
--         (Finset.univ.sum fun ν => instHSMul.hSMul (Λ.val ν μ) (SpaceTime.deriv ν f (instHSMul.hSMul Λ x)))

-- Source: PhysLean (Lorentz.contrMetric.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmetric_eq_1 : Eq Lorentz.contrMetric
--   {
--     hom :=
--       ModuleCat.ofHom
--         {
--           toFun := fun a =>
--             have a' := a;
--             instHSMul.hSMul a' Lorentz.contrMetricVal,
--           map_add' := Lorentz.contrMetric._proof_1, map_smul' := Lorentz.contrMetric._proof_2 },
--     comm := Lorentz.contrMetric._proof_3 }

-- Source: PhysLean (realLorentzTensor.toComplex_eq_zero_iff)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_tocomplex_eq_zero_iff : ∀ {n : Nat} (c : Fin n → realLorentzTensor.Color) (v : realLorentzTensor.Tensor c),
--   Iff (Eq (LinearMap.instFunLike.coe realLorentzTensor.toComplex v) 0) (Eq v 0)

-- Source: PhysLean (Lorentz.SL2C.toMatrix_apply_contrMod)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_tomatrix_apply_contrmod : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex) (v : Lorentz.ContrMod 3),
--   Eq (Lorentz.ContrMod.mulVec (MonoidHom.instFunLike.coe Lorentz.SL2C.toMatrix M) v)
--     (EquivLike.toFunLike.coe Lorentz.ContrMod.toSelfAdjoint.symm
--       (LinearMap.instFunLike.coe (Lorentz.SL2C.toSelfAdjointMap M)
--         (EquivLike.toFunLike.coe Lorentz.ContrMod.toSelfAdjoint v)))

-- Source: PhysLean (complexLorentzTensor.contrCoUnit_eq_basis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_contrcounit_eq_basis : Eq complexLorentzTensor.contrCoUnit
--   (Finset.univ.sum fun i =>
--     Module.Basis.instFunLike.coe
--       (TensorSpecies.Tensor.basis
--         (Matrix.vecCons complexLorentzTensor.Color.up (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty)))
--       fun x =>
--       complexLorentzTensor.coContrUnit_eq_basis.match_1
--         (fun x =>
--           Fin
--             (complexLorentzTensor.repDim
--               (Matrix.vecCons complexLorentzTensor.Color.up
--                 (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty) x)))
--         x (fun _ => i) fun _ => i)

-- Source: PhysLean (Lorentz.coContrToMatrix_ρ_symm)
-- [complex signature, not re-axiomatized]
-- lorentz_cocontrtomatrix_ρ_symm : ∀ (v : Matrix (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3)) Complex) (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (LinearMap.instFunLike.coe
--       (TensorProduct.map (MonoidHom.instFunLike.coe Lorentz.complexCo.ρ M)
--         (MonoidHom.instFunLike.coe Lorentz.complexContr.ρ M))
--       (EquivLike.toFunLike.coe Lorentz.coContrToMatrix.symm v))
--     (EquivLike.toFunLike.coe Lorentz.coContrToMatrix.symm
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--         (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--           (Matrix.inv.inv
--               (MonoidHom.instFunLike.coe LorentzGroup.toComplex
--                 (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M))).transpose
--           v)
--         (MonoidHom.instFunLike.coe LorentzGroup.toComplex
--             (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M)).transpose))

-- Source: PhysLean (Lorentz.ContrMod.stdBasis_toFin1dℝEquiv_apply_same)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_stdbasis_tofin1dℝequiv_apply_same : ∀ {d : Nat} (μ : Sum (Fin 1) (Fin d)),
--   Eq
--     (EquivLike.toFunLike.coe Lorentz.ContrMod.toFin1dℝEquiv (Module.Basis.instFunLike.coe Lorentz.ContrMod.stdBasis μ)
--       μ)
--     1

-- Source: PhysLean (Lorentz.complexCoBasis_ρ_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcobasis_ρ_apply : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex) (i j : Sum (Fin 1) (Fin 3)),
--   Eq
--     (EquivLike.toFunLike.coe (LinearMap.toMatrix Lorentz.complexCoBasis Lorentz.complexCoBasis)
--       (MonoidHom.instFunLike.coe Lorentz.complexCo.ρ M) i j)
--     ((Matrix.inv.inv
--           (MonoidHom.instFunLike.coe LorentzGroup.toComplex
--             (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M))).transpose
--       i j)

-- Source: PhysLean (SpaceTime.instIsFiniteMeasureOnCompactsVolume)
-- [complex signature, not re-axiomatized]
-- spacetime_instisfinitemeasureoncompactsvolume : ∀ {d : Nat}, MeasureTheory.IsFiniteMeasureOnCompacts SpaceTime.instMeasureSpace.volume

-- Source: PhysLean (Lorentz.CoVector.basis)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_basis : {d : Nat} → Module.Basis (Sum (Fin 1) (Fin d)) Real (Lorentz.CoVector d)

-- Source: PhysLean (LorentzGroup.not_isOrthochronous_iff_le_neg_one)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_not_isorthochronous_iff_le_neg_one : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Iff (Not (LorentzGroup.IsOrthochronous Λ)) (Real.instLE.le (Λ.val (Sum.inl 0) (Sum.inl 0)) (-1))

-- Source: PhysLean (Lorentz.SL2C.toLorentzGroup_isOrthochronous)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_tolorentzgroup_isorthochronous : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   LorentzGroup.IsOrthochronous (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M)

-- Source: PhysLean (Lorentz.Velocity.timeComponent_nonneg)
-- [complex signature, not re-axiomatized]
-- lorentz_velocity_timecomponent_nonneg : ∀ {d : Nat} (v : (Lorentz.Velocity d).Elem), Real.instLE.le 0 v.val.timeComponent

-- Source: PhysLean (Lorentz.contrContrContractField.matrix_eq_id_iff)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_matrix_eq_id_iff : ∀ {d : Nat} {Λ : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real},
--   Iff (Eq Λ 1)
--     (∀ (w v : (Lorentz.Contr d).V.carrier),
--       Eq
--         (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--           (TensorProduct.tmul Real v (Lorentz.ContrMod.mulVec Λ w)))
--         (LinearMap.instFunLike.coe Lorentz.contrContrContractField (TensorProduct.tmul Real v w)))

-- Source: PhysLean (Lorentz.Vector.differentiable_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_differentiable_apply : ∀ {d : Nat} {α : Type u_1} [inst : NormedAddCommGroup α] [inst_1 : NormedSpace Real α] (f : α → Lorentz.Vector d),
--   Iff (∀ (i : Sum (Fin 1) (Fin d)), Differentiable Real fun x => f x i) (Differentiable Real f)

-- Source: PhysLean (Lorentz.Contr.ρ_stdBasis)
-- [complex signature, not re-axiomatized]
-- lorentz_contr_ρ_stdbasis : ∀ (μ : Sum (Fin 1) (Fin 3)) (Λ : (LorentzGroup 3).Elem),
--   Eq
--     (LinearMap.instFunLike.coe (MonoidHom.instFunLike.coe (Lorentz.Contr 3).ρ Λ)
--       (Module.Basis.instFunLike.coe Lorentz.ContrMod.stdBasis μ))
--     (Finset.univ.sum fun j => instHSMul.hSMul (Λ.val j μ) (Module.Basis.instFunLike.coe Lorentz.ContrMod.stdBasis j))

-- Source: PhysLean (Lorentz.CoVector.basis_apply)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_basis_apply : ∀ {d : Nat} (μ ν : Sum (Fin 1) (Fin d)), Eq (Module.Basis.instFunLike.coe Lorentz.CoVector.basis μ ν) (ite (Eq μ ν) 1 0)

-- Source: PhysLean (Lorentz.contrCoUnitVal_expand_tmul)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcounitval_expand_tmul : Eq Lorentz.contrCoUnitVal
--   (instHAdd.hAdd
--     (instHAdd.hAdd
--       (instHAdd.hAdd
--         (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inl 0))
--           (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inl 0)))
--         (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 0))
--           (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 0))))
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 1))
--         (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 1))))
--     (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Lorentz.complexContrBasis (Sum.inr 2))
--       (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 2))))

-- Source: PhysLean (Lorentz.Vector.causallyUnrelated)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causallyunrelated : {d : Nat} → Lorentz.Vector d → Lorentz.Vector d → Prop

-- Source: PhysLean (Lorentz.Vector.smul_sub)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_smul_sub : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem) (p q : Lorentz.Vector d),
--   Eq (instHSMul.hSMul Λ (instHSub.hSub p q)) (instHSub.hSub (instHSMul.hSMul Λ p) (instHSMul.hSMul Λ q))

-- Source: PhysLean (complexLorentzTensor.actionT_contrCoUnit)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_actiont_contrcounit : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (instHSMul.hSMul g complexLorentzTensor.contrCoUnit) complexLorentzTensor.contrCoUnit

-- Source: PhysLean (Lorentz.contr_preCoContrUnit)
-- [complex signature, not re-axiomatized]
-- lorentz_contr_precocontrunit : ∀ {d : Nat} (x : (Lorentz.Contr d).V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj
--               (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)) (Lorentz.Contr d)).V
--           (Lorentz.Contr d).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom
--         (Action.instMonoidalCategory.leftUnitor (Lorentz.Contr d)).hom.hom)
--       (((fun X Y => LinearMap.instFunLike)
--             (Action.instMonoidalCategory.tensorObj
--                 (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)) (Lorentz.Contr d)).V
--             (Action.instMonoidalCategory.tensorObj
--                 (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)) (Lorentz.Contr d)).V).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom
--           (Action.instMonoidalCategory.whiskerRight Lorentz.contrCoContract (Lorentz.Contr d)).hom)
--         (((fun X Y => LinearMap.instFunLike)
--               (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d)
--                   (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d))).V
--               (Action.instMonoidalCategory.tensorObj
--                   (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)) (Lorentz.Contr d)).V).coe
--           ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom
--             (Action.instMonoidalCategory.associator (Lorentz.Contr d) (Lorentz.Co d) (Lorentz.Contr d)).inv.hom)
--           (TensorProduct.tmul Real x
--             (((fun X Y => LinearMap.instFunLike)
--                   (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V
--                   (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)).V).coe
--               ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom (Lorentz.preCoContrUnit d).hom) 1)))))
--     x

-- Source: PhysLean (Lorentz.Velocity.zero.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_velocity_zero_eq_1 : ∀ {d : Nat}, Eq Lorentz.Velocity.zero ⟨Module.Basis.instFunLike.coe Lorentz.Vector.basis (Sum.inl 0), ⋯⟩

-- Source: PhysLean (Lorentz.CoVector.equivEuclid)
-- [complex signature, not re-axiomatized]
-- lorentz_covector_equiveuclid : (d : Nat) → LinearEquiv (RingHom.id Real) (Lorentz.CoVector d) (EuclideanSpace Real (Sum (Fin 1) (Fin d)))

-- Source: PhysLean (Lorentz.complexContrBasis)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcontrbasis : Module.Basis (Sum (Fin 1) (Fin 3)) Complex Lorentz.complexContr.V.carrier

-- Source: PhysLean (Lorentz.Vector.smul_eq_sum)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_smul_eq_sum : ∀ {d : Nat} (i : Sum (Fin 1) (Fin d)) (Λ : (LorentzGroup d).Elem) (p : Lorentz.Vector d),
--   Eq (instHSMul.hSMul Λ p i) (Finset.univ.sum fun j => instHMul.hMul (Λ.val i j) (p j))

-- Source: PhysLean (complexLorentzTensor.altLeftLeftUnit_symm)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_altleftleftunit_symm : Eq
--   (EquivLike.toFunLike.coe
--     (TensorSpecies.Tensorial.self complexLorentzTensor
--         (Matrix.vecCons complexLorentzTensor.Color.downL
--           (Matrix.vecCons complexLorentzTensor.Color.upL Matrix.vecEmpty))).toTensor
--     complexLorentzTensor.altLeftLeftUnit)
--   (LinearMap.instFunLike.coe (TensorSpecies.Tensor.permT (Matrix.vecCons 1 (Matrix.vecCons 0 Matrix.vecEmpty)) ⋯)
--     (EquivLike.toFunLike.coe
--       (TensorSpecies.Tensorial.self complexLorentzTensor
--           (Matrix.vecCons complexLorentzTensor.Color.upL
--             (Matrix.vecCons complexLorentzTensor.Color.downL Matrix.vecEmpty))).toTensor
--       complexLorentzTensor.leftAltLeftUnit))

-- Source: PhysLean (Lorentz.coCoToMatrix.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_cocotomatrix_eq_1 : Eq Lorentz.coCoToMatrix
--   (((Lorentz.complexCoBasis.tensorProduct Lorentz.complexCoBasis).repr.trans
--         (Finsupp.linearEquivFunOnFinite Complex Complex (Prod (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3))))).trans
--     (LinearEquiv.curry Complex Complex (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3))))

-- Source: PhysLean (LorentzGroup.dual_mem)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_dual_mem : ∀ {d : Nat} {Λ : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real},
--   Set.instMembership.mem (LorentzGroup d) Λ → Set.instMembership.mem (LorentzGroup d) (minkowskiMatrix.dual Λ)

-- Source: PhysLean (Lorentz.CoMod.stdBasis_decomp)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_stdbasis_decomp : ∀ {d : Nat} (v : Lorentz.CoMod d),
--   Eq v (Finset.univ.sum fun i => instHSMul.hSMul (v.toFin1dℝ i) (Module.Basis.instFunLike.coe Lorentz.CoMod.stdBasis i))

-- Source: PhysLean (Lorentz.«_aux_PhysLean_Relativity_Tensors_RealTensor_Vector_Pre_Modules___macroRules_Lorentz_term_*ᵥ__1»)
-- [complex signature, not re-axiomatized]
-- lorentz_«_aux_physlean_relativity_tensors_realtensor_vector_pre_modules___macrorules_lorentz_term_*ᵥ__1» : Lean.Macro

-- Source: PhysLean (Lorentz.Vector.CausalCharacter.lightLike.elim)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_causalcharacter_lightlike_elim : {motive : Lorentz.Vector.CausalCharacter → Sort u} →
--   (t : Lorentz.Vector.CausalCharacter) → Eq t.ctorIdx 1 → motive Lorentz.Vector.CausalCharacter.lightLike → motive t

-- Source: PhysLean (realLorentzTensor.τ_up_eq_down)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_τ_up_eq_down : ∀ {d : Nat}, Eq ((realLorentzTensor d).τ realLorentzTensor.Color.up) realLorentzTensor.Color.down

-- Source: PhysLean (Lorentz.ContrMod.stdBasis.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_contrmod_stdbasis_eq_1 : ∀ {d : Nat}, Eq Lorentz.ContrMod.stdBasis (Module.Basis.ofEquivFun Lorentz.ContrMod.toFin1dℝEquiv)

-- Source: PhysLean (Lorentz.Vector.smul_basis)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_smul_basis : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem) (μ : Sum (Fin 1) (Fin d)),
--   Eq (instHSMul.hSMul Λ (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ))
--     (Finset.univ.sum fun ν => instHSMul.hSMul (Λ.val ν μ) (Module.Basis.instFunLike.coe Lorentz.Vector.basis ν))

-- Source: PhysLean (CliffordAlgebra.ι_mul_ι_comm_of_isOrtho)
-- [complex signature, not re-axiomatized]
-- cliffordalgebra_ι_mul_ι_comm_of_isortho : ∀ {R : Type u_1} [inst : CommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : Module R M]
--   {Q : QuadraticForm R M} {a b : M},
--   QuadraticMap.IsOrtho Q a b →
--     Eq
--       (instHMul.hMul (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) a)
--         (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) b))
--       (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg
--         (instHMul.hMul (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) b)
--           (LinearMap.instFunLike.coe (CliffordAlgebra.ι Q) a)))

-- Source: PhysLean (Lorentz.contrContrContractField.on_basis_mulVec)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrcontractfield_on_basis_mulvec : ∀ {d : Nat} {Λ : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real} (μ ν : Sum (Fin 1) (Fin d)),
--   Eq
--     (LinearMap.instFunLike.coe Lorentz.contrContrContractField
--       (TensorProduct.tmul Real (Module.Basis.instFunLike.coe Lorentz.ContrMod.stdBasis μ)
--         (Lorentz.ContrMod.mulVec Λ (Module.Basis.instFunLike.coe Lorentz.ContrMod.stdBasis ν))))
--     (instHMul.hMul (minkowskiMatrix μ μ) (Λ μ ν))

-- Source: PhysLean (Lorentz.complexCoBasisFin4_apply_three)
-- [complex signature, not re-axiomatized]
-- lorentz_complexcobasisfin4_apply_three : Eq (Module.Basis.instFunLike.coe Lorentz.complexCoBasisFin4 3)
--   (Module.Basis.instFunLike.coe Lorentz.complexCoBasis (Sum.inr 2))

-- Source: PhysLean (SpaceTime.schwartzAction_injective)
-- [complex signature, not re-axiomatized]
-- spacetime_schwartzaction_injective : ∀ {d : Nat} (Λ : (LorentzGroup d).Elem),
--   Function.Injective (ContinuousLinearMap.funLike.coe (MonoidHom.instFunLike.coe SpaceTime.schwartzAction Λ))

-- Source: PhysLean (Lorentz.CoMod.stdBasis_repr_symm_apply_val)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_stdbasis_repr_symm_apply_val : ∀ {d : Nat} (a : Finsupp (Sum (Fin 1) (Fin d)) Real) (a_1 : Sum (Fin 1) (Fin d)),
--   Eq ((EquivLike.toFunLike.coe Lorentz.CoMod.stdBasis.repr.symm a).val a_1) (Finsupp.instFunLike.coe a a_1)

-- Source: PhysLean (Lorentz.contrContrToMatrixRe_ρ_symm)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrtomatrixre_ρ_symm : ∀ {d : Nat} (v : Matrix (Sum (Fin 1) (Fin d)) (Sum (Fin 1) (Fin d)) Real) (M : (LorentzGroup d).Elem),
--   Eq
--     (LinearMap.instFunLike.coe
--       (TensorProduct.map (MonoidHom.instFunLike.coe (Lorentz.Contr d).ρ M)
--         (MonoidHom.instFunLike.coe (Lorentz.Contr d).ρ M))
--       (EquivLike.toFunLike.coe Lorentz.contrContrToMatrixRe.symm v))
--     (EquivLike.toFunLike.coe Lorentz.contrContrToMatrixRe.symm
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul M.val v)
--         M.val.transpose))

-- Source: PhysLean (realLorentzTensor.repDim_down)
-- [complex signature, not re-axiomatized]
-- reallorentztensor_repdim_down : ∀ {d : Nat}, Eq ((realLorentzTensor d).repDim realLorentzTensor.Color.down) (instHAdd.hAdd 1 d)

-- Source: PhysLean (Lorentz.Vector.spatialCLM_basis_sum_inl)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_spatialclm_basis_sum_inl : ∀ {d : Nat},
--   Eq
--     (ContinuousLinearMap.funLike.coe (Lorentz.Vector.spatialCLM d)
--       (Module.Basis.instFunLike.coe Lorentz.Vector.basis (Sum.inl 0)))
--     0

-- Source: PhysLean (Lorentz.Vector.spatialCLM_apply_eq_spatialPart)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_spatialclm_apply_eq_spatialpart : ∀ {d : Nat} (v : Lorentz.Vector d) (i : Fin d),
--   Eq ((ContinuousLinearMap.funLike.coe (Lorentz.Vector.spatialCLM d) v).ofLp i) (v.spatialPart.ofLp i)

-- Source: PhysLean (Lorentz.SL2C.toSelfAdjointMap_apply_pauliBasis'_inl)
-- [complex signature, not re-axiomatized]
-- lorentz_sl2c_toselfadjointmap_apply_paulibasis'_inl : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (LinearMap.instFunLike.coe (Lorentz.SL2C.toSelfAdjointMap M)
--       (Module.Basis.instFunLike.coe PauliMatrix.pauliBasis' (Sum.inl 0)))
--     (instHAdd.hAdd
--       (instHAdd.hAdd
--         (instHAdd.hAdd
--           (instHSMul.hSMul
--             (instHDiv.hDiv
--               (instHAdd.hAdd
--                 (instHAdd.hAdd
--                   (instHAdd.hAdd (instHPow.hPow (Complex.instNorm.norm (M.val 0 0)) 2)
--                     (instHPow.hPow (Complex.instNorm.norm (M.val 0 1)) 2))
--                   (instHPow.hPow (Complex.instNorm.norm (M.val 1 0)) 2))
--                 (instHPow.hPow (Complex.instNorm.norm (M.val 1 1)) 2))
--               2)
--             (Module.Basis.instFunLike.coe PauliMatrix.pauliBasis' (Sum.inl 0)))
--           (instHSMul.hSMul
--             (Real.instNeg.neg
--               (instHAdd.hAdd
--                 (instHAdd.hAdd
--                   (instHAdd.hAdd (instHMul.hMul (M.val 0 1).re (M.val 1 1).re)
--                     (instHMul.hMul (M.val 0 1).im (M.val 1 1).im))
--                   (instHMul.hMul (M.val 0 0).im (M.val 1 0).im))
--                 (instHMul.hMul (M.val 0 0).re (M.val 1 0).re)))
--             (Module.Basis.instFunLike.coe PauliMatrix.pauliBasis' (Sum.inr 0))))
--         (instHSMul.hSMul
--           (instHAdd.hAdd
--             (instHSub.hSub
--               (instHAdd.hAdd (instHMul.hMul (Real.instNeg.neg (M.val 0 0).re) (M.val 1 0).im)
--                 (instHMul.hMul (M.val 1 0).re (M.val 0 0).im))
--               (instHMul.hMul (M.val 0 1).re (M.val 1 1).im))
--             (instHMul.hMul (M.val 0 1).im (M.val 1 1).re))
--           (Module.Basis.instFunLike.coe PauliMatrix.pauliBasis' (Sum.inr 1))))
--       (instHSMul.hSMul
--         (instHDiv.hDiv
--           (instHAdd.hAdd
--             (instHAdd.hAdd
--               (instHSub.hSub (Real.instNeg.neg (instHPow.hPow (Complex.instNorm.norm (M.val 0 0)) 2))
--                 (instHPow.hPow (Complex.instNorm.norm (M.val 0 1)) 2))
--               (instHPow.hPow (Complex.instNorm.norm (M.val 1 0)) 2))
--             (instHPow.hPow (Complex.instNorm.norm (M.val 1 1)) 2))
--           2)
--         (Module.Basis.instFunLike.coe PauliMatrix.pauliBasis' (Sum.inr 2))))

-- Source: PhysLean (Lorentz.CoMod.stdBasis_apply_same)
-- [complex signature, not re-axiomatized]
-- lorentz_comod_stdbasis_apply_same : ∀ {d : Nat} (μ : Sum (Fin 1) (Fin d)), Eq ((Module.Basis.instFunLike.coe Lorentz.CoMod.stdBasis μ).val μ) 1

-- Source: PhysLean (LorentzGroup.transpose_val)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_transpose_val : ∀ {d : Nat} {Λ : (LorentzGroup d).Elem}, Eq (LorentzGroup.transpose Λ).val Λ.val.transpose

-- Source: PhysLean (LorentzGroup.coeForℤ₂)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_coeforℤ₂ : ContinuousMap (Set.instInsert.insert (-1) (Set.instSingletonSet.singleton 1)).Elem (Multiplicative (ZMod 2))

-- Source: PhysLean (Lorentz.contrContrToMatrix_ρ_symm)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrtomatrix_ρ_symm : ∀ (v : Matrix (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3)) Complex) (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (LinearMap.instFunLike.coe
--       (TensorProduct.map (MonoidHom.instFunLike.coe Lorentz.complexContr.ρ M)
--         (MonoidHom.instFunLike.coe Lorentz.complexContr.ρ M))
--       (EquivLike.toFunLike.coe Lorentz.contrContrToMatrix.symm v))
--     (EquivLike.toFunLike.coe Lorentz.contrContrToMatrix.symm
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--         (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--           (MonoidHom.instFunLike.coe LorentzGroup.toComplex (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M))
--           v)
--         (MonoidHom.instFunLike.coe LorentzGroup.toComplex
--             (MonoidHom.instFunLike.coe Lorentz.SL2C.toLorentzGroup M)).transpose))

-- Source: PhysLean (SpaceTime.time_toTimeAndSpace_symm)
-- [complex signature, not re-axiomatized]
-- spacetime_time_totimeandspace_symm : ∀ {d : Nat} {c : SpeedOfLight} (t : Time) (s : Space d),
--   Eq
--     (LinearMap.instFunLike.coe (SpaceTime.time c)
--       (EquivLike.toFunLike.coe (SpaceTime.toTimeAndSpace c).symm { fst := t, snd := s }))
--     t

-- Source: PhysLean (Lorentz.«termℂ²ˣ²»)
-- [complex signature, not re-axiomatized]
-- lorentz_«termℂ²ˣ²» : Lean.ParserDescr

-- Source: PhysLean (Lorentz.contrCoContract_apply_metric)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcocontract_apply_metric : ∀ {d : Nat},
--   Eq
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)).V
--           (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom
--         ((Action.instBraidedCategory (ModuleCat Real) (LorentzGroup d).Elem).braiding (Lorentz.Contr d)
--               (Lorentz.Co d)).hom.hom)
--       (((fun X Y => LinearMap.instFunLike)
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Contr d).V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorUnit (ModuleCat Real)) (Lorentz.Co d).V))
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Contr d).V (Lorentz.Co d).V)).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft (Lorentz.Contr d).V
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.leftUnitor (Lorentz.Co d).V).hom))
--         (((fun X Y => LinearMap.instFunLike)
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Contr d).V
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                   (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Co d)).V (Lorentz.Co d).V))
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Contr d).V
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                   (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V (Lorentz.Co d).V))).coe
--           ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft (Lorentz.Contr d).V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerRight Lorentz.contrCoContract.hom
--                 (Lorentz.Co d).V)))
--           (((fun X Y => LinearMap.instFunLike)
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Contr d).V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Contr d).V
--                     (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Co d).V
--                       (Lorentz.Co d).V)))
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Contr d).V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                     (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Contr d).V
--                       (Lorentz.Co d).V)
--                     (Lorentz.Co d).V))).coe
--             ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft (Lorentz.Contr d).V
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.associator (Lorentz.Contr d).V (Lorentz.Co d).V
--                     (Lorentz.Co d).V).inv))
--             (((fun X Y => LinearMap.instFunLike)
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                     (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Contr d).V
--                       (Lorentz.Contr d).V)
--                     (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Co d).V (Lorentz.Co d).V))
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Contr d).V
--                     (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Contr d).V
--                       (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Co d).V
--                         (Lorentz.Co d).V)))).coe
--               ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.associator (Lorentz.Contr d).V
--                     (Lorentz.Contr d).V
--                     (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj (Lorentz.Co d).V
--                       (Lorentz.Co d).V)).hom)
--               (TensorProduct.tmul Real
--                 (((fun X Y => LinearMap.instFunLike)
--                       (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V
--                       (Action.instMonoidalCategory.tensorObj (Lorentz.Contr d) (Lorentz.Contr d)).V).coe
--                   ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom (Lorentz.preContrMetric d).hom) 1)
--                 (((fun X Y => LinearMap.instFunLike)
--                       (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V
--                       (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Co d)).V).coe
--                   ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom (Lorentz.preCoMetric d).hom) 1)))))))
--     (((fun X Y => LinearMap.instFunLike) (Action.instMonoidalCategory.tensorUnit (Rep Real (LorentzGroup d).Elem)).V
--           (Action.instMonoidalCategory.tensorObj (Lorentz.Co d) (Lorentz.Contr d)).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Real).hom (Lorentz.preCoContrUnit d).hom) 1)

-- Source: PhysLean (LorentzGroup.genBoostAux₁_apply_basis)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_genboostaux₁_apply_basis : ∀ {d : Nat} (u v : (Lorentz.Velocity d).Elem) (μ : Sum (Fin 1) (Fin d)),
--   Eq (LinearMap.instFunLike.coe (LorentzGroup.genBoostAux₁ u v) (Module.Basis.instFunLike.coe Lorentz.Vector.basis μ))
--     (instHSMul.hSMul (instHMul.hMul (instHMul.hMul 2 (minkowskiMatrix μ μ)) (u.val μ)) v.val)

-- Source: PhysLean (Lorentz.contrContrToMatrix.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_contrcontrtomatrix_eq_1 : Eq Lorentz.contrContrToMatrix
--   (((Lorentz.complexContrBasis.tensorProduct Lorentz.complexContrBasis).repr.trans
--         (Finsupp.linearEquivFunOnFinite Complex Complex (Prod (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3))))).trans
--     (LinearEquiv.curry Complex Complex (Sum (Fin 1) (Fin 3)) (Sum (Fin 1) (Fin 3))))

-- Source: PhysLean (complexLorentzTensor.termδL)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_termδl : Lean.ParserDescr

-- Source: PhysLean (minkowskiMatrix.off_diag_zero)
-- [complex signature, not re-axiomatized]
-- minkowskimatrix_off_diag_zero : ∀ {d : Nat} {μ ν : Sum (Fin 1) (Fin d)}, Ne μ ν → Eq (minkowskiMatrix μ ν) 0

-- Source: PhysLean (Lorentz.Vector.basis.eq_1)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_basis_eq_1 : ∀ {d : Nat}, Eq Lorentz.Vector.basis (Pi.basisFun Real (Sum (Fin 1) (Fin d)))

-- Source: PhysLean (Lorentz.Vector.indexEquiv)
-- [complex signature, not re-axiomatized]
-- lorentz_vector_indexequiv : {d : Nat} →
--   Equiv (TensorSpecies.Tensor.ComponentIdx (Matrix.vecCons realLorentzTensor.Color.up Matrix.vecEmpty))
--     (Sum (Fin 1) (Fin d))

-- Source: PhysLean (LorentzGroup.γ_neg)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_γ_neg : ∀ (β : Real), Eq (LorentzGroup.γ (Real.instNeg.neg β)) (LorentzGroup.γ β)

-- Source: PhysLean (LorentzGroup.orthchroRep)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_orthchrorep : {d : Nat} → MonoidHom (LorentzGroup d).Elem (Multiplicative (ZMod 2))

-- Source: PhysLean (LorentzGroup.boost_inl_0_inr_other)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_boost_inl_0_inr_other : ∀ {d : Nat} {i j : Fin d} {β : Real} (hβ : Real.instLT.lt (abs β) 1),
--   Ne j i → Eq ((LorentzGroup.boost i β hβ).val (Sum.inl 0) (Sum.inr j)) 0

-- Source: PhysLean (SpaceTime.timeSlice)
-- [complex signature, not re-axiomatized]
-- spacetime_timeslice : {d : Nat} → {M : Type} → optParam SpeedOfLight 1 → Equiv (SpaceTime d → M) (Time → Space d → M)

-- Source: PhysLean (complexLorentzTensor.coMetric_eq_basis)
-- [complex signature, not re-axiomatized]
-- complexlorentztensor_cometric_eq_basis : Eq complexLorentzTensor.coMetric
--   (instHSub.hSub
--     (instHSub.hSub
--       (instHSub.hSub
--         (Module.Basis.instFunLike.coe
--           (TensorSpecies.Tensor.basis
--             (Matrix.vecCons complexLorentzTensor.Color.down
--               (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty)))
--           fun x =>
--           complexLorentzTensor.coMetric_eq_basis.match_1
--             (fun x =>
--               Fin
--                 (complexLorentzTensor.repDim
--                   (Matrix.vecCons complexLorentzTensor.Color.down
--                     (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty) x)))
--             x (fun _ => 0) fun _ => 0)
--         (Module.Basis.instFunLike.coe
--           (TensorSpecies.Tensor.basis
--             (Matrix.vecCons complexLorentzTensor.Color.down
--               (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty)))
--           fun x =>
--           complexLorentzTensor.coMetric_eq_basis.match_1
--             (fun x =>
--               Fin
--                 (complexLorentzTensor.repDim
--                   (Matrix.vecCons complexLorentzTensor.Color.down
--                     (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty) x)))
--             x (fun _ => 1) fun _ => 1))
--       (Module.Basis.instFunLike.coe
--         (TensorSpecies.Tensor.basis
--           (Matrix.vecCons complexLorentzTensor.Color.down
--             (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty)))
--         fun x =>
--         complexLorentzTensor.coMetric_eq_basis.match_1
--           (fun x =>
--             Fin
--               (complexLorentzTensor.repDim
--                 (Matrix.vecCons complexLorentzTensor.Color.down
--                   (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty) x)))
--           x (fun _ => 2) fun _ => 2))
--     (Module.Basis.instFunLike.coe
--       (TensorSpecies.Tensor.basis
--         (Matrix.vecCons complexLorentzTensor.Color.down
--           (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty)))
--       fun x =>
--       complexLorentzTensor.coMetric_eq_basis.match_1
--         (fun x =>
--           Fin
--             (complexLorentzTensor.repDim
--               (Matrix.vecCons complexLorentzTensor.Color.down
--                 (Matrix.vecCons complexLorentzTensor.Color.down Matrix.vecEmpty) x)))
--         x (fun _ => 3) fun _ => 3))

-- Source: PhysLean (LorentzGroup.orthchroMapReal)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_orthchromapreal : {d : Nat} → ContinuousMap (LorentzGroup d).Elem Real

-- Source: PhysLean (LorentzGroup.toVector)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_tovector : {d : Nat} → (LorentzGroup d).Elem → Lorentz.Vector d

-- Source: PhysLean (Lorentz.Velocity.instTopologicalSpaceElemVector)
-- [complex signature, not re-axiomatized]
-- lorentz_velocity_insttopologicalspaceelemvector : {d : Nat} → TopologicalSpace (Lorentz.Velocity d).Elem

-- Source: PhysLean (LorentzGroup.parity)
-- [complex signature, not re-axiomatized]
-- lorentzgroup_parity : {d : Nat} → (LorentzGroup d).Elem

end PhysicsGenerator.SpecialRelativity
