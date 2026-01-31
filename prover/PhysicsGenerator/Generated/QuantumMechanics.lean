import Mathlib
import PhysicsGenerator.Basic

/-!
# QuantumMechanics (Generated from PhysLean)

Auto-generated from PhysLean catalog (version: v4.26.0).
These axioms correspond to proven theorems in PhysLean.
Re-axiomatized here for Lean 4.27 compatibility.

DO NOT EDIT — regenerate with `just generate-axioms`.
-/

namespace PhysicsGenerator.QuantumMechanics

open PhysicsGenerator

-- ══════════════════════════════════════════════════════════════
-- Helper Types (for axiom signatures)
-- ══════════════════════════════════════════════════════════════

axiom Hamiltonian : Type
axiom apply_hamiltonian : Hamiltonian → QState → QState
axiom state_time_deriv : (Time → QState) → Time → QState
axiom scale_state : ℝ → QState → QState
axiom measure_prob : Observable → QState → ℝ → ℝ
axiom commutator : Observable → Observable → Observable
axiom position_op : Observable
axiom momentum_op : Observable
axiom identity_op : Observable
axiom ihbar : ℝ

-- ══════════════════════════════════════════════════════════════
-- Theorems (from PhysLean — re-axiomatized)
-- ══════════════════════════════════════════════════════════════

-- Source: PhysLean (StandardModel.HiggsField.Potential.toFun_neg)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_tofun_neg : ∀ (P : StandardModel.HiggsField.Potential) (φ : StandardModel.HiggsField) (x : SpaceTime),
--   Eq (P.neg.toFun φ x) (Real.instNeg.neg (P.toFun φ x))

-- Source: PhysLean (Fermion.leftAltContraction)
-- [complex signature, not re-axiomatized]
-- fermion_leftaltcontraction : Action.instCategory.Hom (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded)
--   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))

-- Source: PhysLean (Fermion.leftAltContraction_basis)
-- [complex signature, not re-axiomatized]
-- fermion_leftaltcontraction_basis : ∀ (i j : Fin 2),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.leftAltContraction.hom)
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.leftBasis i)
--         (Module.Basis.instFunLike.coe Fermion.altLeftBasis j)))
--     (ite (Eq i.val j.val) 1 0)

-- Source: PhysLean (StandardModel.GaugeGroupI.toSU2)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupi_tosu2 : MonoidHom StandardModel.GaugeGroupI
--   (Subtype fun x => SetLike.instMembership.mem (Matrix.specialUnitaryGroup (Fin 2) Complex) x)

-- Source: PhysLean (Fermion.altLeftaltLeftToMatrix)
-- [complex signature, not re-axiomatized]
-- fermion_altleftaltlefttomatrix : LinearEquiv (RingHom.id Complex)
--   (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.altLeftHanded).V.carrier
--   (Matrix (Fin 2) (Fin 2) Complex)

-- Source: PhysLean (Fermion.altLeftAltRightToMatrix_ρ)
-- [complex signature, not re-axiomatized]
-- fermion_altleftaltrighttomatrix_ρ : ∀ (v : (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.altRightHanded).V.carrier)
--   (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (EquivLike.toFunLike.coe Fermion.altLeftAltRightToMatrix
--       (LinearMap.instFunLike.coe
--         (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.altLeftHanded.ρ M)
--           (MonoidHom.instFunLike.coe Fermion.altRightHanded.ρ M))
--         v))
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.inv.inv M.val).transpose
--         (EquivLike.toFunLike.coe Fermion.altLeftAltRightToMatrix v))
--       (Matrix.inv.inv M.val).conjTranspose.transpose)

-- Source: PhysLean (StandardModel.HiggsField.gaugeAction)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_gaugeaction : InformalDefinition

-- Source: PhysLean (StandardModel.instContMDiffVectorBundleTopWithTopENatRealSpaceTimeOfNatNatHiggsVecHiggsBundleVectorAsSmoothManifold)
-- [complex signature, not re-axiomatized]
-- standardmodel_instcontmdiffvectorbundletopwithtopenatrealspacetimeofnatnathiggsvechiggsbundlevectorassmoothmanifold : ContMDiffVectorBundle WithTop.top.top StandardModel.HiggsVec StandardModel.HiggsBundle
--   (Lorentz.Vector.asSmoothManifold 3)

-- Source: PhysLean (StandardModel.HiggsField.toHiggsVec)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_tohiggsvec : StandardModel.HiggsField → SpaceTime → StandardModel.HiggsVec

-- Source: PhysLean (Fermion.RightHandedModule.toFin2ℂEquiv)
-- [complex signature, not re-axiomatized]
-- fermion_righthandedmodule_tofin2ℂequiv : LinearEquiv (RingHom.id Complex) Fermion.RightHandedModule (Fin 2 → Complex)

-- Source: PhysLean (StandardModel.GaugeGroupI.instStar)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupi_inststar : Star StandardModel.GaugeGroupI

-- Source: PhysLean (StandardModel.gaugeTransformI)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugetransformi : InformalDefinition

-- Source: PhysLean (StandardModel.GaugeGroupI.toU1.eq_1)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupi_tou1_eq_1 : Eq StandardModel.GaugeGroupI.toU1
--   { toFun := fun g => g.snd.snd, map_one' := StandardModel.GaugeGroupI.toU1._proof_1,
--     map_mul' := StandardModel.GaugeGroupI.toU1._proof_2 }

-- Source: PhysLean (StandardModel.HiggsVec.ofReal)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsvec_ofreal : Real → StandardModel.HiggsVec

-- Source: PhysLean (Fermion.altRightMetric_apply_one)
-- [complex signature, not re-axiomatized]
-- fermion_altrightmetric_apply_one : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.altRightHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altRightMetric.hom) 1)
--   Fermion.altRightMetricVal

-- Source: PhysLean (StandardModel.HiggsField.inner_neg_left)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_inner_neg_left : ∀ (φ1 φ2 : StandardModel.HiggsField),
--   Eq
--     (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex.inner (SpaceTime → Complex)
--       (ContMDiffSection.instNeg.neg φ1) φ2)
--     (Pi.instNeg.neg
--       (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex.inner (SpaceTime → Complex) φ1 φ2))

-- Source: PhysLean (StandardModel.HiggsField.Potential.toFun_eq_zero_iff)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_tofun_eq_zero_iff : ∀ (P : StandardModel.HiggsField.Potential),
--   Ne P.𝓵 0 →
--     ∀ (φ : StandardModel.HiggsField) (x : SpaceTime),
--       Iff (Eq (P.toFun φ x) 0)
--         (Or (Eq (ContMDiffSection.instDFunLike.coe φ x) 0) (Eq (φ.normSq x) (instHDiv.hDiv P.μ2 P.𝓵)))

-- Source: PhysLean (StandardModel.HiggsField.Potential.pos_𝓵_quadDiscrim_zero_bound)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_pos_𝓵_quaddiscrim_zero_bound : ∀ (P : StandardModel.HiggsField.Potential),
--   Real.instLT.lt 0 P.𝓵 →
--     ∀ (φ : StandardModel.HiggsField) (x : SpaceTime),
--       Real.instLE.le (instHDiv.hDiv (Real.instNeg.neg (instHPow.hPow P.μ2 2)) (instHMul.hMul 4 P.𝓵)) (P.toFun φ x)

-- Source: PhysLean (StandardModel.HiggsField.Potential.neg_𝓵_sol_exists_iff)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_neg_𝓵_sol_exists_iff : ∀ (P : StandardModel.HiggsField.Potential),
--   Real.instLT.lt P.𝓵 0 →
--     ∀ (c : Real),
--       Iff (Exists fun φ => Exists fun x => Eq (P.toFun φ x) c)
--         (Or (And (Real.instLT.lt 0 P.μ2) (Real.instLE.le c 0))
--           (And (Real.instLE.le P.μ2 0)
--             (Real.instLE.le c (instHDiv.hDiv (Real.instNeg.neg (instHPow.hPow P.μ2 2)) (instHMul.hMul 4 P.𝓵)))))

-- Source: PhysLean (StandardModel.GaugeGroupQuot.ℤ₆.sizeOf_spec)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupquot_ℤ₆_sizeof_spec : Eq (StandardModel.GaugeGroupQuot._sizeOf_inst.sizeOf StandardModel.GaugeGroupQuot.ℤ₆) 1

-- Source: PhysLean (Fermion.altLeftMetricVal)
-- [complex signature, not re-axiomatized]
-- fermion_altleftmetricval : (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.altLeftHanded).V.carrier

-- Source: PhysLean (StandardModel.HiggsField.Potential.𝓵)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_𝓵 : StandardModel.HiggsField.Potential → Real

-- Source: PhysLean (Fermion.altLeftAltRightToMatrix_ρ_symm)
-- [complex signature, not re-axiomatized]
-- fermion_altleftaltrighttomatrix_ρ_symm : ∀ (v : Matrix (Fin 2) (Fin 2) Complex) (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (LinearMap.instFunLike.coe
--       (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.altLeftHanded.ρ M)
--         (MonoidHom.instFunLike.coe Fermion.altRightHanded.ρ M))
--       (EquivLike.toFunLike.coe Fermion.altLeftAltRightToMatrix.symm v))
--     (EquivLike.toFunLike.coe Fermion.altLeftAltRightToMatrix.symm
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--         (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.inv.inv M.val).transpose v)
--         (Matrix.inv.inv M.val).conjTranspose.transpose))

-- Source: PhysLean (Fermion.leftMetric)
-- [complex signature, not re-axiomatized]
-- fermion_leftmetric : Action.instCategory.Hom
--   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--   (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.leftHanded)

-- Source: PhysLean (Fermion.leftAltContraction_apply_metric)
-- [complex signature, not re-axiomatized]
-- fermion_leftaltcontraction_apply_metric : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded).V
--         (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--       ((Action.instBraidedCategory (ModuleCat Complex) (Matrix.SpecialLinearGroup (Fin 2) Complex)).braiding
--             Fermion.leftHanded Fermion.altLeftHanded).hom.hom)
--     (((fun X Y => LinearMap.instFunLike)
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.leftHanded.V
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorUnit (ModuleCat Complex))
--               Fermion.altLeftHanded.V))
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.leftHanded.V
--             Fermion.altLeftHanded.V)).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--         (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft Fermion.leftHanded.V
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.leftUnitor Fermion.altLeftHanded.V).hom))
--       (((fun X Y => LinearMap.instFunLike)
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.leftHanded.V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                 (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded).V
--                 Fermion.altLeftHanded.V))
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.leftHanded.V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                 (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                 Fermion.altLeftHanded.V))).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft Fermion.leftHanded.V
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerRight Fermion.leftAltContraction.hom
--               Fermion.altLeftHanded.V)))
--         (((fun X Y => LinearMap.instFunLike)
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.leftHanded.V
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.leftHanded.V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altLeftHanded.V
--                     Fermion.altLeftHanded.V)))
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.leftHanded.V
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.leftHanded.V
--                     Fermion.altLeftHanded.V)
--                   Fermion.altLeftHanded.V))).coe
--           ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft Fermion.leftHanded.V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.associator Fermion.leftHanded.V
--                   Fermion.altLeftHanded.V Fermion.altLeftHanded.V).inv))
--           (((fun X Y => LinearMap.instFunLike)
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.leftHanded.V
--                     Fermion.leftHanded.V)
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altLeftHanded.V
--                     Fermion.altLeftHanded.V))
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.leftHanded.V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.leftHanded.V
--                     (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altLeftHanded.V
--                       Fermion.altLeftHanded.V)))).coe
--             ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.associator Fermion.leftHanded.V
--                   Fermion.leftHanded.V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altLeftHanded.V
--                     Fermion.altLeftHanded.V)).hom)
--             (TensorProduct.tmul Complex
--               (((fun X Y => LinearMap.instFunLike)
--                     (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                     (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.leftHanded).V).coe
--                 ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.leftMetric.hom) 1)
--               (((fun X Y => LinearMap.instFunLike)
--                     (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                     (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.altLeftHanded).V).coe
--                 ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altLeftMetric.hom) 1)))))))
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altLeftLeftUnit.hom) 1)

-- Source: PhysLean (Fermion.altRightRightUnitVal.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_altrightrightunitval_eq_1 : Eq Fermion.altRightRightUnitVal (EquivLike.toFunLike.coe Fermion.altRightRightToMatrix.symm 1)

-- Source: PhysLean (Fermion.altRightRightUnitVal_expand_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_altrightrightunitval_expand_tmul : Eq Fermion.altRightRightUnitVal
--   (instHAdd.hAdd
--     (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altRightBasis 0)
--       (Module.Basis.instFunLike.coe Fermion.rightBasis 0))
--     (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altRightBasis 1)
--       (Module.Basis.instFunLike.coe Fermion.rightBasis 1)))

-- Source: PhysLean (Fermion.leftRightToMatrix.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_leftrighttomatrix_eq_1 : Eq Fermion.leftRightToMatrix
--   (((Fermion.leftBasis.tensorProduct Fermion.rightBasis).repr.trans
--         (Finsupp.linearEquivFunOnFinite Complex Complex (Prod (Fin 2) (Fin 2)))).trans
--     (LinearEquiv.curry Complex Complex (Fin 2) (Fin 2)))

-- Source: PhysLean (Fermion.LeftHandedModule.toFin2ℂEquiv_symm_apply_val)
-- [complex signature, not re-axiomatized]
-- fermion_lefthandedmodule_tofin2ℂequiv_symm_apply_val : ∀ (a : Fin 2 → Complex) (a_1 : Fin 2),
--   Eq ((EquivLike.toFunLike.coe Fermion.LeftHandedModule.toFin2ℂEquiv.symm a).val a_1) (a a_1)

-- Source: PhysLean (Fermion.altRightAltRightToMatrix_ρ)
-- [complex signature, not re-axiomatized]
-- fermion_altrightaltrighttomatrix_ρ : ∀ (v : (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.altRightHanded).V.carrier)
--   (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (EquivLike.toFunLike.coe Fermion.altRightAltRightToMatrix
--       (LinearMap.instFunLike.coe
--         (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.altRightHanded.ρ M)
--           (MonoidHom.instFunLike.coe Fermion.altRightHanded.ρ M))
--         v))
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.inv.inv M.val).conjTranspose
--         (EquivLike.toFunLike.coe Fermion.altRightAltRightToMatrix v))
--       (Matrix.inv.inv M.val).conjTranspose.transpose)

-- Source: PhysLean (Fermion.leftAltLeftToMatrix_symm_expand_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_leftaltlefttomatrix_symm_expand_tmul : ∀ (M : Matrix (Fin 2) (Fin 2) Complex),
--   Eq (EquivLike.toFunLike.coe Fermion.leftAltLeftToMatrix.symm M)
--     (Finset.univ.sum fun i =>
--       Finset.univ.sum fun j =>
--         instHSMul.hSMul (M i j)
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.leftBasis i)
--             (Module.Basis.instFunLike.coe Fermion.altLeftBasis j)))

-- Source: PhysLean (StandardModel.HiggsField.inner_eq_expand)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_inner_eq_expand : ∀ (φ1 φ2 : StandardModel.HiggsField),
--   Eq (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex.inner (SpaceTime → Complex) φ1 φ2) fun x =>
--     EquivLike.toFunLike.coe Complex.equivRealProdCLM.symm
--       {
--         fst :=
--           instHAdd.hAdd
--             (instHAdd.hAdd
--               (instHAdd.hAdd
--                 (instHMul.hMul ((ContMDiffSection.instDFunLike.coe φ1 x).ofLp 0).re
--                   ((ContMDiffSection.instDFunLike.coe φ2 x).ofLp 0).re)
--                 (instHMul.hMul ((ContMDiffSection.instDFunLike.coe φ1 x).ofLp 1).re
--                   ((ContMDiffSection.instDFunLike.coe φ2 x).ofLp 1).re))
--               (instHMul.hMul ((ContMDiffSection.instDFunLike.coe φ1 x).ofLp 0).im
--                 ((ContMDiffSection.instDFunLike.coe φ2 x).ofLp 0).im))
--             (instHMul.hMul ((ContMDiffSection.instDFunLike.coe φ1 x).ofLp 1).im
--               ((ContMDiffSection.instDFunLike.coe φ2 x).ofLp 1).im),
--         snd :=
--           instHSub.hSub
--             (instHSub.hSub
--               (instHAdd.hAdd
--                 (instHMul.hMul ((ContMDiffSection.instDFunLike.coe φ1 x).ofLp 0).re
--                   ((ContMDiffSection.instDFunLike.coe φ2 x).ofLp 0).im)
--                 (instHMul.hMul ((ContMDiffSection.instDFunLike.coe φ1 x).ofLp 1).re
--                   ((ContMDiffSection.instDFunLike.coe φ2 x).ofLp 1).im))
--               (instHMul.hMul ((ContMDiffSection.instDFunLike.coe φ1 x).ofLp 0).im
--                 ((ContMDiffSection.instDFunLike.coe φ2 x).ofLp 0).re))
--             (instHMul.hMul ((ContMDiffSection.instDFunLike.coe φ1 x).ofLp 1).im
--               ((ContMDiffSection.instDFunLike.coe φ2 x).ofLp 1).re) }

-- Source: PhysLean (StandardModel.HiggsField.inner_expand_conj)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_inner_expand_conj : ∀ (φ1 φ2 : StandardModel.HiggsField) (x : SpaceTime),
--   Eq (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex.inner (SpaceTime → Complex) φ1 φ2 x)
--     (instHAdd.hAdd
--       (instHMul.hMul
--         (RingHom.instFunLike.coe (starRingEnd ((fun x => Complex) 0)) ((ContMDiffSection.instDFunLike.coe φ1 x).ofLp 0))
--         ((ContMDiffSection.instDFunLike.coe φ2 x).ofLp 0))
--       (instHMul.hMul
--         (RingHom.instFunLike.coe (starRingEnd ((fun x => Complex) 1)) ((ContMDiffSection.instDFunLike.coe φ1 x).ofLp 1))
--         ((ContMDiffSection.instDFunLike.coe φ2 x).ofLp 1)))

-- Source: PhysLean (StandardModel.HiggsField.contDiff)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_contdiff : ∀ (φ : StandardModel.HiggsField), ContDiff Real WithTop.top.top (ContMDiffSection.instDFunLike.coe φ)

-- Source: PhysLean (Fermion.AltLeftHandedModule.toFin2ℂFun)
-- [complex signature, not re-axiomatized]
-- fermion_altlefthandedmodule_tofin2ℂfun : Equiv Fermion.AltLeftHandedModule (Fin 2 → Complex)

-- Source: PhysLean (Fermion.rightRightToMatrix_ρ)
-- [complex signature, not re-axiomatized]
-- fermion_rightrighttomatrix_ρ : ∀ (v : (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.rightHanded).V.carrier)
--   (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (EquivLike.toFunLike.coe Fermion.rightRightToMatrix
--       (LinearMap.instFunLike.coe
--         (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.rightHanded.ρ M)
--           (MonoidHom.instFunLike.coe Fermion.rightHanded.ρ M))
--         v))
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (M.val.map StarRing.toStarAddMonoid.star)
--         (EquivLike.toFunLike.coe Fermion.rightRightToMatrix v))
--       (M.val.map StarRing.toStarAddMonoid.star).transpose)

-- Source: PhysLean (Fermion.leftAltLeftUnit_symm)
-- [complex signature, not re-axiomatized]
-- fermion_leftaltleftunit_symm : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.leftAltLeftUnit.hom) 1)
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded).V
--         (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--       (Action.instMonoidalCategory.whiskerLeft Fermion.leftHanded (Action.instCategory.id Fermion.altLeftHanded)).hom)
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded).V
--           (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--         ((Action.instBraidedCategory (ModuleCat Complex) (Matrix.SpecialLinearGroup (Fin 2) Complex)).braiding
--               Fermion.altLeftHanded Fermion.leftHanded).hom.hom)
--       (((fun X Y => LinearMap.instFunLike)
--             (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--             (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded).V).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altLeftLeftUnit.hom) 1)))

-- Source: PhysLean (Fermion.leftAltLeftToMatrix_ρ_symm)
-- [complex signature, not re-axiomatized]
-- fermion_leftaltlefttomatrix_ρ_symm : ∀ (v : Matrix (Fin 2) (Fin 2) Complex) (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (LinearMap.instFunLike.coe
--       (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.leftHanded.ρ M)
--         (MonoidHom.instFunLike.coe Fermion.altLeftHanded.ρ M))
--       (EquivLike.toFunLike.coe Fermion.leftAltLeftToMatrix.symm v))
--     (EquivLike.toFunLike.coe Fermion.leftAltLeftToMatrix.symm
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul M.val v)
--         (Matrix.inv.inv M.val)))

-- Source: PhysLean (Fermion.altLeftContraction_tmul_symm)
-- [complex signature, not re-axiomatized]
-- fermion_altleftcontraction_tmul_symm : ∀ (φ : Fermion.altLeftHanded.V.carrier) (ψ : Fermion.leftHanded.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altLeftContraction.hom)
--       (TensorProduct.tmul Complex φ ψ))
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.leftAltContraction.hom)
--       (TensorProduct.tmul Complex ψ φ))

-- Source: PhysLean (StandardModel.GaugeGroupQuot.ℤ₆.elim)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupquot_ℤ₆_elim : {motive : StandardModel.GaugeGroupQuot → Sort u} →
--   (t : StandardModel.GaugeGroupQuot) → Eq t.ctorIdx 0 → motive StandardModel.GaugeGroupQuot.ℤ₆ → motive t

-- Source: PhysLean (Fermion.altRightRightUnit)
-- [complex signature, not re-axiomatized]
-- fermion_altrightrightunit : Action.instCategory.Hom
--   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--   (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded)

-- Source: PhysLean (Fermion.leftHandedAltEquiv)
-- [complex signature, not re-axiomatized]
-- fermion_lefthandedaltequiv : CategoryTheory.Iso Fermion.leftHanded Fermion.altLeftHanded

-- Source: PhysLean (StandardModel.GaugeGroupQuot.ℤ₃.elim)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupquot_ℤ₃_elim : {motive : StandardModel.GaugeGroupQuot → Sort u} →
--   (t : StandardModel.GaugeGroupQuot) → Eq t.ctorIdx 2 → motive StandardModel.GaugeGroupQuot.ℤ₃ → motive t

-- Source: PhysLean (Fermion.leftLeftToMatrix_symm_expand_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_leftlefttomatrix_symm_expand_tmul : ∀ (M : Matrix (Fin 2) (Fin 2) Complex),
--   Eq (EquivLike.toFunLike.coe Fermion.leftLeftToMatrix.symm M)
--     (Finset.univ.sum fun i =>
--       Finset.univ.sum fun j =>
--         instHSMul.hSMul (M i j)
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.leftBasis i)
--             (Module.Basis.instFunLike.coe Fermion.leftBasis j)))

-- Source: PhysLean (StandardModel.HiggsField.Potential.quadDiscrim_eq_zero_iff)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_quaddiscrim_eq_zero_iff : ∀ (P : StandardModel.HiggsField.Potential),
--   Ne P.𝓵 0 →
--     ∀ (φ : StandardModel.HiggsField) (x : SpaceTime),
--       Iff (Eq (P.quadDiscrim φ x) 0)
--         (Eq (P.toFun φ x) (instHDiv.hDiv (Real.instNeg.neg (instHPow.hPow P.μ2 2)) (instHMul.hMul 4 P.𝓵)))

-- Source: PhysLean (Fermion.altLeftaltLeftToMatrix_symm_expand_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_altleftaltlefttomatrix_symm_expand_tmul : ∀ (M : Matrix (Fin 2) (Fin 2) Complex),
--   Eq (EquivLike.toFunLike.coe Fermion.altLeftaltLeftToMatrix.symm M)
--     (Finset.univ.sum fun i =>
--       Finset.univ.sum fun j =>
--         instHSMul.hSMul (M i j)
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altLeftBasis i)
--             (Module.Basis.instFunLike.coe Fermion.altLeftBasis j)))

-- Source: PhysLean (Fermion.leftHandedAltEquiv_hom_hom_apply)
-- [complex signature, not re-axiomatized]
-- fermion_lefthandedaltequiv_hom_hom_apply : ∀ (ψ : Fermion.leftHanded.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike) Fermion.leftHanded.V Fermion.altLeftHanded.V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.leftHandedAltEquiv.hom.hom) ψ)
--     (EquivLike.toFunLike.coe Fermion.AltLeftHandedModule.toFin2ℂEquiv.symm
--       ((EquivLike.toFunLike.coe Matrix.of
--             (Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons 1 Matrix.vecEmpty))
--               (Matrix.vecCons (Matrix.vecCons (-1) (Matrix.vecCons 0 Matrix.vecEmpty)) Matrix.vecEmpty))).mulVec
--         (Fermion.LeftHandedModule.toFin2ℂ ψ)))

-- Source: PhysLean (Fermion.altLeftContraction_basis)
-- [complex signature, not re-axiomatized]
-- fermion_altleftcontraction_basis : ∀ (i j : Fin 2),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altLeftContraction.hom)
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altLeftBasis i)
--         (Module.Basis.instFunLike.coe Fermion.leftBasis j)))
--     (ite (Eq i.val j.val) 1 0)

-- Source: PhysLean (Fermion.altRightBasis_toFin2ℂ)
-- [complex signature, not re-axiomatized]
-- fermion_altrightbasis_tofin2ℂ : ∀ (i : Fin 2),
--   Eq (Fermion.AltRightHandedModule.toFin2ℂ (Module.Basis.instFunLike.coe Fermion.altRightBasis i)) (Pi.single i 1)

-- Source: PhysLean (Fermion.altLeftLeftUnitVal.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_altleftleftunitval_eq_1 : Eq Fermion.altLeftLeftUnitVal (EquivLike.toFunLike.coe Fermion.altLeftLeftToMatrix.symm 1)

-- Source: PhysLean (Fermion.rightBasis)
-- [complex signature, not re-axiomatized]
-- fermion_rightbasis : Module.Basis (Fin 2) Complex Fermion.rightHanded.V.carrier

-- Source: PhysLean (Fermion.leftAltLeftToMatrix)
-- [complex signature, not re-axiomatized]
-- fermion_leftaltlefttomatrix : LinearEquiv (RingHom.id Complex)
--   (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded).V.carrier
--   (Matrix (Fin 2) (Fin 2) Complex)

-- Source: PhysLean (Fermion.altRightRightToMatrix.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_altrightrighttomatrix_eq_1 : Eq Fermion.altRightRightToMatrix
--   (((Fermion.altRightBasis.tensorProduct Fermion.rightBasis).repr.trans
--         (Finsupp.linearEquivFunOnFinite Complex Complex (Prod (Fin 2) (Fin 2)))).trans
--     (LinearEquiv.curry Complex Complex (Fin 2) (Fin 2)))

-- Source: PhysLean (Fermion.leftAltLeftToMatrix_ρ)
-- [complex signature, not re-axiomatized]
-- fermion_leftaltlefttomatrix_ρ : ∀ (v : (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded).V.carrier)
--   (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (EquivLike.toFunLike.coe Fermion.leftAltLeftToMatrix
--       (LinearMap.instFunLike.coe
--         (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.leftHanded.ρ M)
--           (MonoidHom.instFunLike.coe Fermion.altLeftHanded.ρ M))
--         v))
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul M.val (EquivLike.toFunLike.coe Fermion.leftAltLeftToMatrix v))
--       (Matrix.inv.inv M.val))

-- Source: PhysLean (Fermion.rightHanded)
/-- The vector space ℂ^2 carrying the conjugate representation of SL(2,C).
In index notation corresponds to a Weyl fermion with indices ψ^{dot a}.  -/
axiom fermion_righthanded :
  Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)

-- Source: PhysLean (Fermion.RightHandedModule.toFin2ℂFun)
-- [complex signature, not re-axiomatized]
-- fermion_righthandedmodule_tofin2ℂfun : Equiv Fermion.RightHandedModule (Fin 2 → Complex)

-- Source: PhysLean (StandardModel.HiggsField.Potential.complete_square)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_complete_square : ∀ (P : StandardModel.HiggsField.Potential),
--   Ne P.𝓵 0 →
--     ∀ (φ : StandardModel.HiggsField) (x : SpaceTime),
--       Eq (P.toFun φ x)
--         (instHSub.hSub
--           (instHMul.hMul P.𝓵 (instHPow.hPow (instHSub.hSub (φ.normSq x) (instHDiv.hDiv P.μ2 (instHMul.hMul 2 P.𝓵))) 2))
--           (instHDiv.hDiv (instHPow.hPow P.μ2 2) (instHMul.hMul 4 P.𝓵)))

-- Source: PhysLean (StandardModel.GaugeGroupI.toU1)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupi_tou1 : MonoidHom StandardModel.GaugeGroupI (Subtype fun x => SetLike.instMembership.mem (unitary Complex) x)

-- Source: PhysLean (StandardModel.HiggsField.normSq_zero)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_normsq_zero : Eq (StandardModel.HiggsField.normSq 0) 0

-- Source: PhysLean (Fermion.LeftHandedModule.toFin2ℂEquiv_apply)
-- [complex signature, not re-axiomatized]
-- fermion_lefthandedmodule_tofin2ℂequiv_apply : ∀ (a : Fermion.LeftHandedModule) (a_1 : Fin 2),
--   Eq (EquivLike.toFunLike.coe Fermion.LeftHandedModule.toFin2ℂEquiv a a_1)
--     (EquivLike.toFunLike.coe Fermion.LeftHandedModule.toFin2ℂFun a a_1)

-- Source: PhysLean (Fermion.altRightBasis_ρ_apply)
-- [complex signature, not re-axiomatized]
-- fermion_altrightbasis_ρ_apply : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex) (i j : Fin 2),
--   Eq
--     (EquivLike.toFunLike.coe (LinearMap.toMatrix Fermion.altRightBasis Fermion.altRightBasis)
--       (MonoidHom.instFunLike.coe Fermion.altRightHanded.ρ M) i j)
--     ((Matrix.inv.inv M.val).conjTranspose i j)

-- Source: PhysLean (Fermion.altLeftAltRightToMatrix)
-- [complex signature, not re-axiomatized]
-- fermion_altleftaltrighttomatrix : LinearEquiv (RingHom.id Complex)
--   (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.altRightHanded).V.carrier
--   (Matrix (Fin 2) (Fin 2) Complex)

-- Source: PhysLean (Fermion.altRightMetricVal)
-- [complex signature, not re-axiomatized]
-- fermion_altrightmetricval : (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.altRightHanded).V.carrier

-- Source: PhysLean (StandardModel.HiggsField.Potential.isBounded_iff_of_𝓵_zero)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_isbounded_iff_of_𝓵_zero : InformalLemma

-- Source: PhysLean (StandardModel.HiggsField.normSq_eq_inner_self_re)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_normsq_eq_inner_self_re : ∀ (φ : StandardModel.HiggsField) (x : SpaceTime),
--   Eq (φ.normSq x)
--     (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex.inner (SpaceTime → Complex) φ φ x).re

-- Source: PhysLean (StandardModel.HiggsField.Potential.quadDiscrim_nonneg)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_quaddiscrim_nonneg : ∀ (P : StandardModel.HiggsField.Potential),
--   Ne P.𝓵 0 → ∀ (φ : StandardModel.HiggsField) (x : SpaceTime), Real.instLE.le 0 (P.quadDiscrim φ x)

-- Source: PhysLean (StandardModel.HiggsField.toVec_smooth)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_tovec_smooth : ∀ (φ : StandardModel.HiggsField),
--   ContMDiff (modelWithCornersSelf Real SpaceTime) (modelWithCornersSelf Real (EuclideanSpace Complex (Fin 2)))
--     WithTop.top.top (ContMDiffSection.instDFunLike.coe φ)

-- Source: PhysLean (Fermion.RightHandedModule.instModuleComplex)
-- [complex signature, not re-axiomatized]
-- fermion_righthandedmodule_instmodulecomplex : Module Complex Fermion.RightHandedModule

-- Source: PhysLean (Fermion.leftHanded)
/-- The vector space ℂ^2 carrying the fundamental representation of SL(2,C).
In index notation corresponds to a Weyl fermion with indices ψ^a.  -/
axiom fermion_lefthanded :
  Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)

-- Source: PhysLean (StandardModel.GaugeGroupQuot.ctorIdx)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupquot_ctoridx : StandardModel.GaugeGroupQuot → Nat

-- Source: PhysLean (Fermion.rightAltRightUnit_symm)
-- [complex signature, not re-axiomatized]
-- fermion_rightaltrightunit_symm : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.rightAltRightUnit.hom) 1)
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded).V
--         (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--       (Action.instMonoidalCategory.whiskerLeft Fermion.rightHanded (Action.instCategory.id Fermion.altRightHanded)).hom)
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded).V
--           (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--         ((Action.instBraidedCategory (ModuleCat Complex) (Matrix.SpecialLinearGroup (Fin 2) Complex)).braiding
--               Fermion.altRightHanded Fermion.rightHanded).hom.hom)
--       (((fun X Y => LinearMap.instFunLike)
--             (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--             (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded).V).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altRightRightUnit.hom) 1)))

-- Source: PhysLean (Fermion.altLeftLeftToMatrix.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_altleftlefttomatrix_eq_1 : Eq Fermion.altLeftLeftToMatrix
--   (((Fermion.altLeftBasis.tensorProduct Fermion.leftBasis).repr.trans
--         (Finsupp.linearEquivFunOnFinite Complex Complex (Prod (Fin 2) (Fin 2)))).trans
--     (LinearEquiv.curry Complex Complex (Fin 2) (Fin 2)))

-- Source: PhysLean (Fermion.altRightAltRightToMatrix_symm_expand_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_altrightaltrighttomatrix_symm_expand_tmul : ∀ (M : Matrix (Fin 2) (Fin 2) Complex),
--   Eq (EquivLike.toFunLike.coe Fermion.altRightAltRightToMatrix.symm M)
--     (Finset.univ.sum fun i =>
--       Finset.univ.sum fun j =>
--         instHSMul.hSMul (M i j)
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altRightBasis i)
--             (Module.Basis.instFunLike.coe Fermion.altRightBasis j)))

-- Source: PhysLean (StandardModel.HiggsField.Potential.isMinOn_iff_field_of_μSq_nonneg_𝓵_pos)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_isminon_iff_field_of_μsq_nonneg_𝓵_pos : ∀ (P : StandardModel.HiggsField.Potential),
--   Real.instLT.lt 0 P.𝓵 →
--     Real.instLE.le 0 P.μ2 →
--       ∀ (φ : StandardModel.HiggsField) (x : SpaceTime),
--         Iff
--           (IsMinOn
--             (fun x =>
--               StandardModel.HiggsField.Potential.isMinOn_iff_of_μSq_nonpos_𝓵_pos.match_1 (fun x => Real) x fun φ x =>
--                 P.toFun φ x)
--             Set.univ { fst := φ, snd := x })
--           (Eq (φ.normSq x) (instHDiv.hDiv P.μ2 (instHMul.hMul 2 P.𝓵)))

-- Source: PhysLean (StandardModel.HiggsField.Potential.IsBounded.eq_1)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_isbounded_eq_1 : ∀ (P : StandardModel.HiggsField.Potential),
--   Eq P.IsBounded (Exists fun c => ∀ (Φ : StandardModel.HiggsField) (x : SpaceTime), Real.instLE.le c (P.toFun Φ x))

-- Source: PhysLean (Fermion.LeftHandedModule.instAddCommMonoid)
-- [complex signature, not re-axiomatized]
-- fermion_lefthandedmodule_instaddcommmonoid : AddCommMonoid Fermion.LeftHandedModule

-- Source: PhysLean (StandardModel.HiggsVec.smooth_toFin2ℂ)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsvec_smooth_tofin2ℂ : ContMDiff (modelWithCornersSelf Real StandardModel.HiggsVec) (modelWithCornersSelf Real (Fin 2 → Complex))
--   WithTop.top.top (ContinuousLinearMap.funLike.coe StandardModel.HiggsVec.toFin2ℂ)

-- Source: PhysLean (StandardModel.HiggsField.«term‖_‖_H^2»)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_«term‖_‖_h^2» : Lean.ParserDescr

-- Source: PhysLean (Fermion.altRightBasis)
-- [complex signature, not re-axiomatized]
-- fermion_altrightbasis : Module.Basis (Fin 2) Complex Fermion.altRightHanded.V.carrier

-- Source: PhysLean (Fermion.altLeftLeftUnit_symm)
-- [complex signature, not re-axiomatized]
-- fermion_altleftleftunit_symm : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altLeftLeftUnit.hom) 1)
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded).V
--         (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--       (Action.instMonoidalCategory.whiskerLeft Fermion.altLeftHanded (Action.instCategory.id Fermion.leftHanded)).hom)
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded).V
--           (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--         ((Action.instBraidedCategory (ModuleCat Complex) (Matrix.SpecialLinearGroup (Fin 2) Complex)).braiding
--               Fermion.leftHanded Fermion.altLeftHanded).hom.hom)
--       (((fun X Y => LinearMap.instFunLike)
--             (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--             (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded).V).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.leftAltLeftUnit.hom) 1)))

-- Source: PhysLean (Fermion.AltRightHandedModule.toFin2ℂEquiv_symm_apply_val)
-- [complex signature, not re-axiomatized]
-- fermion_altrighthandedmodule_tofin2ℂequiv_symm_apply_val : ∀ (a : Fin 2 → Complex) (a_1 : Fin 2),
--   Eq ((EquivLike.toFunLike.coe Fermion.AltRightHandedModule.toFin2ℂEquiv.symm a).val a_1) (a a_1)

-- Source: PhysLean (StandardModel.GaugeGroupQuot.ℤ₂.elim)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupquot_ℤ₂_elim : {motive : StandardModel.GaugeGroupQuot → Sort u} →
--   (t : StandardModel.GaugeGroupQuot) → Eq t.ctorIdx 1 → motive StandardModel.GaugeGroupQuot.ℤ₂ → motive t

-- Source: PhysLean (Fermion.rightAltContraction_apply_metric)
-- [complex signature, not re-axiomatized]
-- fermion_rightaltcontraction_apply_metric : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded).V
--         (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--       ((Action.instBraidedCategory (ModuleCat Complex) (Matrix.SpecialLinearGroup (Fin 2) Complex)).braiding
--             Fermion.rightHanded Fermion.altRightHanded).hom.hom)
--     (((fun X Y => LinearMap.instFunLike)
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.rightHanded.V
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorUnit (ModuleCat Complex))
--               Fermion.altRightHanded.V))
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.rightHanded.V
--             Fermion.altRightHanded.V)).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--         (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft Fermion.rightHanded.V
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.leftUnitor Fermion.altRightHanded.V).hom))
--       (((fun X Y => LinearMap.instFunLike)
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.rightHanded.V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                 (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded).V
--                 Fermion.altRightHanded.V))
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.rightHanded.V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                 (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                 Fermion.altRightHanded.V))).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft Fermion.rightHanded.V
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerRight Fermion.rightAltContraction.hom
--               Fermion.altRightHanded.V)))
--         (((fun X Y => LinearMap.instFunLike)
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.rightHanded.V
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.rightHanded.V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altRightHanded.V
--                     Fermion.altRightHanded.V)))
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.rightHanded.V
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.rightHanded.V
--                     Fermion.altRightHanded.V)
--                   Fermion.altRightHanded.V))).coe
--           ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft Fermion.rightHanded.V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.associator Fermion.rightHanded.V
--                   Fermion.altRightHanded.V Fermion.altRightHanded.V).inv))
--           (((fun X Y => LinearMap.instFunLike)
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.rightHanded.V
--                     Fermion.rightHanded.V)
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altRightHanded.V
--                     Fermion.altRightHanded.V))
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.rightHanded.V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.rightHanded.V
--                     (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altRightHanded.V
--                       Fermion.altRightHanded.V)))).coe
--             ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.associator Fermion.rightHanded.V
--                   Fermion.rightHanded.V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altRightHanded.V
--                     Fermion.altRightHanded.V)).hom)
--             (TensorProduct.tmul Complex
--               (((fun X Y => LinearMap.instFunLike)
--                     (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                     (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.rightHanded).V).coe
--                 ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.rightMetric.hom) 1)
--               (((fun X Y => LinearMap.instFunLike)
--                     (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                     (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.altRightHanded).V).coe
--                 ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altRightMetric.hom) 1)))))))
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altRightRightUnit.hom) 1)

-- Source: PhysLean (Fermion.rightAltRightUnit)
-- [complex signature, not re-axiomatized]
-- fermion_rightaltrightunit : Action.instCategory.Hom
--   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--   (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded)

-- Source: PhysLean (StandardModel.HiggsField.normSq)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_normsq : StandardModel.HiggsField → SpaceTime → Real

-- Source: PhysLean (Fermion.altRightContraction_apply_metric)
-- [complex signature, not re-axiomatized]
-- fermion_altrightcontraction_apply_metric : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded).V
--         (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--       ((Action.instBraidedCategory (ModuleCat Complex) (Matrix.SpecialLinearGroup (Fin 2) Complex)).braiding
--             Fermion.altRightHanded Fermion.rightHanded).hom.hom)
--     (((fun X Y => LinearMap.instFunLike)
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altRightHanded.V
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorUnit (ModuleCat Complex))
--               Fermion.rightHanded.V))
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altRightHanded.V
--             Fermion.rightHanded.V)).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--         (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft Fermion.altRightHanded.V
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.leftUnitor Fermion.rightHanded.V).hom))
--       (((fun X Y => LinearMap.instFunLike)
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altRightHanded.V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                 (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded).V
--                 Fermion.rightHanded.V))
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altRightHanded.V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                 (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                 Fermion.rightHanded.V))).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft Fermion.altRightHanded.V
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerRight Fermion.altRightContraction.hom
--               Fermion.rightHanded.V)))
--         (((fun X Y => LinearMap.instFunLike)
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altRightHanded.V
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altRightHanded.V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.rightHanded.V
--                     Fermion.rightHanded.V)))
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altRightHanded.V
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altRightHanded.V
--                     Fermion.rightHanded.V)
--                   Fermion.rightHanded.V))).coe
--           ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft Fermion.altRightHanded.V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.associator Fermion.altRightHanded.V
--                   Fermion.rightHanded.V Fermion.rightHanded.V).inv))
--           (((fun X Y => LinearMap.instFunLike)
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altRightHanded.V
--                     Fermion.altRightHanded.V)
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.rightHanded.V
--                     Fermion.rightHanded.V))
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altRightHanded.V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altRightHanded.V
--                     (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.rightHanded.V
--                       Fermion.rightHanded.V)))).coe
--             ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.associator Fermion.altRightHanded.V
--                   Fermion.altRightHanded.V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.rightHanded.V
--                     Fermion.rightHanded.V)).hom)
--             (TensorProduct.tmul Complex
--               (((fun X Y => LinearMap.instFunLike)
--                     (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                     (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.altRightHanded).V).coe
--                 ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altRightMetric.hom) 1)
--               (((fun X Y => LinearMap.instFunLike)
--                     (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                     (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.rightHanded).V).coe
--                 ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.rightMetric.hom) 1)))))))
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.rightAltRightUnit.hom) 1)

-- Source: PhysLean (StandardModel.HiggsField.Potential.quadDiscrim.eq_1)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_quaddiscrim_eq_1 : ∀ (P : StandardModel.HiggsField.Potential) (φ : StandardModel.HiggsField) (x : SpaceTime),
--   Eq (P.quadDiscrim φ x) (discrim P.𝓵 (Real.instNeg.neg P.μ2) (Real.instNeg.neg (P.toFun φ x)))

-- Source: PhysLean (Fermion.altLeftLeftUnit)
-- [complex signature, not re-axiomatized]
-- fermion_altleftleftunit : Action.instCategory.Hom
--   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--   (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded)

-- Source: PhysLean (Fermion.RightHandedModule.instAddCommMonoid)
-- [complex signature, not re-axiomatized]
-- fermion_righthandedmodule_instaddcommmonoid : AddCommMonoid Fermion.RightHandedModule

-- Source: PhysLean (Fermion.AltRightHandedModule.ctorIdx)
-- [complex signature, not re-axiomatized]
-- fermion_altrighthandedmodule_ctoridx : Fermion.AltRightHandedModule → Nat

-- Source: PhysLean (Fermion.altLeftContraction_apply_metric)
-- [complex signature, not re-axiomatized]
-- fermion_altleftcontraction_apply_metric : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded).V
--         (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--       ((Action.instBraidedCategory (ModuleCat Complex) (Matrix.SpecialLinearGroup (Fin 2) Complex)).braiding
--             Fermion.altLeftHanded Fermion.leftHanded).hom.hom)
--     (((fun X Y => LinearMap.instFunLike)
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altLeftHanded.V
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorUnit (ModuleCat Complex))
--               Fermion.leftHanded.V))
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altLeftHanded.V
--             Fermion.leftHanded.V)).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--         (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft Fermion.altLeftHanded.V
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.leftUnitor Fermion.leftHanded.V).hom))
--       (((fun X Y => LinearMap.instFunLike)
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altLeftHanded.V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                 (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded).V
--                 Fermion.leftHanded.V))
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altLeftHanded.V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                 (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                 Fermion.leftHanded.V))).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--           (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft Fermion.altLeftHanded.V
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerRight Fermion.altLeftContraction.hom
--               Fermion.leftHanded.V)))
--         (((fun X Y => LinearMap.instFunLike)
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altLeftHanded.V
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altLeftHanded.V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.leftHanded.V
--                     Fermion.leftHanded.V)))
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altLeftHanded.V
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altLeftHanded.V
--                     Fermion.leftHanded.V)
--                   Fermion.leftHanded.V))).coe
--           ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--             (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.whiskerLeft Fermion.altLeftHanded.V
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.associator Fermion.altLeftHanded.V
--                   Fermion.leftHanded.V Fermion.leftHanded.V).inv))
--           (((fun X Y => LinearMap.instFunLike)
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altLeftHanded.V
--                     Fermion.altLeftHanded.V)
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.leftHanded.V
--                     Fermion.leftHanded.V))
--                 (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altLeftHanded.V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.altLeftHanded.V
--                     (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.leftHanded.V
--                       Fermion.leftHanded.V)))).coe
--             ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--               (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.associator Fermion.altLeftHanded.V
--                   Fermion.altLeftHanded.V
--                   (ModuleCat.MonoidalCategory.instMonoidalCategoryStruct.tensorObj Fermion.leftHanded.V
--                     Fermion.leftHanded.V)).hom)
--             (TensorProduct.tmul Complex
--               (((fun X Y => LinearMap.instFunLike)
--                     (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                     (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.altLeftHanded).V).coe
--                 ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altLeftMetric.hom) 1)
--               (((fun X Y => LinearMap.instFunLike)
--                     (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                     (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.leftHanded).V).coe
--                 ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.leftMetric.hom) 1)))))))
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.leftAltLeftUnit.hom) 1)

-- Source: PhysLean (Fermion.altLeftAltRightToMatrix_ρ_symm_selfAdjoint)
-- [complex signature, not re-axiomatized]
-- fermion_altleftaltrighttomatrix_ρ_symm_selfadjoint : ∀ (v : Matrix (Fin 2) (Fin 2) Complex) (hv : IsSelfAdjoint v) (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (LinearMap.instFunLike.coe
--       (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.altLeftHanded.ρ M)
--         (MonoidHom.instFunLike.coe Fermion.altRightHanded.ρ M))
--       (EquivLike.toFunLike.coe Fermion.altLeftAltRightToMatrix.symm v))
--     (EquivLike.toFunLike.coe Fermion.altLeftAltRightToMatrix.symm
--       (LinearMap.instFunLike.coe (Lorentz.SL2C.toSelfAdjointMap (Matrix.SpecialLinearGroup.hasInv.inv M.transpose))
--           ⟨v, hv⟩).val)

-- Source: PhysLean (StandardModel.HiggsField.Potential.toFun.eq_1)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_tofun_eq_1 : ∀ (P : StandardModel.HiggsField.Potential) (φ : StandardModel.HiggsField) (x : SpaceTime),
--   Eq (P.toFun φ x)
--     (instHAdd.hAdd (instHMul.hMul (Real.instNeg.neg P.μ2) (φ.normSq x))
--       (instHMul.hMul (instHMul.hMul P.𝓵 (φ.normSq x)) (φ.normSq x)))

-- Source: PhysLean (StandardModel.HiggsField.inner_zero_left)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_inner_zero_left : ∀ (φ : StandardModel.HiggsField),
--   Eq (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex.inner (SpaceTime → Complex) 0 φ) 0

-- Source: PhysLean (StandardModel.HiggsField.const_normSq)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_const_normsq : ∀ (φ : StandardModel.HiggsVec) (x : SpaceTime),
--   Eq ((LinearMap.instFunLike.coe StandardModel.HiggsField.const φ).normSq x)
--     (instHPow.hPow ((PiLp.instNorm 2 fun x => Complex).norm φ) 2)

-- Source: PhysLean (Fermion.AltLeftHandedModule.toFin2ℂEquiv_symm_apply_val)
-- [complex signature, not re-axiomatized]
-- fermion_altlefthandedmodule_tofin2ℂequiv_symm_apply_val : ∀ (a : Fin 2 → Complex) (a_1 : Fin 2),
--   Eq ((EquivLike.toFunLike.coe Fermion.AltLeftHandedModule.toFin2ℂEquiv.symm a).val a_1) (a a_1)

-- Source: PhysLean (StandardModel.HiggsField.Potential.isMinOn_iff_of_μSq_nonpos_𝓵_pos)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_isminon_iff_of_μsq_nonpos_𝓵_pos : ∀ (P : StandardModel.HiggsField.Potential),
--   Real.instLT.lt 0 P.𝓵 →
--     Real.instLE.le P.μ2 0 →
--       ∀ (φ : StandardModel.HiggsField) (x : SpaceTime),
--         Iff
--           (IsMinOn
--             (fun x =>
--               StandardModel.HiggsField.Potential.isMinOn_iff_of_μSq_nonpos_𝓵_pos.match_1 (fun x => Real) x fun φ x =>
--                 P.toFun φ x)
--             Set.univ { fst := φ, snd := x })
--           (Eq (P.toFun φ x) 0)

-- Source: PhysLean (Fermion.altLeftBasis_toFin2ℂ)
-- [complex signature, not re-axiomatized]
-- fermion_altleftbasis_tofin2ℂ : ∀ (i : Fin 2),
--   Eq (Fermion.AltLeftHandedModule.toFin2ℂ (Module.Basis.instFunLike.coe Fermion.altLeftBasis i)) (Pi.single i 1)

-- Source: PhysLean (Fermion.rightAltRightToMatrix_ρ_symm)
-- [complex signature, not re-axiomatized]
-- fermion_rightaltrighttomatrix_ρ_symm : ∀ (v : Matrix (Fin 2) (Fin 2) Complex) (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (LinearMap.instFunLike.coe
--       (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.rightHanded.ρ M)
--         (MonoidHom.instFunLike.coe Fermion.altRightHanded.ρ M))
--       (EquivLike.toFunLike.coe Fermion.rightAltRightToMatrix.symm v))
--     (EquivLike.toFunLike.coe Fermion.rightAltRightToMatrix.symm
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--         (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (M.val.map StarRing.toStarAddMonoid.star) v)
--         (Matrix.inv.inv M.val).conjTranspose.transpose))

-- Source: PhysLean (StandardModel.HiggsVec.gaugeGroupI_smul_eq_U1_mul_SU2)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsvec_gaugegroupi_smul_eq_u1_mul_su2 : ∀ (g : StandardModel.GaugeGroupI) (φ : StandardModel.HiggsVec),
--   Eq (instHSMul.hSMul g φ)
--     {
--       ofLp :=
--         (MonoidHom.instFunLike.coe StandardModel.GaugeGroupI.toSU2 g).val.mulVec
--           (instHSMul.hSMul (instHPow.hPow (MonoidHom.instFunLike.coe StandardModel.GaugeGroupI.toU1 g) 3) φ.ofLp) }

-- Source: PhysLean (StandardModel.HiggsField.Potential.μ2)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_μ2 : StandardModel.HiggsField.Potential → Real

-- Source: PhysLean (Fermion.rightAltContraction)
-- [complex signature, not re-axiomatized]
-- fermion_rightaltcontraction : Action.instCategory.Hom (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded)
--   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))

-- Source: PhysLean (Fermion.leftAltLeftUnitVal)
-- [complex signature, not re-axiomatized]
-- fermion_leftaltleftunitval : (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded).V.carrier

-- Source: PhysLean (StandardModel.HiggsField.const_toHiggsVec_apply)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_const_tohiggsvec_apply : ∀ (φ : StandardModel.HiggsField) (x : SpaceTime),
--   Eq (ContMDiffSection.instDFunLike.coe (LinearMap.instFunLike.coe StandardModel.HiggsField.const (φ.toHiggsVec x)) x)
--     (ContMDiffSection.instDFunLike.coe φ x)

-- Source: PhysLean (Fermion.AltRightHandedModule.instModuleComplex)
-- [complex signature, not re-axiomatized]
-- fermion_altrighthandedmodule_instmodulecomplex : Module Complex Fermion.AltRightHandedModule

-- Source: PhysLean (Fermion.star_comm_metricRaw)
-- [complex signature, not re-axiomatized]
-- fermion_star_comm_metricraw : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (M.val.map StarRing.toStarAddMonoid.star) Fermion.metricRaw)
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul Fermion.metricRaw (Matrix.inv.inv M.val).conjTranspose)

-- Source: PhysLean (StandardModel.HiggsField.inner_add_right)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_inner_add_right : ∀ (φ1 φ2 φ3 : StandardModel.HiggsField),
--   Eq
--     (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex.inner (SpaceTime → Complex) φ1
--       (instHAdd.hAdd φ2 φ3))
--     (instHAdd.hAdd (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex.inner (SpaceTime → Complex) φ1 φ2)
--       (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex.inner (SpaceTime → Complex) φ1 φ3))

-- Source: PhysLean (Fermion.altLeftLeftUnitVal_expand_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_altleftleftunitval_expand_tmul : Eq Fermion.altLeftLeftUnitVal
--   (instHAdd.hAdd
--     (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altLeftBasis 0)
--       (Module.Basis.instFunLike.coe Fermion.leftBasis 0))
--     (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altLeftBasis 1)
--       (Module.Basis.instFunLike.coe Fermion.leftBasis 1)))

-- Source: PhysLean (Fermion.altRightBi)
-- [complex signature, not re-axiomatized]
-- fermion_altrightbi : LinearMap (RingHom.id Complex) Fermion.altRightHanded.V.carrier
--   (LinearMap (RingHom.id Complex) Fermion.rightHanded.V.carrier Complex)

-- Source: PhysLean (Fermion.altRightMetricVal_expand_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_altrightmetricval_expand_tmul : Eq Fermion.altRightMetricVal
--   (instHSub.hSub
--     (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altRightBasis 0)
--       (Module.Basis.instFunLike.coe Fermion.altRightBasis 1))
--     (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altRightBasis 1)
--       (Module.Basis.instFunLike.coe Fermion.altRightBasis 0)))

-- Source: PhysLean (Fermion.leftAltContraction_tmul_symm)
-- [complex signature, not re-axiomatized]
-- fermion_leftaltcontraction_tmul_symm : ∀ (ψ : Fermion.leftHanded.V.carrier) (φ : Fermion.altLeftHanded.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.leftAltContraction.hom)
--       (TensorProduct.tmul Complex ψ φ))
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altLeftContraction.hom)
--       (TensorProduct.tmul Complex φ ψ))

-- Source: PhysLean (StandardModel.HiggsField.normSq_smooth)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_normsq_smooth : ∀ (φ : StandardModel.HiggsField),
--   ContMDiff (modelWithCornersSelf Real SpaceTime) (modelWithCornersSelf Real Real) WithTop.top.top φ.normSq

-- Source: PhysLean (StandardModel.HiggsBundle)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsbundle : SpaceTime → Type

-- Source: PhysLean (StandardModel.repU1Map_coe)
-- [complex signature, not re-axiomatized]
-- standardmodel_repu1map_coe : ∀ (g : Subtype fun x => SetLike.instMembership.mem (unitary Complex) x),
--   Eq (StandardModel.repU1Map g).val (instHSMul.hSMul (instHPow.hPow g 3) 1)

-- Source: PhysLean (Fermion.altRightRightToMatrix_ρ)
-- [complex signature, not re-axiomatized]
-- fermion_altrightrighttomatrix_ρ : ∀ (v : (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded).V.carrier)
--   (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (EquivLike.toFunLike.coe Fermion.altRightRightToMatrix
--       (LinearMap.instFunLike.coe
--         (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.altRightHanded.ρ M)
--           (MonoidHom.instFunLike.coe Fermion.rightHanded.ρ M))
--         v))
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.inv.inv M.val).conjTranspose
--         (EquivLike.toFunLike.coe Fermion.altRightRightToMatrix v))
--       (M.val.map StarRing.toStarAddMonoid.star).transpose)

-- Source: PhysLean (Fermion.AltRightHandedModule.toFin2ℂFun)
-- [complex signature, not re-axiomatized]
-- fermion_altrighthandedmodule_tofin2ℂfun : Equiv Fermion.AltRightHandedModule (Fin 2 → Complex)

-- Source: PhysLean (Fermion.RightHandedModule.ctorIdx)
-- [complex signature, not re-axiomatized]
-- fermion_righthandedmodule_ctoridx : Fermion.RightHandedModule → Nat

-- Source: PhysLean (StandardModel.HiggsField.inner_zero_right)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_inner_zero_right : ∀ (φ : StandardModel.HiggsField),
--   Eq (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex.inner (SpaceTime → Complex) φ 0) 0

-- Source: PhysLean (StandardModel.HiggsField.Potential.isMinOn_iff_field_of_𝓵_pos)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_isminon_iff_field_of_𝓵_pos : ∀ (P : StandardModel.HiggsField.Potential),
--   Real.instLT.lt 0 P.𝓵 →
--     ∀ (φ : StandardModel.HiggsField) (x : SpaceTime),
--       Iff
--         (IsMinOn
--           (fun x =>
--             StandardModel.HiggsField.Potential.isMinOn_iff_of_μSq_nonpos_𝓵_pos.match_1 (fun x => Real) x fun φ x =>
--               P.toFun φ x)
--           Set.univ { fst := φ, snd := x })
--         (Or (And (Real.instLE.le 0 P.μ2) (Eq (φ.normSq x) (instHDiv.hDiv P.μ2 (instHMul.hMul 2 P.𝓵))))
--           (And (Real.instLT.lt P.μ2 0) (Eq (ContMDiffSection.instDFunLike.coe φ x) 0)))

-- Source: PhysLean (StandardModel.HiggsField)
/-- The type `HiggsField` is defined such that elements are smooth sections of the trivial
vector bundle `HiggsBundle`. Such elements are Higgs fields. Since `HiggsField` is
trivial as a vector bundle, a Higgs field is equivalent to a smooth map
from `SpaceTime` to `HiggsVec`.  -/
axiom standardmodel_higgsfield :
  Type

-- Source: PhysLean (Fermion.AltLeftHandedModule.toFin2ℂEquiv_apply)
-- [complex signature, not re-axiomatized]
-- fermion_altlefthandedmodule_tofin2ℂequiv_apply : ∀ (a : Fermion.AltLeftHandedModule) (a_1 : Fin 2),
--   Eq (EquivLike.toFunLike.coe Fermion.AltLeftHandedModule.toFin2ℂEquiv a a_1)
--     (EquivLike.toFunLike.coe Fermion.AltLeftHandedModule.toFin2ℂFun a a_1)

-- Source: PhysLean (Fermion.AltLeftHandedModule.instAddCommMonoid)
-- [complex signature, not re-axiomatized]
-- fermion_altlefthandedmodule_instaddcommmonoid : AddCommMonoid Fermion.AltLeftHandedModule

-- Source: PhysLean (Fermion.leftHandedToAlt_hom_apply)
-- [complex signature, not re-axiomatized]
-- fermion_lefthandedtoalt_hom_apply : ∀ (ψ : Fermion.leftHanded.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike) Fermion.leftHanded.V Fermion.altLeftHanded.V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.leftHandedToAlt.hom) ψ)
--     (EquivLike.toFunLike.coe Fermion.AltLeftHandedModule.toFin2ℂEquiv.symm
--       ((EquivLike.toFunLike.coe Matrix.of
--             (Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons 1 Matrix.vecEmpty))
--               (Matrix.vecCons (Matrix.vecCons (-1) (Matrix.vecCons 0 Matrix.vecEmpty)) Matrix.vecEmpty))).mulVec
--         (Fermion.LeftHandedModule.toFin2ℂ ψ)))

-- Source: PhysLean (Fermion.AltLeftHandedModule.val)
-- [complex signature, not re-axiomatized]
-- fermion_altlefthandedmodule_val : Fermion.AltLeftHandedModule → Fin 2 → Complex

-- Source: PhysLean (StandardModel.HiggsField.Potential.neg_𝓵_toFun_neg)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_neg_𝓵_tofun_neg : ∀ (P : StandardModel.HiggsField.Potential),
--   Real.instLT.lt P.𝓵 0 →
--     ∀ (φ : StandardModel.HiggsField) (x : SpaceTime),
--       Or (And (Real.instLT.lt 0 P.μ2) (Real.instLE.le (P.toFun φ x) 0)) (Real.instLE.le P.μ2 0)

-- Source: PhysLean (Fermion.altLeftLeftToMatrix_ρ)
-- [complex signature, not re-axiomatized]
-- fermion_altleftlefttomatrix_ρ : ∀ (v : (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded).V.carrier)
--   (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (EquivLike.toFunLike.coe Fermion.altLeftLeftToMatrix
--       (LinearMap.instFunLike.coe
--         (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.altLeftHanded.ρ M)
--           (MonoidHom.instFunLike.coe Fermion.leftHanded.ρ M))
--         v))
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.inv.inv M.val).transpose
--         (EquivLike.toFunLike.coe Fermion.altLeftLeftToMatrix v))
--       M.val.transpose)

-- Source: PhysLean (Fermion.rightBasis.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_rightbasis_eq_1 : Eq Fermion.rightBasis (Module.Basis.ofEquivFun (Equiv.linearEquiv Complex Fermion.RightHandedModule.toFin2ℂFun))

-- Source: PhysLean (Fermion.leftBasis.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_leftbasis_eq_1 : Eq Fermion.leftBasis (Module.Basis.ofEquivFun (Equiv.linearEquiv Complex Fermion.LeftHandedModule.toFin2ℂFun))

-- Source: PhysLean (Fermion.leftAltLeftUnitVal.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_leftaltleftunitval_eq_1 : Eq Fermion.leftAltLeftUnitVal (EquivLike.toFunLike.coe Fermion.leftAltLeftToMatrix.symm 1)

-- Source: PhysLean (Fermion.leftRightToMatrix_ρ_symm)
-- [complex signature, not re-axiomatized]
-- fermion_leftrighttomatrix_ρ_symm : ∀ (v : Matrix (Fin 2) (Fin 2) Complex) (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (LinearMap.instFunLike.coe
--       (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.leftHanded.ρ M)
--         (MonoidHom.instFunLike.coe Fermion.rightHanded.ρ M))
--       (EquivLike.toFunLike.coe Fermion.leftRightToMatrix.symm v))
--     (EquivLike.toFunLike.coe Fermion.leftRightToMatrix.symm
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul M.val v)
--         M.val.conjTranspose))

-- Source: PhysLean (StandardModel.HiggsVec.toFin2ℂ)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsvec_tofin2ℂ : ContinuousLinearMap (RingHom.id Real) StandardModel.HiggsVec (Fin 2 → Complex)

-- Source: PhysLean (Fermion.altRightAltRightToMatrix.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_altrightaltrighttomatrix_eq_1 : Eq Fermion.altRightAltRightToMatrix
--   (((Fermion.altRightBasis.tensorProduct Fermion.altRightBasis).repr.trans
--         (Finsupp.linearEquivFunOnFinite Complex Complex (Prod (Fin 2) (Fin 2)))).trans
--     (LinearEquiv.curry Complex Complex (Fin 2) (Fin 2)))

-- Source: PhysLean (StandardModel.HiggsField.normSq_nonneg)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_normsq_nonneg : ∀ (φ : StandardModel.HiggsField) (x : SpaceTime), Real.instLE.le 0 (φ.normSq x)

-- Source: PhysLean (Fermion.altRightMetric)
-- [complex signature, not re-axiomatized]
-- fermion_altrightmetric : Action.instCategory.Hom
--   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--   (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.altRightHanded)

-- Source: PhysLean (StandardModel.GaugeGroupQuot.ctorElim)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupquot_ctorelim : {motive : StandardModel.GaugeGroupQuot → Sort u} →
--   (ctorIdx : Nat) →
--     (t : StandardModel.GaugeGroupQuot) →
--       Eq ctorIdx t.ctorIdx → StandardModel.GaugeGroupQuot.ctorElimType ctorIdx → motive t

-- Source: PhysLean (StandardModel.HiggsVec.instSMulGaugeGroupI)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsvec_instsmulgaugegroupi : SMul StandardModel.GaugeGroupI StandardModel.HiggsVec

-- Source: PhysLean (StandardModel.HiggsField.Potential.as_quad)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_as_quad : ∀ (P : StandardModel.HiggsField.Potential) (φ : StandardModel.HiggsField) (x : SpaceTime),
--   Eq
--     (instHAdd.hAdd
--       (instHAdd.hAdd (instHMul.hMul (instHMul.hMul P.𝓵 (φ.normSq x)) (φ.normSq x))
--         (instHMul.hMul (Real.instNeg.neg P.μ2) (φ.normSq x)))
--       (Real.instNeg.neg (P.toFun φ x)))
--     0

-- Source: PhysLean (Fermion.AltRightHandedModule.toFin2ℂEquiv)
-- [complex signature, not re-axiomatized]
-- fermion_altrighthandedmodule_tofin2ℂequiv : LinearEquiv (RingHom.id Complex) Fermion.AltRightHandedModule (Fin 2 → Complex)

-- Source: PhysLean (Fermion.altLeftaltLeftToMatrix_ρ_symm)
-- [complex signature, not re-axiomatized]
-- fermion_altleftaltlefttomatrix_ρ_symm : ∀ (v : Matrix (Fin 2) (Fin 2) Complex) (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (LinearMap.instFunLike.coe
--       (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.altLeftHanded.ρ M)
--         (MonoidHom.instFunLike.coe Fermion.altLeftHanded.ρ M))
--       (EquivLike.toFunLike.coe Fermion.altLeftaltLeftToMatrix.symm v))
--     (EquivLike.toFunLike.coe Fermion.altLeftaltLeftToMatrix.symm
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--         (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.inv.inv M.val).transpose v) (Matrix.inv.inv M.val)))

-- Source: PhysLean (StandardModel.HiggsField.Potential.neg.eq_1)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_neg_eq_1 : ∀ (P : StandardModel.HiggsField.Potential), Eq P.neg { μ2 := Real.instNeg.neg P.μ2, 𝓵 := Real.instNeg.neg P.𝓵 }

-- Source: PhysLean (StandardModel.HiggsField.inner_add_left)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_inner_add_left : ∀ (φ1 φ2 φ3 : StandardModel.HiggsField),
--   Eq
--     (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex.inner (SpaceTime → Complex) (instHAdd.hAdd φ1 φ2)
--       φ3)
--     (instHAdd.hAdd (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex.inner (SpaceTime → Complex) φ1 φ3)
--       (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex.inner (SpaceTime → Complex) φ2 φ3))

-- Source: PhysLean (StandardModel.repU1Map.eq_1)
-- [complex signature, not re-axiomatized]
-- standardmodel_repu1map_eq_1 : ∀ (g : Subtype fun x => SetLike.instMembership.mem (unitary Complex) x),
--   Eq (StandardModel.repU1Map g) ⟨instHSMul.hSMul (instHPow.hPow g 3) 1, ⋯⟩

-- Source: PhysLean (Fermion.AltRightHandedModule.instAddCommMonoid)
-- [complex signature, not re-axiomatized]
-- fermion_altrighthandedmodule_instaddcommmonoid : AddCommMonoid Fermion.AltRightHandedModule

-- Source: PhysLean (Fermion.AltLeftHandedModule.instAddCommGroup)
-- [complex signature, not re-axiomatized]
-- fermion_altlefthandedmodule_instaddcommgroup : AddCommGroup Fermion.AltLeftHandedModule

-- Source: PhysLean (StandardModel.gaugeGroup_lie)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroup_lie : InformalLemma

-- Source: PhysLean (Fermion.rightAltRightUnit_apply_one)
-- [complex signature, not re-axiomatized]
-- fermion_rightaltrightunit_apply_one : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.rightAltRightUnit.hom) 1)
--   Fermion.rightAltRightUnitVal

-- Source: PhysLean (Fermion.rightAltContraction_hom_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_rightaltcontraction_hom_tmul : ∀ (ψ : Fermion.rightHanded.V.carrier) (φ : Fermion.altRightHanded.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.rightAltContraction.hom)
--       (TensorProduct.tmul Complex ψ φ))
--     (dotProduct (Fermion.RightHandedModule.toFin2ℂ ψ) (Fermion.AltRightHandedModule.toFin2ℂ φ))

-- Source: PhysLean (Fermion.altRightRightToMatrix_symm_expand_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_altrightrighttomatrix_symm_expand_tmul : ∀ (M : Matrix (Fin 2) (Fin 2) Complex),
--   Eq (EquivLike.toFunLike.coe Fermion.altRightRightToMatrix.symm M)
--     (Finset.univ.sum fun i =>
--       Finset.univ.sum fun j =>
--         instHSMul.hSMul (M i j)
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altRightBasis i)
--             (Module.Basis.instFunLike.coe Fermion.rightBasis j)))

-- Source: PhysLean (Fermion.altLeftBasis)
-- [complex signature, not re-axiomatized]
-- fermion_altleftbasis : Module.Basis (Fin 2) Complex Fermion.altLeftHanded.V.carrier

-- Source: PhysLean (StandardModel.GaugeGroupℤ₆)
/-- The smallest possible gauge group of the Standard Model, i.e., the quotient of `GaugeGroupI` by
the ℤ₆-subgroup `gaugeGroupℤ₆SubGroup`.

See https://math.ucr.edu/home/baez/guts.pdf
 -/
axiom standardmodel_gaugegroupℤ₆ :
  Type

-- Source: PhysLean (Fermion.rightAltRightToMatrix_ρ)
-- [complex signature, not re-axiomatized]
-- fermion_rightaltrighttomatrix_ρ : ∀ (v : (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded).V.carrier)
--   (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (EquivLike.toFunLike.coe Fermion.rightAltRightToMatrix
--       (LinearMap.instFunLike.coe
--         (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.rightHanded.ρ M)
--           (MonoidHom.instFunLike.coe Fermion.altRightHanded.ρ M))
--         v))
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (M.val.map StarRing.toStarAddMonoid.star)
--         (EquivLike.toFunLike.coe Fermion.rightAltRightToMatrix v))
--       (Matrix.inv.inv M.val).conjTranspose.transpose)

-- Source: PhysLean (Fermion.leftLeftToMatrix_ρ)
-- [complex signature, not re-axiomatized]
-- fermion_leftlefttomatrix_ρ : ∀ (v : (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.leftHanded).V.carrier)
--   (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (EquivLike.toFunLike.coe Fermion.leftLeftToMatrix
--       (LinearMap.instFunLike.coe
--         (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.leftHanded.ρ M)
--           (MonoidHom.instFunLike.coe Fermion.leftHanded.ρ M))
--         v))
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul M.val (EquivLike.toFunLike.coe Fermion.leftLeftToMatrix v))
--       M.val.transpose)

-- Source: PhysLean (Fermion.leftAltLeftUnitVal_expand_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_leftaltleftunitval_expand_tmul : Eq Fermion.leftAltLeftUnitVal
--   (instHAdd.hAdd
--     (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.leftBasis 0)
--       (Module.Basis.instFunLike.coe Fermion.altLeftBasis 0))
--     (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.leftBasis 1)
--       (Module.Basis.instFunLike.coe Fermion.altLeftBasis 1)))

-- Source: PhysLean (Fermion.rightMetricVal.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_rightmetricval_eq_1 : Eq Fermion.rightMetricVal (EquivLike.toFunLike.coe Fermion.rightRightToMatrix.symm (Matrix.neg.neg Fermion.metricRaw))

-- Source: PhysLean (Fermion.altLeftMetricVal.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_altleftmetricval_eq_1 : Eq Fermion.altLeftMetricVal (EquivLike.toFunLike.coe Fermion.altLeftaltLeftToMatrix.symm Fermion.metricRaw)

-- Source: PhysLean (Fermion.leftAltLeftToMatrix.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_leftaltlefttomatrix_eq_1 : Eq Fermion.leftAltLeftToMatrix
--   (((Fermion.leftBasis.tensorProduct Fermion.altLeftBasis).repr.trans
--         (Finsupp.linearEquivFunOnFinite Complex Complex (Prod (Fin 2) (Fin 2)))).trans
--     (LinearEquiv.curry Complex Complex (Fin 2) (Fin 2)))

-- Source: PhysLean (Fermion.rightAltRightToMatrix_symm_expand_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_rightaltrighttomatrix_symm_expand_tmul : ∀ (M : Matrix (Fin 2) (Fin 2) Complex),
--   Eq (EquivLike.toFunLike.coe Fermion.rightAltRightToMatrix.symm M)
--     (Finset.univ.sum fun i =>
--       Finset.univ.sum fun j =>
--         instHSMul.hSMul (M i j)
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.rightBasis i)
--             (Module.Basis.instFunLike.coe Fermion.altRightBasis j)))

-- Source: PhysLean (StandardModel.HiggsField.Potential.IsBounded)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_isbounded : StandardModel.HiggsField.Potential → Prop

-- Source: PhysLean (Fermion.altLeftMetricVal_expand_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_altleftmetricval_expand_tmul : Eq Fermion.altLeftMetricVal
--   (instHSub.hSub
--     (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altLeftBasis 0)
--       (Module.Basis.instFunLike.coe Fermion.altLeftBasis 1))
--     (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altLeftBasis 1)
--       (Module.Basis.instFunLike.coe Fermion.altLeftBasis 0)))

-- Source: PhysLean (Fermion.rightRightToMatrix_symm_expand_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_rightrighttomatrix_symm_expand_tmul : ∀ (M : Matrix (Fin 2) (Fin 2) Complex),
--   Eq (EquivLike.toFunLike.coe Fermion.rightRightToMatrix.symm M)
--     (Finset.univ.sum fun i =>
--       Finset.univ.sum fun j =>
--         instHSMul.hSMul (M i j)
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.rightBasis i)
--             (Module.Basis.instFunLike.coe Fermion.rightBasis j)))

-- Source: PhysLean (Fermion.metricRaw.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_metricraw_eq_1 : Eq Fermion.metricRaw
--   (EquivLike.toFunLike.coe Matrix.of
--     (Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons 1 Matrix.vecEmpty))
--       (Matrix.vecCons (Matrix.vecCons (-1) (Matrix.vecCons 0 Matrix.vecEmpty)) Matrix.vecEmpty)))

-- Source: PhysLean (StandardModel.HiggsField.apply_re_smooth)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_apply_re_smooth : ∀ (φ : StandardModel.HiggsField) (i : Fin 2),
--   ContMDiff (modelWithCornersSelf Real SpaceTime) (modelWithCornersSelf Real Real) WithTop.top.top
--     (Function.comp (ContinuousLinearMap.funLike.coe Complex.reCLM) fun x =>
--       (ContMDiffSection.instDFunLike.coe φ x).ofLp i)

-- Source: PhysLean (Fermion.rightAltRightUnitVal)
-- [complex signature, not re-axiomatized]
-- fermion_rightaltrightunitval : (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded).V.carrier

-- Source: PhysLean (StandardModel.HiggsField.Potential.quadDiscrim_eq_zero_iff_normSq)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_quaddiscrim_eq_zero_iff_normsq : ∀ (P : StandardModel.HiggsField.Potential),
--   Ne P.𝓵 0 →
--     ∀ (φ : StandardModel.HiggsField) (x : SpaceTime),
--       Iff (Eq (P.quadDiscrim φ x) 0) (Eq (φ.normSq x) (instHDiv.hDiv P.μ2 (instHMul.hMul 2 P.𝓵)))

-- Source: PhysLean (StandardModel.HiggsField.Potential.ctorIdx)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_ctoridx : StandardModel.HiggsField.Potential → Nat

-- Source: PhysLean (Fermion.leftHandedAltTo_hom_apply)
-- [complex signature, not re-axiomatized]
-- fermion_lefthandedaltto_hom_apply : ∀ (ψ : Fermion.altLeftHanded.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike) Fermion.altLeftHanded.V Fermion.leftHanded.V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.leftHandedAltTo.hom) ψ)
--     (EquivLike.toFunLike.coe Fermion.LeftHandedModule.toFin2ℂEquiv.symm
--       ((EquivLike.toFunLike.coe Matrix.of
--             (Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons (-1) Matrix.vecEmpty))
--               (Matrix.vecCons (Matrix.vecCons 1 (Matrix.vecCons 0 Matrix.vecEmpty)) Matrix.vecEmpty))).mulVec
--         (Fermion.AltLeftHandedModule.toFin2ℂ ψ)))

-- Source: PhysLean (Fermion.leftRightToMatrix_symm_expand_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_leftrighttomatrix_symm_expand_tmul : ∀ (M : Matrix (Fin 2) (Fin 2) Complex),
--   Eq (EquivLike.toFunLike.coe Fermion.leftRightToMatrix.symm M)
--     (Finset.univ.sum fun i =>
--       Finset.univ.sum fun j =>
--         instHSMul.hSMul (M i j)
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.leftBasis i)
--             (Module.Basis.instFunLike.coe Fermion.rightBasis j)))

-- Source: PhysLean (StandardModel.fundamentalSU2_apply_coe)
-- [complex signature, not re-axiomatized]
-- standardmodel_fundamentalsu2_apply_coe : ∀ (g : Subtype fun x => SetLike.instMembership.mem (Matrix.specialUnitaryGroup (Fin 2) Complex) x),
--   Eq (MonoidHom.instFunLike.coe StandardModel.fundamentalSU2 g).val g.val

-- Source: PhysLean (Fermion.altLeftLeftUnit_apply_one)
-- [complex signature, not re-axiomatized]
-- fermion_altleftleftunit_apply_one : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altLeftLeftUnit.hom) 1)
--   Fermion.altLeftLeftUnitVal

-- Source: PhysLean (StandardModel.HiggsField.gauge_orbit_surject)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_gauge_orbit_surject : InformalLemma

-- Source: PhysLean (StandardModel.HiggsField.Potential.toFun_zero)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_tofun_zero : ∀ (P : StandardModel.HiggsField.Potential) (x : SpaceTime), Eq (P.toFun 0 x) 0

-- Source: PhysLean (Fermion.leftHandedAltEquiv_inv_hom_apply)
-- [complex signature, not re-axiomatized]
-- fermion_lefthandedaltequiv_inv_hom_apply : ∀ (ψ : Fermion.altLeftHanded.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike) Fermion.altLeftHanded.V Fermion.leftHanded.V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.leftHandedAltEquiv.inv.hom) ψ)
--     (EquivLike.toFunLike.coe Fermion.LeftHandedModule.toFin2ℂEquiv.symm
--       ((EquivLike.toFunLike.coe Matrix.of
--             (Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons (-1) Matrix.vecEmpty))
--               (Matrix.vecCons (Matrix.vecCons 1 (Matrix.vecCons 0 Matrix.vecEmpty)) Matrix.vecEmpty))).mulVec
--         (Fermion.AltLeftHandedModule.toFin2ℂ ψ)))

-- Source: PhysLean (StandardModel.HiggsField.Potential.isMinOn_iff_field_of_μSq_nonpos_𝓵_pos)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_isminon_iff_field_of_μsq_nonpos_𝓵_pos : ∀ (P : StandardModel.HiggsField.Potential),
--   Real.instLT.lt 0 P.𝓵 →
--     Real.instLE.le P.μ2 0 →
--       ∀ (φ : StandardModel.HiggsField) (x : SpaceTime),
--         Iff
--           (IsMinOn
--             (fun x =>
--               StandardModel.HiggsField.Potential.isMinOn_iff_of_μSq_nonpos_𝓵_pos.match_1 (fun x => Real) x fun φ x =>
--                 P.toFun φ x)
--             Set.univ { fst := φ, snd := x })
--           (Eq (ContMDiffSection.instDFunLike.coe φ x) 0)

-- Source: PhysLean (StandardModel.GaugeGroupQuot.ℤ₂.sizeOf_spec)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupquot_ℤ₂_sizeof_spec : Eq (StandardModel.GaugeGroupQuot._sizeOf_inst.sizeOf StandardModel.GaugeGroupQuot.ℤ₂) 1

-- Source: PhysLean (Fermion.altLeftLeftUnitVal)
-- [complex signature, not re-axiomatized]
-- fermion_altleftleftunitval : (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded).V.carrier

-- Source: PhysLean (Fermion.metricRaw_comm_star)
-- [complex signature, not re-axiomatized]
-- fermion_metricraw_comm_star : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul Fermion.metricRaw (M.val.map StarRing.toStarAddMonoid.star))
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.inv.inv M.val).conjTranspose Fermion.metricRaw)

-- Source: PhysLean (Fermion.LeftHandedModule.instModuleComplex)
-- [complex signature, not re-axiomatized]
-- fermion_lefthandedmodule_instmodulecomplex : Module Complex Fermion.LeftHandedModule

-- Source: PhysLean (Fermion.leftLeftToMatrix.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_leftlefttomatrix_eq_1 : Eq Fermion.leftLeftToMatrix
--   (((Fermion.leftBasis.tensorProduct Fermion.leftBasis).repr.trans
--         (Finsupp.linearEquivFunOnFinite Complex Complex (Prod (Fin 2) (Fin 2)))).trans
--     (LinearEquiv.curry Complex Complex (Fin 2) (Fin 2)))

-- Source: PhysLean (StandardModel.HiggsVec.gaugeGroupI_smul_inner)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsvec_gaugegroupi_smul_inner : ∀ (g : StandardModel.GaugeGroupI) (φ ψ : StandardModel.HiggsVec),
--   Eq ((PiLp.innerProductSpace fun x => Complex).inner Complex (instHSMul.hSMul g φ) (instHSMul.hSMul g ψ))
--     ((PiLp.innerProductSpace fun x => Complex).inner Complex φ ψ)

-- Source: PhysLean (Fermion.RightHandedModule.instAddCommGroup)
-- [complex signature, not re-axiomatized]
-- fermion_righthandedmodule_instaddcommgroup : AddCommGroup Fermion.RightHandedModule

-- Source: PhysLean (StandardModel.GaugeGroupI)
/-- The global gauge group of the Standard Model with no discrete quotients.
The `I` in the Name is an indication of the statement that this has no discrete quotients.  -/
axiom standardmodel_gaugegroupi :
  Type

-- Source: PhysLean (Fermion.rightAltRightUnitVal_expand_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_rightaltrightunitval_expand_tmul : Eq Fermion.rightAltRightUnitVal
--   (instHAdd.hAdd
--     (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.rightBasis 0)
--       (Module.Basis.instFunLike.coe Fermion.altRightBasis 0))
--     (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.rightBasis 1)
--       (Module.Basis.instFunLike.coe Fermion.altRightBasis 1)))

-- Source: PhysLean (Fermion.rightMetric)
-- [complex signature, not re-axiomatized]
-- fermion_rightmetric : Action.instCategory.Hom
--   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--   (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.rightHanded)

-- Source: PhysLean (StandardModel.gaugeBundleI)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugebundlei : InformalDefinition

-- Source: PhysLean (StandardModel.GaugeGroupℤ₂)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupℤ₂ : InformalDefinition

-- Source: PhysLean (Fermion.rightRightToMatrix)
-- [complex signature, not re-axiomatized]
-- fermion_rightrighttomatrix : LinearEquiv (RingHom.id Complex)
--   (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.rightHanded).V.carrier
--   (Matrix (Fin 2) (Fin 2) Complex)

-- Source: PhysLean (Fermion.rightAltContraction_basis)
-- [complex signature, not re-axiomatized]
-- fermion_rightaltcontraction_basis : ∀ (i j : Fin 2),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.rightAltContraction.hom)
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.rightBasis i)
--         (Module.Basis.instFunLike.coe Fermion.altRightBasis j)))
--     (ite (Eq i.val j.val) 1 0)

-- Source: PhysLean (StandardModel.HiggsVec.toRealGroupElem)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsvec_torealgroupelem : StandardModel.HiggsVec → StandardModel.GaugeGroupI

-- Source: PhysLean (Fermion.AltLeftHandedModule.toFin2ℂ.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_altlefthandedmodule_tofin2ℂ_eq_1 : ∀ (ψ : Fermion.AltLeftHandedModule), Eq ψ.toFin2ℂ (EquivLike.toFunLike.coe Fermion.AltLeftHandedModule.toFin2ℂEquiv ψ)

-- Source: PhysLean (StandardModel.GaugeGroupI.star_toU1)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupi_star_tou1 : ∀ (g : StandardModel.GaugeGroupI),
--   Eq (MonoidHom.instFunLike.coe StandardModel.GaugeGroupI.toU1 (StandardModel.GaugeGroupI.instStar.star g))
--     (Unitary.instStarSubtypeMemSubmonoidUnitary.star (MonoidHom.instFunLike.coe StandardModel.GaugeGroupI.toU1 g))

-- Source: PhysLean (Fermion.rightAltBi)
-- [complex signature, not re-axiomatized]
-- fermion_rightaltbi : LinearMap (RingHom.id Complex) Fermion.rightHanded.V.carrier
--   (LinearMap (RingHom.id Complex) Fermion.altRightHanded.V.carrier Complex)

-- Source: PhysLean (Fermion.LeftHandedModule.val)
-- [complex signature, not re-axiomatized]
-- fermion_lefthandedmodule_val : Fermion.LeftHandedModule → Fin 2 → Complex

-- Source: PhysLean (Fermion.altLeftMetric_apply_one)
-- [complex signature, not re-axiomatized]
-- fermion_altleftmetric_apply_one : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.altLeftHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altLeftMetric.hom) 1)
--   Fermion.altLeftMetricVal

-- Source: PhysLean (Fermion.altRightContraction_tmul_symm)
-- [complex signature, not re-axiomatized]
-- fermion_altrightcontraction_tmul_symm : ∀ (φ : Fermion.altRightHanded.V.carrier) (ψ : Fermion.rightHanded.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altRightContraction.hom)
--       (TensorProduct.tmul Complex φ ψ))
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.rightAltContraction.hom)
--       (TensorProduct.tmul Complex ψ φ))

-- Source: PhysLean (StandardModel.HiggsField.Potential.toFun_smooth)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_tofun_smooth : ∀ (P : StandardModel.HiggsField.Potential) (φ : StandardModel.HiggsField),
--   ContMDiff (modelWithCornersSelf Real SpaceTime) (modelWithCornersSelf Real Real) WithTop.top.top fun x => P.toFun φ x

-- Source: PhysLean (StandardModel.gaugeGroupI_lie)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupi_lie : InformalLemma

-- Source: PhysLean (StandardModel.HiggsField.normSq.eq_1)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_normsq_eq_1 : ∀ (φ : StandardModel.HiggsField) (x : SpaceTime),
--   Eq (φ.normSq x) (instHPow.hPow ((PiLp.instNorm 2 fun x => Complex).norm (ContMDiffSection.instDFunLike.coe φ x)) 2)

-- Source: PhysLean (Fermion.LeftHandedModule.toFin2ℂEquiv)
-- [complex signature, not re-axiomatized]
-- fermion_lefthandedmodule_tofin2ℂequiv : LinearEquiv (RingHom.id Complex) Fermion.LeftHandedModule (Fin 2 → Complex)

-- Source: PhysLean (Fermion.contr_leftAltLeftUnit)
-- [complex signature, not re-axiomatized]
-- fermion_contr_leftaltleftunit : ∀ (x : Fermion.altLeftHanded.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj
--               (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--               Fermion.altLeftHanded).V
--           Fermion.altLeftHanded.V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--         (Action.instMonoidalCategory.leftUnitor Fermion.altLeftHanded).hom.hom)
--       (((fun X Y => LinearMap.instFunLike)
--             (Action.instMonoidalCategory.tensorObj
--                 (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded)
--                 Fermion.altLeftHanded).V
--             (Action.instMonoidalCategory.tensorObj
--                 (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--                 Fermion.altLeftHanded).V).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--           (Action.instMonoidalCategory.whiskerRight Fermion.altLeftContraction Fermion.altLeftHanded).hom)
--         (((fun X Y => LinearMap.instFunLike)
--               (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded
--                   (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded)).V
--               (Action.instMonoidalCategory.tensorObj
--                   (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded)
--                   Fermion.altLeftHanded).V).coe
--           ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--             (Action.instMonoidalCategory.associator Fermion.altLeftHanded Fermion.leftHanded
--                   Fermion.altLeftHanded).inv.hom)
--           (TensorProduct.tmul Complex x
--             (((fun X Y => LinearMap.instFunLike)
--                   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                   (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded).V).coe
--               ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.leftAltLeftUnit.hom) 1)))))
--     x

-- Source: PhysLean (Fermion.rightAltRightToMatrix.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_rightaltrighttomatrix_eq_1 : Eq Fermion.rightAltRightToMatrix
--   (((Fermion.rightBasis.tensorProduct Fermion.altRightBasis).repr.trans
--         (Finsupp.linearEquivFunOnFinite Complex Complex (Prod (Fin 2) (Fin 2)))).trans
--     (LinearEquiv.curry Complex Complex (Fin 2) (Fin 2)))

-- Source: PhysLean (Fermion.leftLeftToMatrix_ρ_symm)
-- [complex signature, not re-axiomatized]
-- fermion_leftlefttomatrix_ρ_symm : ∀ (v : Matrix (Fin 2) (Fin 2) Complex) (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (LinearMap.instFunLike.coe
--       (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.leftHanded.ρ M)
--         (MonoidHom.instFunLike.coe Fermion.leftHanded.ρ M))
--       (EquivLike.toFunLike.coe Fermion.leftLeftToMatrix.symm v))
--     (EquivLike.toFunLike.coe Fermion.leftLeftToMatrix.symm
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul M.val v)
--         M.val.transpose))

-- Source: PhysLean (StandardModel.GaugeGroupI.toSU3.eq_1)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupi_tosu3_eq_1 : Eq StandardModel.GaugeGroupI.toSU3
--   { toFun := fun g => g.fst, map_one' := StandardModel.GaugeGroupI.toSU3._proof_1,
--     map_mul' := StandardModel.GaugeGroupI.toSU3._proof_2 }

-- Source: PhysLean (Fermion.AltLeftHandedModule.ctorIdx)
-- [complex signature, not re-axiomatized]
-- fermion_altlefthandedmodule_ctoridx : Fermion.AltLeftHandedModule → Nat

-- Source: PhysLean (Fermion.rightBasis_ρ_apply)
-- [complex signature, not re-axiomatized]
-- fermion_rightbasis_ρ_apply : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex) (i j : Fin 2),
--   Eq
--     (EquivLike.toFunLike.coe (LinearMap.toMatrix Fermion.rightBasis Fermion.rightBasis)
--       (MonoidHom.instFunLike.coe Fermion.rightHanded.ρ M) i j)
--     (M.val.map StarRing.toStarAddMonoid.star i j)

-- Source: PhysLean (Fermion.leftHandedToAlt)
-- [complex signature, not re-axiomatized]
-- fermion_lefthandedtoalt : Action.instCategory.Hom Fermion.leftHanded Fermion.altLeftHanded

-- Source: PhysLean (Fermion.leftBasis)
-- [complex signature, not re-axiomatized]
-- fermion_leftbasis : Module.Basis (Fin 2) Complex Fermion.leftHanded.V.carrier

-- Source: PhysLean (Fermion.rightAltRightUnitVal.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_rightaltrightunitval_eq_1 : Eq Fermion.rightAltRightUnitVal (EquivLike.toFunLike.coe Fermion.rightAltRightToMatrix.symm 1)

-- Source: PhysLean (Fermion.rightMetricVal_expand_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_rightmetricval_expand_tmul : Eq Fermion.rightMetricVal
--   (instHAdd.hAdd
--     (TensorProduct.neg.neg
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.rightBasis 0)
--         (Module.Basis.instFunLike.coe Fermion.rightBasis 1)))
--     (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.rightBasis 1)
--       (Module.Basis.instFunLike.coe Fermion.rightBasis 0)))

-- Source: PhysLean (Fermion.leftBasis_ρ_apply)
-- [complex signature, not re-axiomatized]
-- fermion_leftbasis_ρ_apply : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex) (i j : Fin 2),
--   Eq
--     (EquivLike.toFunLike.coe (LinearMap.toMatrix Fermion.leftBasis Fermion.leftBasis)
--       (MonoidHom.instFunLike.coe Fermion.leftHanded.ρ M) i j)
--     (M.val i j)

-- Source: PhysLean (StandardModel.GaugeGroupI.ext)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupi_ext : ∀ {g g' : StandardModel.GaugeGroupI},
--   Eq (MonoidHom.instFunLike.coe StandardModel.GaugeGroupI.toSU3 g)
--       (MonoidHom.instFunLike.coe StandardModel.GaugeGroupI.toSU3 g') →
--     Eq (MonoidHom.instFunLike.coe StandardModel.GaugeGroupI.toSU2 g)
--         (MonoidHom.instFunLike.coe StandardModel.GaugeGroupI.toSU2 g') →
--       Eq (MonoidHom.instFunLike.coe StandardModel.GaugeGroupI.toU1 g)
--           (MonoidHom.instFunLike.coe StandardModel.GaugeGroupI.toU1 g') →
--         Eq g g'

-- Source: PhysLean (Fermion.altRightRightUnit_symm)
-- [complex signature, not re-axiomatized]
-- fermion_altrightrightunit_symm : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altRightRightUnit.hom) 1)
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded).V
--         (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--       (Action.instMonoidalCategory.whiskerLeft Fermion.altRightHanded (Action.instCategory.id Fermion.rightHanded)).hom)
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded).V
--           (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--         ((Action.instBraidedCategory (ModuleCat Complex) (Matrix.SpecialLinearGroup (Fin 2) Complex)).braiding
--               Fermion.rightHanded Fermion.altRightHanded).hom.hom)
--       (((fun X Y => LinearMap.instFunLike)
--             (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--             (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded).V).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.rightAltRightUnit.hom) 1)))

-- Source: PhysLean (Fermion.leftAltBi)
-- [complex signature, not re-axiomatized]
-- fermion_leftaltbi : LinearMap (RingHom.id Complex) Fermion.leftHanded.V.carrier
--   (LinearMap (RingHom.id Complex) Fermion.altLeftHanded.V.carrier Complex)

-- Source: PhysLean (Fermion.altRightBasis.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_altrightbasis_eq_1 : Eq Fermion.altRightBasis (Module.Basis.ofEquivFun (Equiv.linearEquiv Complex Fermion.AltRightHandedModule.toFin2ℂFun))

-- Source: PhysLean (Fermion.LeftHandedModule.ctorIdx)
-- [complex signature, not re-axiomatized]
-- fermion_lefthandedmodule_ctoridx : Fermion.LeftHandedModule → Nat

-- Source: PhysLean (Fermion.RightHandedModule.toFin2ℂEquiv_symm_apply_val)
-- [complex signature, not re-axiomatized]
-- fermion_righthandedmodule_tofin2ℂequiv_symm_apply_val : ∀ (a : Fin 2 → Complex) (a_1 : Fin 2),
--   Eq ((EquivLike.toFunLike.coe Fermion.RightHandedModule.toFin2ℂEquiv.symm a).val a_1) (a a_1)

-- Source: PhysLean (Fermion.altLeftLeftToMatrix_symm_expand_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_altleftlefttomatrix_symm_expand_tmul : ∀ (M : Matrix (Fin 2) (Fin 2) Complex),
--   Eq (EquivLike.toFunLike.coe Fermion.altLeftLeftToMatrix.symm M)
--     (Finset.univ.sum fun i =>
--       Finset.univ.sum fun j =>
--         instHSMul.hSMul (M i j)
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altLeftBasis i)
--             (Module.Basis.instFunLike.coe Fermion.leftBasis j)))

-- Source: PhysLean (StandardModel.HiggsVec.stability_group_single)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsvec_stability_group_single : InformalLemma

-- Source: PhysLean (Fermion.rightMetric_apply_one)
-- [complex signature, not re-axiomatized]
-- fermion_rightmetric_apply_one : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.rightHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.rightMetric.hom) 1)
--   Fermion.rightMetricVal

-- Source: PhysLean (Fermion.LeftHandedModule.toFin2ℂ.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_lefthandedmodule_tofin2ℂ_eq_1 : ∀ (ψ : Fermion.LeftHandedModule), Eq ψ.toFin2ℂ (EquivLike.toFunLike.coe Fermion.LeftHandedModule.toFin2ℂEquiv ψ)

-- Source: PhysLean (Fermion.altLeftBasis_ρ_apply)
-- [complex signature, not re-axiomatized]
-- fermion_altleftbasis_ρ_apply : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex) (i j : Fin 2),
--   Eq
--     (EquivLike.toFunLike.coe (LinearMap.toMatrix Fermion.altLeftBasis Fermion.altLeftBasis)
--       (MonoidHom.instFunLike.coe Fermion.altLeftHanded.ρ M) i j)
--     ((Matrix.inv.inv M.val).transpose i j)

-- Source: PhysLean (Fermion.AltLeftHandedModule.instModuleComplex)
-- [complex signature, not re-axiomatized]
-- fermion_altlefthandedmodule_instmodulecomplex : Module Complex Fermion.AltLeftHandedModule

-- Source: PhysLean (Fermion.altLeftaltLeftToMatrix.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_altleftaltlefttomatrix_eq_1 : Eq Fermion.altLeftaltLeftToMatrix
--   (((Fermion.altLeftBasis.tensorProduct Fermion.altLeftBasis).repr.trans
--         (Finsupp.linearEquivFunOnFinite Complex Complex (Prod (Fin 2) (Fin 2)))).trans
--     (LinearEquiv.curry Complex Complex (Fin 2) (Fin 2)))

-- Source: PhysLean (Fermion.altRightAltRightToMatrix)
-- [complex signature, not re-axiomatized]
-- fermion_altrightaltrighttomatrix : LinearEquiv (RingHom.id Complex)
--   (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.altRightHanded).V.carrier
--   (Matrix (Fin 2) (Fin 2) Complex)

-- Source: PhysLean (StandardModel.HiggsField.inner_neg_right)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_inner_neg_right : ∀ (φ1 φ2 : StandardModel.HiggsField),
--   Eq
--     (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex.inner (SpaceTime → Complex) φ1
--       (ContMDiffSection.instNeg.neg φ2))
--     (Pi.instNeg.neg
--       (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex.inner (SpaceTime → Complex) φ1 φ2))

-- Source: PhysLean (Fermion.leftRightToMatrix_ρ)
-- [complex signature, not re-axiomatized]
-- fermion_leftrighttomatrix_ρ : ∀ (v : (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.rightHanded).V.carrier)
--   (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (EquivLike.toFunLike.coe Fermion.leftRightToMatrix
--       (LinearMap.instFunLike.coe
--         (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.leftHanded.ρ M)
--           (MonoidHom.instFunLike.coe Fermion.rightHanded.ρ M))
--         v))
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul M.val (EquivLike.toFunLike.coe Fermion.leftRightToMatrix v))
--       M.val.conjTranspose)

-- Source: PhysLean (Fermion.leftAltLeftUnit_apply_one)
-- [complex signature, not re-axiomatized]
-- fermion_leftaltleftunit_apply_one : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.leftAltLeftUnit.hom) 1)
--   Fermion.leftAltLeftUnitVal

-- Source: PhysLean (Fermion.altLeftLeftToMatrix)
-- [complex signature, not re-axiomatized]
-- fermion_altleftlefttomatrix : LinearEquiv (RingHom.id Complex)
--   (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded).V.carrier
--   (Matrix (Fin 2) (Fin 2) Complex)

-- Source: PhysLean (Fermion.metricRaw)
/-- The raw `2x2` matrix corresponding to the metric for fermions.  -/
axiom fermion_metricraw :
  Matrix (Fin 2) (Fin 2) Complex

-- Source: PhysLean (Fermion.altRightContraction_basis)
-- [complex signature, not re-axiomatized]
-- fermion_altrightcontraction_basis : ∀ (i j : Fin 2),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altRightContraction.hom)
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altRightBasis i)
--         (Module.Basis.instFunLike.coe Fermion.rightBasis j)))
--     (ite (Eq i.val j.val) 1 0)

-- Source: PhysLean (StandardModel.HiggsField.Potential.quadDiscrim)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_quaddiscrim : StandardModel.HiggsField.Potential → StandardModel.HiggsField → SpaceTime → Real

-- Source: PhysLean (Fermion.leftRightToMatrix)
-- [complex signature, not re-axiomatized]
-- fermion_leftrighttomatrix : LinearEquiv (RingHom.id Complex)
--   (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.rightHanded).V.carrier
--   (Matrix (Fin 2) (Fin 2) Complex)

-- Source: PhysLean (Fermion.rightAltRightUnit.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_rightaltrightunit_eq_1 : Eq Fermion.rightAltRightUnit
--   {
--     hom :=
--       ModuleCat.ofHom
--         {
--           toFun := fun a =>
--             have a' := a;
--             instHSMul.hSMul a' Fermion.rightAltRightUnitVal,
--           map_add' := Fermion.rightAltRightUnit._proof_1, map_smul' := Fermion.rightAltRightUnit._proof_2 },
--     comm := Fermion.rightAltRightUnit._proof_3 }

-- Source: PhysLean (StandardModel.HiggsField.Potential.isBounded_𝓵_nonneg)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_isbounded_𝓵_nonneg : ∀ (P : StandardModel.HiggsField.Potential), P.IsBounded → Real.instLE.le 0 P.𝓵

-- Source: PhysLean (Fermion.RightHandedModule.toFin2ℂ)
-- [complex signature, not re-axiomatized]
-- fermion_righthandedmodule_tofin2ℂ : Fermion.RightHandedModule → Fin 2 → Complex

-- Source: PhysLean (Fermion.altLeftAltRightToMatrix.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_altleftaltrighttomatrix_eq_1 : Eq Fermion.altLeftAltRightToMatrix
--   (((Fermion.altLeftBasis.tensorProduct Fermion.altRightBasis).repr.trans
--         (Finsupp.linearEquivFunOnFinite Complex Complex (Prod (Fin 2) (Fin 2)))).trans
--     (LinearEquiv.curry Complex Complex (Fin 2) (Fin 2)))

-- Source: PhysLean (StandardModel.HiggsField.toFin2ℂ_comp_toHiggsVec)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_tofin2ℂ_comp_tohiggsvec : ∀ (φ : StandardModel.HiggsField), Eq φ.toHiggsVec (ContMDiffSection.instDFunLike.coe φ)

-- Source: PhysLean (StandardModel.HiggsVec.instMulActionGaugeGroupI)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsvec_instmulactiongaugegroupi : MulAction StandardModel.GaugeGroupI StandardModel.HiggsVec

-- Source: PhysLean (StandardModel.HiggsField.Potential.eq_zero_iff_of_μSq_nonpos_𝓵_pos)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_eq_zero_iff_of_μsq_nonpos_𝓵_pos : ∀ (P : StandardModel.HiggsField.Potential),
--   Real.instLT.lt 0 P.𝓵 →
--     Real.instLE.le P.μ2 0 →
--       ∀ (φ : StandardModel.HiggsField) (x : SpaceTime),
--         Iff (Eq (P.toFun φ x) 0) (Eq (ContMDiffSection.instDFunLike.coe φ x) 0)

-- Source: PhysLean (Fermion.RightHandedModule.val)
-- [complex signature, not re-axiomatized]
-- fermion_righthandedmodule_val : Fermion.RightHandedModule → Fin 2 → Complex

-- Source: PhysLean (Fermion.altLeftAltRightToMatrix_symm_expand_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_altleftaltrighttomatrix_symm_expand_tmul : ∀ (M : Matrix (Fin 2) (Fin 2) Complex),
--   Eq (EquivLike.toFunLike.coe Fermion.altLeftAltRightToMatrix.symm M)
--     (Finset.univ.sum fun i =>
--       Finset.univ.sum fun j =>
--         instHSMul.hSMul (M i j)
--           (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.altLeftBasis i)
--             (Module.Basis.instFunLike.coe Fermion.altRightBasis j)))

-- Source: PhysLean (StandardModel.HiggsField.const)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_const : LinearMap (RingHom.id Real) StandardModel.HiggsVec StandardModel.HiggsField

-- Source: PhysLean (StandardModel.HiggsVec)
/-- The vector space `HiggsVec` is defined to be the complex Euclidean space of dimension 2.
For a given spacetime point a Higgs field gives a value in `HiggsVec`.  -/
axiom standardmodel_higgsvec :
  Type

-- Source: PhysLean (Fermion.AltRightHandedModule.toFin2ℂ)
-- [complex signature, not re-axiomatized]
-- fermion_altrighthandedmodule_tofin2ℂ : Fermion.AltRightHandedModule → Fin 2 → Complex

-- Source: PhysLean (Fermion.altLeftContraction_hom_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_altleftcontraction_hom_tmul : ∀ (φ : Fermion.altLeftHanded.V.carrier) (ψ : Fermion.leftHanded.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altLeftContraction.hom)
--       (TensorProduct.tmul Complex φ ψ))
--     (dotProduct (Fermion.AltLeftHandedModule.toFin2ℂ φ) (Fermion.LeftHandedModule.toFin2ℂ ψ))

-- Source: PhysLean (StandardModel.GaugeGroupQuot.ℤ₃.sizeOf_spec)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupquot_ℤ₃_sizeof_spec : Eq (StandardModel.GaugeGroupQuot._sizeOf_inst.sizeOf StandardModel.GaugeGroupQuot.ℤ₃) 1

-- Source: PhysLean (Fermion.rightRightToMatrix_ρ_symm)
-- [complex signature, not re-axiomatized]
-- fermion_rightrighttomatrix_ρ_symm : ∀ (v : Matrix (Fin 2) (Fin 2) Complex) (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (LinearMap.instFunLike.coe
--       (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.rightHanded.ρ M)
--         (MonoidHom.instFunLike.coe Fermion.rightHanded.ρ M))
--       (EquivLike.toFunLike.coe Fermion.rightRightToMatrix.symm v))
--     (EquivLike.toFunLike.coe Fermion.rightRightToMatrix.symm
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--         (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (M.val.map StarRing.toStarAddMonoid.star) v)
--         (M.val.map StarRing.toStarAddMonoid.star).transpose))

-- Source: PhysLean (Fermion.AltLeftHandedModule.toFin2ℂ)
-- [complex signature, not re-axiomatized]
-- fermion_altlefthandedmodule_tofin2ℂ : Fermion.AltLeftHandedModule → Fin 2 → Complex

-- Source: PhysLean (StandardModel.HiggsField.Potential.pos_𝓵_sol_exists_iff)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_pos_𝓵_sol_exists_iff : ∀ (P : StandardModel.HiggsField.Potential),
--   Real.instLT.lt 0 P.𝓵 →
--     ∀ (c : Real),
--       Iff (Exists fun φ => Exists fun x => Eq (P.toFun φ x) c)
--         (Or (And (Real.instLT.lt P.μ2 0) (Real.instLE.le 0 c))
--           (And (Real.instLE.le 0 P.μ2)
--             (Real.instLE.le (instHDiv.hDiv (Real.instNeg.neg (instHPow.hPow P.μ2 2)) (instHMul.hMul 4 P.𝓵)) c)))

-- Source: PhysLean (StandardModel.HiggsVec.gaugeGroupI_smul_norm)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsvec_gaugegroupi_smul_norm : ∀ (g : StandardModel.GaugeGroupI) (φ : StandardModel.HiggsVec),
--   Eq ((PiLp.instNorm 2 fun x => Complex).norm (instHSMul.hSMul g φ)) ((PiLp.instNorm 2 fun x => Complex).norm φ)

-- Source: PhysLean (Fermion.metricRaw_comm)
-- [complex signature, not re-axiomatized]
-- fermion_metricraw_comm : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul Fermion.metricRaw M.val)
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.inv.inv M.val).transpose Fermion.metricRaw)

-- Source: PhysLean (Fermion.altLeftLeftUnit.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_altleftleftunit_eq_1 : Eq Fermion.altLeftLeftUnit
--   {
--     hom :=
--       ModuleCat.ofHom
--         {
--           toFun := fun a =>
--             have a' := a;
--             instHSMul.hSMul a' Fermion.altLeftLeftUnitVal,
--           map_add' := Fermion.altLeftLeftUnit._proof_1, map_smul' := Fermion.altLeftLeftUnit._proof_2 },
--     comm := Fermion.altLeftLeftUnit._proof_3 }

-- Source: PhysLean (Fermion.AltRightHandedModule.toFin2ℂEquiv_apply)
-- [complex signature, not re-axiomatized]
-- fermion_altrighthandedmodule_tofin2ℂequiv_apply : ∀ (a : Fermion.AltRightHandedModule) (a_1 : Fin 2),
--   Eq (EquivLike.toFunLike.coe Fermion.AltRightHandedModule.toFin2ℂEquiv a a_1)
--     (EquivLike.toFunLike.coe Fermion.AltRightHandedModule.toFin2ℂFun a a_1)

-- Source: PhysLean (StandardModel.HiggsField.Potential.isMaxOn_iff_field_of_𝓵_neg)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_ismaxon_iff_field_of_𝓵_neg : ∀ (P : StandardModel.HiggsField.Potential),
--   Real.instLT.lt P.𝓵 0 →
--     ∀ (φ : StandardModel.HiggsField) (x : SpaceTime),
--       Iff
--         (IsMaxOn
--           (fun x =>
--             StandardModel.HiggsField.Potential.isMinOn_iff_of_μSq_nonpos_𝓵_pos.match_1 (fun x => Real) x fun φ x =>
--               P.toFun φ x)
--           Set.univ { fst := φ, snd := x })
--         (Or (And (Real.instLE.le P.μ2 0) (Eq (φ.normSq x) (instHDiv.hDiv P.μ2 (instHMul.hMul 2 P.𝓵))))
--           (And (Real.instLT.lt 0 P.μ2) (Eq (ContMDiffSection.instDFunLike.coe φ x) 0)))

-- Source: PhysLean (StandardModel.HiggsField.guage_orbit)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_guage_orbit : InformalLemma

-- Source: PhysLean (StandardModel.HiggsField.inner_apply)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_inner_apply : ∀ (φ1 φ2 : StandardModel.HiggsField) (x : SpaceTime),
--   Eq (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex.inner (SpaceTime → Complex) φ1 φ2 x)
--     ((PiLp.innerProductSpace fun x => Complex).inner Complex (ContMDiffSection.instDFunLike.coe φ1 x)
--       (ContMDiffSection.instDFunLike.coe φ2 x))

-- Source: PhysLean (StandardModel.HiggsVec.mem_orbit_gaugeGroupI_iff)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsvec_mem_orbit_gaugegroupi_iff : ∀ (φ ψ : StandardModel.HiggsVec),
--   Iff (Set.instMembership.mem (MulAction.orbit StandardModel.GaugeGroupI φ) ψ)
--     (Eq ((PiLp.instNorm 2 fun x => Complex).norm ψ) ((PiLp.instNorm 2 fun x => Complex).norm φ))

-- Source: PhysLean (StandardModel.HiggsField.inner_smooth)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_inner_smooth : ∀ (φ1 φ2 : StandardModel.HiggsField),
--   ContMDiff (modelWithCornersSelf Real SpaceTime) (modelWithCornersSelf Real Complex) WithTop.top.top
--     (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex.inner (SpaceTime → Complex) φ1 φ2)

-- Source: PhysLean (Fermion.leftMetricVal.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_leftmetricval_eq_1 : Eq Fermion.leftMetricVal (EquivLike.toFunLike.coe Fermion.leftLeftToMatrix.symm (Matrix.neg.neg Fermion.metricRaw))

-- Source: PhysLean (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_instinnerforallspacetimeofnatnatcomplex : Inner (SpaceTime → Complex) StandardModel.HiggsField

-- Source: PhysLean (StandardModel.HiggsField.Potential.isBounded_of_𝓵_pos)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_isbounded_of_𝓵_pos : ∀ (P : StandardModel.HiggsField.Potential), Real.instLT.lt 0 P.𝓵 → P.IsBounded

-- Source: PhysLean (StandardModel.gaugeGroupℤ₃SubGroup)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupℤ₃subgroup : InformalDefinition

-- Source: PhysLean (StandardModel.HiggsVec.orthonormBasis)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsvec_orthonormbasis : OrthonormalBasis (Fin 2) Complex StandardModel.HiggsVec

-- Source: PhysLean (Fermion.LeftHandedModule.toFin2ℂFun)
-- [complex signature, not re-axiomatized]
-- fermion_lefthandedmodule_tofin2ℂfun : Equiv Fermion.LeftHandedModule (Fin 2 → Complex)

-- Source: PhysLean (StandardModel.HiggsField.Potential.neg)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_neg : StandardModel.HiggsField.Potential → StandardModel.HiggsField.Potential

-- Source: PhysLean (StandardModel.GaugeGroupQuot.I.elim)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupquot_i_elim : {motive : StandardModel.GaugeGroupQuot → Sort u} →
--   (t : StandardModel.GaugeGroupQuot) → Eq t.ctorIdx 3 → motive StandardModel.GaugeGroupQuot.I → motive t

-- Source: PhysLean (Fermion.altLeftContraction)
-- [complex signature, not re-axiomatized]
-- fermion_altleftcontraction : Action.instCategory.Hom (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded)
--   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))

-- Source: PhysLean (StandardModel.HiggsVec.toRealGroupElem_smul_self)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsvec_torealgroupelem_smul_self : ∀ (φ : StandardModel.HiggsVec),
--   Eq (instHSMul.hSMul φ.toRealGroupElem φ)
--     (StandardModel.HiggsVec.ofReal (instHPow.hPow ((PiLp.instNorm 2 fun x => Complex).norm φ) 2))

-- Source: PhysLean (Fermion.rightBasis_toFin2ℂ)
-- [complex signature, not re-axiomatized]
-- fermion_rightbasis_tofin2ℂ : ∀ (i : Fin 2),
--   Eq (Fermion.RightHandedModule.toFin2ℂ (Module.Basis.instFunLike.coe Fermion.rightBasis i)) (Pi.single i 1)

-- Source: PhysLean (StandardModel.HiggsField.Potential.quadDiscrim_eq_sqrt_mul_sqrt)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_quaddiscrim_eq_sqrt_mul_sqrt : ∀ (P : StandardModel.HiggsField.Potential),
--   Ne P.𝓵 0 →
--     ∀ (φ : StandardModel.HiggsField) (x : SpaceTime),
--       Eq (P.quadDiscrim φ x) (instHMul.hMul (P.quadDiscrim φ x).sqrt (P.quadDiscrim φ x).sqrt)

-- Source: PhysLean (StandardModel.gaugeGroupℤ₆SubGroup)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupℤ₆subgroup : [inst : Group StandardModel.GaugeGroupI] → Subgroup StandardModel.GaugeGroupI

-- Source: PhysLean (Fermion.LeftHandedModule.instAddCommGroup)
-- [complex signature, not re-axiomatized]
-- fermion_lefthandedmodule_instaddcommgroup : AddCommGroup Fermion.LeftHandedModule

-- Source: PhysLean (StandardModel.HiggsField.normSq_expand)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_normsq_expand : ∀ (φ : StandardModel.HiggsField),
--   Eq φ.normSq fun x =>
--     (instHAdd.hAdd
--         (instHMul.hMul
--           (RingHom.instFunLike.coe (starRingEnd ((fun x => Complex) 0))
--             ((ContMDiffSection.instDFunLike.coe φ x).ofLp 0))
--           ((ContMDiffSection.instDFunLike.coe φ x).ofLp 0))
--         (instHMul.hMul
--           (RingHom.instFunLike.coe (starRingEnd ((fun x => Complex) 1))
--             ((ContMDiffSection.instDFunLike.coe φ x).ofLp 1))
--           ((ContMDiffSection.instDFunLike.coe φ x).ofLp 1))).re

-- Source: PhysLean (Fermion.contr_rightAltRightUnit)
-- [complex signature, not re-axiomatized]
-- fermion_contr_rightaltrightunit : ∀ (x : Fermion.altRightHanded.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj
--               (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--               Fermion.altRightHanded).V
--           Fermion.altRightHanded.V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--         (Action.instMonoidalCategory.leftUnitor Fermion.altRightHanded).hom.hom)
--       (((fun X Y => LinearMap.instFunLike)
--             (Action.instMonoidalCategory.tensorObj
--                 (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded)
--                 Fermion.altRightHanded).V
--             (Action.instMonoidalCategory.tensorObj
--                 (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--                 Fermion.altRightHanded).V).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--           (Action.instMonoidalCategory.whiskerRight Fermion.altRightContraction Fermion.altRightHanded).hom)
--         (((fun X Y => LinearMap.instFunLike)
--               (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded
--                   (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded)).V
--               (Action.instMonoidalCategory.tensorObj
--                   (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded)
--                   Fermion.altRightHanded).V).coe
--           ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--             (Action.instMonoidalCategory.associator Fermion.altRightHanded Fermion.rightHanded
--                   Fermion.altRightHanded).inv.hom)
--           (TensorProduct.tmul Complex x
--             (((fun X Y => LinearMap.instFunLike)
--                   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                   (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded).V).coe
--               ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.rightAltRightUnit.hom) 1)))))
--     x

-- Source: PhysLean (StandardModel.HiggsField.toHiggsVec_smooth)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_tohiggsvec_smooth : ∀ (φ : StandardModel.HiggsField),
--   ContMDiff (modelWithCornersSelf Real SpaceTime) (modelWithCornersSelf Real StandardModel.HiggsVec) WithTop.top.top
--     φ.toHiggsVec

-- Source: PhysLean (StandardModel.HiggsField.const_apply)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_const_apply : ∀ (φ : StandardModel.HiggsVec) (x : SpaceTime),
--   Eq (ContMDiffSection.instDFunLike.coe (LinearMap.instFunLike.coe StandardModel.HiggsField.const φ) x) φ

-- Source: PhysLean (StandardModel.HiggsVec.stability_group)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsvec_stability_group : InformalLemma

-- Source: PhysLean (Fermion.AltRightHandedModule.val)
-- [complex signature, not re-axiomatized]
-- fermion_altrighthandedmodule_val : Fermion.AltRightHandedModule → Fin 2 → Complex

-- Source: PhysLean (Fermion.altRightRightToMatrix)
-- [complex signature, not re-axiomatized]
-- fermion_altrightrighttomatrix : LinearEquiv (RingHom.id Complex)
--   (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded).V.carrier
--   (Matrix (Fin 2) (Fin 2) Complex)

-- Source: PhysLean (StandardModel.GaugeGroupI.star_toSU3)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupi_star_tosu3 : ∀ (g : StandardModel.GaugeGroupI),
--   Eq (MonoidHom.instFunLike.coe StandardModel.GaugeGroupI.toSU3 (StandardModel.GaugeGroupI.instStar.star g))
--     (Matrix.instStarMulSubtypeMemSubmonoidSpecialUnitaryGroup.star
--       (MonoidHom.instFunLike.coe StandardModel.GaugeGroupI.toSU3 g))

-- Source: PhysLean (StandardModel.HiggsVec.toRealGroupElem.eq_1)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsvec_torealgroupelem_eq_1 : ∀ (φ : StandardModel.HiggsVec),
--   Eq φ.toRealGroupElem
--     (if hφ : Eq φ 0 then 1
--     else
--       have h0 := ⋯;
--       have h0' := ⋯;
--       { fst := 1,
--         snd :=
--           {
--             fst :=
--               ⟨EquivLike.toFunLike.coe Matrix.of
--                   (Matrix.vecCons
--                     (Matrix.vecCons
--                       (instHDiv.hDiv (RingHom.instFunLike.coe (starRingEnd ((fun x => Complex) 0)) (φ.ofLp 0))
--                         (Complex.ofReal ((PiLp.instNorm 2 fun x => Complex).norm φ)))
--                       (Matrix.vecCons
--                         (instHDiv.hDiv (RingHom.instFunLike.coe (starRingEnd ((fun x => Complex) 1)) (φ.ofLp 1))
--                           (Complex.ofReal ((PiLp.instNorm 2 fun x => Complex).norm φ)))
--                         Matrix.vecEmpty))
--                     (Matrix.vecCons
--                       (Matrix.vecCons
--                         (instHDiv.hDiv (Complex.instNeg.neg (φ.ofLp 1))
--                           (Complex.ofReal ((PiLp.instNorm 2 fun x => Complex).norm φ)))
--                         (Matrix.vecCons
--                           (instHDiv.hDiv (φ.ofLp 0) (Complex.ofReal ((PiLp.instNorm 2 fun x => Complex).norm φ)))
--                           Matrix.vecEmpty))
--                       Matrix.vecEmpty)),
--                 ⋯⟩,
--             snd := 1 } })

-- Source: PhysLean (Fermion.leftRightToMatrix_ρ_symm_selfAdjoint)
-- [complex signature, not re-axiomatized]
-- fermion_leftrighttomatrix_ρ_symm_selfadjoint : ∀ (v : Matrix (Fin 2) (Fin 2) Complex) (hv : IsSelfAdjoint v) (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (LinearMap.instFunLike.coe
--       (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.leftHanded.ρ M)
--         (MonoidHom.instFunLike.coe Fermion.rightHanded.ρ M))
--       (EquivLike.toFunLike.coe Fermion.leftRightToMatrix.symm v))
--     (EquivLike.toFunLike.coe Fermion.leftRightToMatrix.symm
--       (LinearMap.instFunLike.coe (Lorentz.SL2C.toSelfAdjointMap M) ⟨v, hv⟩).val)

-- Source: PhysLean (StandardModel.HiggsField.«_aux_PhysLean_Particles_StandardModel_HiggsBoson_Basic___macroRules_StandardModel_HiggsField_term‖_‖_H^2_1»)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_«_aux_physlean_particles_standardmodel_higgsboson_basic___macrorules_standardmodel_higgsfield_term‖_‖_h^2_1» : Lean.Macro

-- Source: PhysLean (Fermion.leftLeftToMatrix)
-- [complex signature, not re-axiomatized]
-- fermion_leftlefttomatrix : LinearEquiv (RingHom.id Complex) (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.leftHanded).V.carrier
--   (Matrix (Fin 2) (Fin 2) Complex)

-- Source: PhysLean (Fermion.contr_altRightRightUnit)
-- [complex signature, not re-axiomatized]
-- fermion_contr_altrightrightunit : ∀ (x : Fermion.rightHanded.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj
--               (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--               Fermion.rightHanded).V
--           Fermion.rightHanded.V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--         (Action.instMonoidalCategory.leftUnitor Fermion.rightHanded).hom.hom)
--       (((fun X Y => LinearMap.instFunLike)
--             (Action.instMonoidalCategory.tensorObj
--                 (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded)
--                 Fermion.rightHanded).V
--             (Action.instMonoidalCategory.tensorObj
--                 (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--                 Fermion.rightHanded).V).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--           (Action.instMonoidalCategory.whiskerRight Fermion.rightAltContraction Fermion.rightHanded).hom)
--         (((fun X Y => LinearMap.instFunLike)
--               (Action.instMonoidalCategory.tensorObj Fermion.rightHanded
--                   (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded)).V
--               (Action.instMonoidalCategory.tensorObj
--                   (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded)
--                   Fermion.rightHanded).V).coe
--           ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--             (Action.instMonoidalCategory.associator Fermion.rightHanded Fermion.altRightHanded
--                   Fermion.rightHanded).inv.hom)
--           (TensorProduct.tmul Complex x
--             (((fun X Y => LinearMap.instFunLike)
--                   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                   (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded).V).coe
--               ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altRightRightUnit.hom) 1)))))
--     x

-- Source: PhysLean (StandardModel.HiggsField.apply_im_smooth)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_apply_im_smooth : ∀ (φ : StandardModel.HiggsField) (i : Fin 2),
--   ContMDiff (modelWithCornersSelf Real SpaceTime) (modelWithCornersSelf Real Real) WithTop.top.top
--     (Function.comp (ContinuousLinearMap.funLike.coe Complex.imCLM) fun x =>
--       (ContMDiffSection.instDFunLike.coe φ x).ofLp i)

-- Source: PhysLean (StandardModel.HiggsVec.ofReal_normSq)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsvec_ofreal_normsq : ∀ {a : Real},
--   Real.instLE.le 0 a →
--     Eq (instHPow.hPow ((PiLp.instNorm 2 fun x => Complex).norm (StandardModel.HiggsVec.ofReal a)) 2) a

-- Source: PhysLean (Fermion.leftBasis_toFin2ℂ)
-- [complex signature, not re-axiomatized]
-- fermion_leftbasis_tofin2ℂ : ∀ (i : Fin 2), Eq (Fermion.LeftHandedModule.toFin2ℂ (Module.Basis.instFunLike.coe Fermion.leftBasis i)) (Pi.single i 1)

-- Source: PhysLean (StandardModel.HiggsField.Potential.neg_𝓵_quadDiscrim_zero_bound)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_neg_𝓵_quaddiscrim_zero_bound : ∀ (P : StandardModel.HiggsField.Potential),
--   Real.instLT.lt P.𝓵 0 →
--     ∀ (φ : StandardModel.HiggsField) (x : SpaceTime),
--       Real.instLE.le (P.toFun φ x) (instHDiv.hDiv (Real.instNeg.neg (instHPow.hPow P.μ2 2)) (instHMul.hMul 4 P.𝓵))

-- Source: PhysLean (StandardModel.fundamentalSU2)
/-- The fundamental representation of SU(2) as a homomorphism to `unitaryGroup (Fin 2) ℂ`.  -/
axiom standardmodel_fundamentalsu2 :
  MonoidHom (Subtype fun x => SetLike.instMembership.mem (Matrix.specialUnitaryGroup (Fin 2) Complex) x)
  (Subtype fun x => SetLike.instMembership.mem (Matrix.unitaryGroup (Fin 2) Complex) x)

-- Source: PhysLean (Fermion.altLeftHanded)
/-- The vector space ℂ^2 carrying the representation of SL(2,C) given by
M → (M⁻¹)ᵀ. In index notation corresponds to a Weyl fermion with indices ψ_a.  -/
axiom fermion_altlefthanded :
  Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)

-- Source: PhysLean (StandardModel.GaugeGroupQuot.I.sizeOf_spec)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupquot_i_sizeof_spec : Eq (StandardModel.GaugeGroupQuot._sizeOf_inst.sizeOf StandardModel.GaugeGroupQuot.I) 1

-- Source: PhysLean (Fermion.altLeftLeftToMatrix_ρ_symm)
-- [complex signature, not re-axiomatized]
-- fermion_altleftlefttomatrix_ρ_symm : ∀ (v : Matrix (Fin 2) (Fin 2) Complex) (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (LinearMap.instFunLike.coe
--       (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.altLeftHanded.ρ M)
--         (MonoidHom.instFunLike.coe Fermion.leftHanded.ρ M))
--       (EquivLike.toFunLike.coe Fermion.altLeftLeftToMatrix.symm v))
--     (EquivLike.toFunLike.coe Fermion.altLeftLeftToMatrix.symm
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--         (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.inv.inv M.val).transpose v) M.val.transpose))

-- Source: PhysLean (Fermion.rightAltRightToMatrix)
-- [complex signature, not re-axiomatized]
-- fermion_rightaltrighttomatrix : LinearEquiv (RingHom.id Complex)
--   (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded).V.carrier
--   (Matrix (Fin 2) (Fin 2) Complex)

-- Source: PhysLean (StandardModel.repU1_apply_coe)
-- [complex signature, not re-axiomatized]
-- standardmodel_repu1_apply_coe : ∀ (g : Subtype fun x => SetLike.instMembership.mem (unitary Complex) x),
--   Eq (MonoidHom.instFunLike.coe StandardModel.repU1 g).val (instHSMul.hSMul (instHPow.hPow g 3) 1)

-- Source: PhysLean (Fermion.altLeftaltLeftToMatrix_ρ)
-- [complex signature, not re-axiomatized]
-- fermion_altleftaltlefttomatrix_ρ : ∀ (v : (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.altLeftHanded).V.carrier)
--   (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (EquivLike.toFunLike.coe Fermion.altLeftaltLeftToMatrix
--       (LinearMap.instFunLike.coe
--         (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.altLeftHanded.ρ M)
--           (MonoidHom.instFunLike.coe Fermion.altLeftHanded.ρ M))
--         v))
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.inv.inv M.val).transpose
--         (EquivLike.toFunLike.coe Fermion.altLeftaltLeftToMatrix v))
--       (Matrix.inv.inv M.val))

-- Source: PhysLean (Fermion.altRightContraction)
-- [complex signature, not re-axiomatized]
-- fermion_altrightcontraction : Action.instCategory.Hom (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded)
--   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))

-- Source: PhysLean (StandardModel.repU1_fundamentalSU2_commute)
-- [complex signature, not re-axiomatized]
-- standardmodel_repu1_fundamentalsu2_commute : ∀ (u1 : Subtype fun x => SetLike.instMembership.mem (unitary Complex) x)
--   (g : Subtype fun x => SetLike.instMembership.mem (Matrix.specialUnitaryGroup (Fin 2) Complex) x),
--   Eq
--     (instHMul.hMul (MonoidHom.instFunLike.coe StandardModel.repU1 u1)
--       (MonoidHom.instFunLike.coe StandardModel.fundamentalSU2 g))
--     (instHMul.hMul (MonoidHom.instFunLike.coe StandardModel.fundamentalSU2 g)
--       (MonoidHom.instFunLike.coe StandardModel.repU1 u1))

-- Source: PhysLean (Fermion.AltRightHandedModule.instAddCommGroup)
-- [complex signature, not re-axiomatized]
-- fermion_altrighthandedmodule_instaddcommgroup : AddCommGroup Fermion.AltRightHandedModule

-- Source: PhysLean (StandardModel.repU1)
/-- The 2d representation of U(1) with charge 3 as a homomorphism
from U(1) to `unitaryGroup (Fin 2) ℂ`.  -/
axiom standardmodel_repu1 :
  MonoidHom (Subtype fun x => SetLike.instMembership.mem (unitary Complex) x)
  (Subtype fun x => SetLike.instMembership.mem (Matrix.unitaryGroup (Fin 2) Complex) x)

-- Source: PhysLean (Fermion.altRightRightUnitVal)
-- [complex signature, not re-axiomatized]
-- fermion_altrightrightunitval : (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded).V.carrier

-- Source: PhysLean (StandardModel.GaugeGroupI.star_toSU2)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupi_star_tosu2 : ∀ (g : StandardModel.GaugeGroupI),
--   Eq (MonoidHom.instFunLike.coe StandardModel.GaugeGroupI.toSU2 (StandardModel.GaugeGroupI.instStar.star g))
--     (Matrix.instStarMulSubtypeMemSubmonoidSpecialUnitaryGroup.star
--       (MonoidHom.instFunLike.coe StandardModel.GaugeGroupI.toSU2 g))

-- Source: PhysLean (Fermion.altLeftBasis.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_altleftbasis_eq_1 : Eq Fermion.altLeftBasis (Module.Basis.ofEquivFun (Equiv.linearEquiv Complex Fermion.AltLeftHandedModule.toFin2ℂFun))

-- Source: PhysLean (Fermion.leftAltLeftUnit.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_leftaltleftunit_eq_1 : Eq Fermion.leftAltLeftUnit
--   {
--     hom :=
--       ModuleCat.ofHom
--         {
--           toFun := fun a =>
--             have a' := a;
--             instHSMul.hSMul a' Fermion.leftAltLeftUnitVal,
--           map_add' := Fermion.leftAltLeftUnit._proof_1, map_smul' := Fermion.leftAltLeftUnit._proof_2 },
--     comm := Fermion.leftAltLeftUnit._proof_3 }

-- Source: PhysLean (StandardModel.HiggsField.Potential.isMaxOn_iff_isMinOn_neg)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_ismaxon_iff_isminon_neg : ∀ (P : StandardModel.HiggsField.Potential) (φ : StandardModel.HiggsField) (x : SpaceTime),
--   Iff
--     (IsMaxOn
--       (fun x =>
--         StandardModel.HiggsField.Potential.isMinOn_iff_of_μSq_nonpos_𝓵_pos.match_1 (fun x => Real) x fun φ x =>
--           P.toFun φ x)
--       Set.univ { fst := φ, snd := x })
--     (IsMinOn
--       (fun x =>
--         StandardModel.HiggsField.Potential.isMinOn_iff_of_μSq_nonpos_𝓵_pos.match_1 (fun x => Real) x fun φ x =>
--           P.neg.toFun φ x)
--       Set.univ { fst := φ, snd := x })

-- Source: PhysLean (Fermion.AltLeftHandedModule.toFin2ℂEquiv)
-- [complex signature, not re-axiomatized]
-- fermion_altlefthandedmodule_tofin2ℂequiv : LinearEquiv (RingHom.id Complex) Fermion.AltLeftHandedModule (Fin 2 → Complex)

-- Source: PhysLean (StandardModel.HiggsField.Potential.𝓵_neg)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_𝓵_neg : ∀ (P : StandardModel.HiggsField.Potential), Eq P.neg.𝓵 (Real.instNeg.neg P.𝓵)

-- Source: PhysLean (StandardModel.HiggsField.Potential.isMinOn_iff_of_μSq_nonneg_𝓵_pos)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_isminon_iff_of_μsq_nonneg_𝓵_pos : ∀ (P : StandardModel.HiggsField.Potential),
--   Real.instLT.lt 0 P.𝓵 →
--     Real.instLE.le 0 P.μ2 →
--       ∀ (φ : StandardModel.HiggsField) (x : SpaceTime),
--         Iff
--           (IsMinOn
--             (fun x =>
--               StandardModel.HiggsField.Potential.isMinOn_iff_of_μSq_nonpos_𝓵_pos.match_1 (fun x => Real) x fun φ x =>
--                 P.toFun φ x)
--             Set.univ { fst := φ, snd := x })
--           (Eq (P.toFun φ x) (instHDiv.hDiv (Real.instNeg.neg (instHPow.hPow P.μ2 2)) (instHMul.hMul 4 P.𝓵)))

-- Source: PhysLean (StandardModel.HiggsVec.ofReal.eq_1)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsvec_ofreal_eq_1 : ∀ (a : Real),
--   Eq (StandardModel.HiggsVec.ofReal a)
--     { ofLp := Matrix.vecCons (Complex.ofReal a.sqrt) (Matrix.vecCons 0 Matrix.vecEmpty) }

-- Source: PhysLean (StandardModel.HiggsVec.gaugeGroupI_smul_eq)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsvec_gaugegroupi_smul_eq : ∀ (g : StandardModel.GaugeGroupI) (φ : StandardModel.HiggsVec),
--   Eq (instHSMul.hSMul g φ)
--     {
--       ofLp :=
--         instHSMul.hSMul (instHPow.hPow (MonoidHom.instFunLike.coe StandardModel.GaugeGroupI.toU1 g) 3)
--           ((MonoidHom.instFunLike.coe StandardModel.GaugeGroupI.toSU2 g).val.mulVec φ.ofLp) }

-- Source: PhysLean (StandardModel.repU1Map)
/-- The 2d representation of U(1) with charge 3 as a map from U(1) to `unitaryGroup (Fin 2) ℂ`.  -/
axiom standardmodel_repu1map :
  (Subtype fun x => SetLike.instMembership.mem (unitary Complex) x) →
  Subtype fun x => SetLike.instMembership.mem (Matrix.unitaryGroup (Fin 2) Complex) x

-- Source: PhysLean (Fermion.leftAltContraction_hom_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_leftaltcontraction_hom_tmul : ∀ (ψ : Fermion.leftHanded.V.carrier) (φ : Fermion.altLeftHanded.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.leftAltContraction.hom)
--       (TensorProduct.tmul Complex ψ φ))
--     (dotProduct (Fermion.LeftHandedModule.toFin2ℂ ψ) (Fermion.AltLeftHandedModule.toFin2ℂ φ))

-- Source: PhysLean (StandardModel.GaugeGroup)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroup : InformalDefinition

-- Source: PhysLean (StandardModel.GaugeGroupI.toSU2.eq_1)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupi_tosu2_eq_1 : Eq StandardModel.GaugeGroupI.toSU2
--   { toFun := fun g => g.snd.fst, map_one' := StandardModel.GaugeGroupI.toSU2._proof_1,
--     map_mul' := StandardModel.GaugeGroupI.toSU2._proof_2 }

-- Source: PhysLean (Fermion.rightHandedWeylAltEquiv)
-- [complex signature, not re-axiomatized]
-- fermion_righthandedweylaltequiv : InformalDefinition

-- Source: PhysLean (StandardModel.HiggsField.Potential.μ2_neg)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_μ2_neg : ∀ (P : StandardModel.HiggsField.Potential), Eq P.neg.μ2 (Real.instNeg.neg P.μ2)

-- Source: PhysLean (Fermion.altRightContraction_hom_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_altrightcontraction_hom_tmul : ∀ (φ : Fermion.altRightHanded.V.carrier) (ψ : Fermion.rightHanded.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altRightContraction.hom)
--       (TensorProduct.tmul Complex φ ψ))
--     (dotProduct (Fermion.AltRightHandedModule.toFin2ℂ φ) (Fermion.RightHandedModule.toFin2ℂ ψ))

-- Source: PhysLean (Fermion.altRightHanded)
/-- The vector space ℂ^2 carrying the representation of SL(2,C) given by
M → (M⁻¹)^†.
In index notation this corresponds to a Weyl fermion with index `ψ_{dot a}`.  -/
axiom fermion_altrighthanded :
  Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)

-- Source: PhysLean (Fermion.rightRightToMatrix.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_rightrighttomatrix_eq_1 : Eq Fermion.rightRightToMatrix
--   (((Fermion.rightBasis.tensorProduct Fermion.rightBasis).repr.trans
--         (Finsupp.linearEquivFunOnFinite Complex Complex (Prod (Fin 2) (Fin 2)))).trans
--     (LinearEquiv.curry Complex Complex (Fin 2) (Fin 2)))

-- Source: PhysLean (Fermion.altRightRightToMatrix_ρ_symm)
-- [complex signature, not re-axiomatized]
-- fermion_altrightrighttomatrix_ρ_symm : ∀ (v : Matrix (Fin 2) (Fin 2) Complex) (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (LinearMap.instFunLike.coe
--       (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.altRightHanded.ρ M)
--         (MonoidHom.instFunLike.coe Fermion.rightHanded.ρ M))
--       (EquivLike.toFunLike.coe Fermion.altRightRightToMatrix.symm v))
--     (EquivLike.toFunLike.coe Fermion.altRightRightToMatrix.symm
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--         (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.inv.inv M.val).conjTranspose v)
--         (M.val.map StarRing.toStarAddMonoid.star).transpose))

-- Source: PhysLean (StandardModel.HiggsField.inner_self_eq_normSq)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_inner_self_eq_normsq : ∀ (φ : StandardModel.HiggsField) (x : SpaceTime),
--   Eq (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex.inner (SpaceTime → Complex) φ φ x)
--     (Complex.ofReal (φ.normSq x))

-- Source: PhysLean (Fermion.altRightRightUnit.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_altrightrightunit_eq_1 : Eq Fermion.altRightRightUnit
--   {
--     hom :=
--       ModuleCat.ofHom
--         {
--           toFun := fun a =>
--             have a' := a;
--             instHSMul.hSMul a' Fermion.altRightRightUnitVal,
--           map_add' := Fermion.altRightRightUnit._proof_1, map_smul' := Fermion.altRightRightUnit._proof_2 },
--     comm := Fermion.altRightRightUnit._proof_3 }

-- Source: PhysLean (Fermion.RightHandedModule.toFin2ℂEquiv_apply)
-- [complex signature, not re-axiomatized]
-- fermion_righthandedmodule_tofin2ℂequiv_apply : ∀ (a : Fermion.RightHandedModule) (a_1 : Fin 2),
--   Eq (EquivLike.toFunLike.coe Fermion.RightHandedModule.toFin2ℂEquiv a a_1)
--     (EquivLike.toFunLike.coe Fermion.RightHandedModule.toFin2ℂFun a a_1)

-- Source: PhysLean (StandardModel.GaugeGroupI.star_eq)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupi_star_eq : ∀ (g : StandardModel.GaugeGroupI),
--   Eq (StandardModel.GaugeGroupI.instStar.star g)
--     { fst := Matrix.instStarMulSubtypeMemSubmonoidSpecialUnitaryGroup.star g.fst,
--       snd :=
--         { fst := Matrix.instStarMulSubtypeMemSubmonoidSpecialUnitaryGroup.star g.snd.fst,
--           snd := Unitary.instStarSubtypeMemSubmonoidUnitary.star g.snd.snd } }

-- Source: PhysLean (Fermion.leftMetric_apply_one)
-- [complex signature, not re-axiomatized]
-- fermion_leftmetric_apply_one : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.leftHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.leftMetric.hom) 1)
--   Fermion.leftMetricVal

-- Source: PhysLean (StandardModel.GaugeGroupQuot.toCtorIdx)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupquot_toctoridx : StandardModel.GaugeGroupQuot → Nat

-- Source: PhysLean (StandardModel.gaugeGroupℤ₂SubGroup)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupℤ₂subgroup : InformalDefinition

-- Source: PhysLean (Fermion.comm_metricRaw)
-- [complex signature, not re-axiomatized]
-- fermion_comm_metricraw : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul M.val Fermion.metricRaw)
--     (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul Fermion.metricRaw (Matrix.inv.inv M.val).transpose)

-- Source: PhysLean (Fermion.rightAltContraction_tmul_symm)
-- [complex signature, not re-axiomatized]
-- fermion_rightaltcontraction_tmul_symm : ∀ (ψ : Fermion.rightHanded.V.carrier) (φ : Fermion.altRightHanded.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.altRightHanded).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.rightAltContraction.hom)
--       (TensorProduct.tmul Complex ψ φ))
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded).V
--           (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altRightContraction.hom)
--       (TensorProduct.tmul Complex φ ψ))

-- Source: PhysLean (Fermion.rightHandedWeylAltEquiv_equivariant)
-- [complex signature, not re-axiomatized]
-- fermion_righthandedweylaltequiv_equivariant : InformalLemma

-- Source: PhysLean (StandardModel.GaugeGroupI.instInvolutiveStar)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupi_instinvolutivestar : InvolutiveStar StandardModel.GaugeGroupI

-- Source: PhysLean (Fermion.leftMetricVal_expand_tmul)
-- [complex signature, not re-axiomatized]
-- fermion_leftmetricval_expand_tmul : Eq Fermion.leftMetricVal
--   (instHAdd.hAdd
--     (TensorProduct.neg.neg
--       (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.leftBasis 0)
--         (Module.Basis.instFunLike.coe Fermion.leftBasis 1)))
--     (TensorProduct.tmul Complex (Module.Basis.instFunLike.coe Fermion.leftBasis 1)
--       (Module.Basis.instFunLike.coe Fermion.leftBasis 0)))

-- Source: PhysLean (StandardModel.GaugeGroupℤ₃)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupℤ₃ : InformalDefinition

-- Source: PhysLean (Fermion.leftMetricVal)
-- [complex signature, not re-axiomatized]
-- fermion_leftmetricval : (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.leftHanded).V.carrier

-- Source: PhysLean (Fermion.altRightMetricVal.eq_1)
-- [complex signature, not re-axiomatized]
-- fermion_altrightmetricval_eq_1 : Eq Fermion.altRightMetricVal (EquivLike.toFunLike.coe Fermion.altRightAltRightToMatrix.symm Fermion.metricRaw)

-- Source: PhysLean (StandardModel.HiggsField.inner_symm)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_inner_symm : ∀ (φ1 φ2 : StandardModel.HiggsField),
--   Eq
--     (RingHom.instFunLike.coe (starRingEnd (SpaceTime → Complex))
--       (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex.inner (SpaceTime → Complex) φ2 φ1))
--     (StandardModel.HiggsField.instInnerForallSpaceTimeOfNatNatComplex.inner (SpaceTime → Complex) φ1 φ2)

-- Source: PhysLean (StandardModel.HiggsField.Potential.toFun)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_tofun : StandardModel.HiggsField.Potential → StandardModel.HiggsField → SpaceTime → Real

-- Source: PhysLean (Fermion.leftAltLeftUnit)
-- [complex signature, not re-axiomatized]
-- fermion_leftaltleftunit : Action.instCategory.Hom
--   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--   (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded)

-- Source: PhysLean (Fermion.altRightAltRightToMatrix_ρ_symm)
-- [complex signature, not re-axiomatized]
-- fermion_altrightaltrighttomatrix_ρ_symm : ∀ (v : Matrix (Fin 2) (Fin 2) Complex) (M : Matrix.SpecialLinearGroup (Fin 2) Complex),
--   Eq
--     (LinearMap.instFunLike.coe
--       (TensorProduct.map (MonoidHom.instFunLike.coe Fermion.altRightHanded.ρ M)
--         (MonoidHom.instFunLike.coe Fermion.altRightHanded.ρ M))
--       (EquivLike.toFunLike.coe Fermion.altRightAltRightToMatrix.symm v))
--     (EquivLike.toFunLike.coe Fermion.altRightAltRightToMatrix.symm
--       (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
--         (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (Matrix.inv.inv M.val).conjTranspose v)
--         (Matrix.inv.inv M.val).conjTranspose.transpose))

-- Source: PhysLean (Fermion.altRightRightUnit_apply_one)
-- [complex signature, not re-axiomatized]
-- fermion_altrightrightunit_apply_one : Eq
--   (((fun X Y => LinearMap.instFunLike)
--         (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--         (Action.instMonoidalCategory.tensorObj Fermion.altRightHanded Fermion.rightHanded).V).coe
--     ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altRightRightUnit.hom) 1)
--   Fermion.altRightRightUnitVal

-- Source: PhysLean (StandardModel.HiggsField.apply_smooth)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_apply_smooth : ∀ (φ : StandardModel.HiggsField) (i : Fin 2),
--   ContMDiff (modelWithCornersSelf Real SpaceTime) (modelWithCornersSelf Real Complex) WithTop.top.top fun x =>
--     (ContMDiffSection.instDFunLike.coe φ x).ofLp i

-- Source: PhysLean (StandardModel.HiggsField.Potential.pos_𝓵_toFun_pos)
-- [complex signature, not re-axiomatized]
-- standardmodel_higgsfield_potential_pos_𝓵_tofun_pos : ∀ (P : StandardModel.HiggsField.Potential),
--   Real.instLT.lt 0 P.𝓵 →
--     ∀ (φ : StandardModel.HiggsField) (x : SpaceTime),
--       Or (And (Real.instLT.lt P.μ2 0) (Real.instLE.le 0 (P.toFun φ x))) (Real.instLE.le 0 P.μ2)

-- Source: PhysLean (Fermion.contr_altLeftLeftUnit)
-- [complex signature, not re-axiomatized]
-- fermion_contr_altleftleftunit : ∀ (x : Fermion.leftHanded.V.carrier),
--   Eq
--     (((fun X Y => LinearMap.instFunLike)
--           (Action.instMonoidalCategory.tensorObj
--               (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--               Fermion.leftHanded).V
--           Fermion.leftHanded.V).coe
--       ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--         (Action.instMonoidalCategory.leftUnitor Fermion.leftHanded).hom.hom)
--       (((fun X Y => LinearMap.instFunLike)
--             (Action.instMonoidalCategory.tensorObj
--                 (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded) Fermion.leftHanded).V
--             (Action.instMonoidalCategory.tensorObj
--                 (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--                 Fermion.leftHanded).V).coe
--         ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--           (Action.instMonoidalCategory.whiskerRight Fermion.leftAltContraction Fermion.leftHanded).hom)
--         (((fun X Y => LinearMap.instFunLike)
--               (Action.instMonoidalCategory.tensorObj Fermion.leftHanded
--                   (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded)).V
--               (Action.instMonoidalCategory.tensorObj
--                   (Action.instMonoidalCategory.tensorObj Fermion.leftHanded Fermion.altLeftHanded)
--                   Fermion.leftHanded).V).coe
--           ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom
--             (Action.instMonoidalCategory.associator Fermion.leftHanded Fermion.altLeftHanded
--                   Fermion.leftHanded).inv.hom)
--           (TensorProduct.tmul Complex x
--             (((fun X Y => LinearMap.instFunLike)
--                   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex))).V
--                   (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.leftHanded).V).coe
--               ((ModuleCat.instConcreteCategoryLinearMapIdCarrier Complex).hom Fermion.altLeftLeftUnit.hom) 1)))))
--     x

-- Source: PhysLean (Fermion.altLeftMetric)
-- [complex signature, not re-axiomatized]
-- fermion_altleftmetric : Action.instCategory.Hom
--   (Action.instMonoidalCategory.tensorUnit (Rep Complex (Matrix.SpecialLinearGroup (Fin 2) Complex)))
--   (Action.instMonoidalCategory.tensorObj Fermion.altLeftHanded Fermion.altLeftHanded)

-- Source: PhysLean (StandardModel.GaugeGroupQuot.ctorElimType)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupquot_ctorelimtype : {motive : StandardModel.GaugeGroupQuot → Sort u} → Nat → Sort (max 1 u)

-- Source: PhysLean (Fermion.rightMetricVal)
-- [complex signature, not re-axiomatized]
-- fermion_rightmetricval : (Action.instMonoidalCategory.tensorObj Fermion.rightHanded Fermion.rightHanded).V.carrier

-- Source: PhysLean (Fermion.LeftHandedModule.toFin2ℂ)
-- [complex signature, not re-axiomatized]
-- fermion_lefthandedmodule_tofin2ℂ : Fermion.LeftHandedModule → Fin 2 → Complex

-- Source: PhysLean (Fermion.leftHandedAltTo)
-- [complex signature, not re-axiomatized]
-- fermion_lefthandedaltto : Action.instCategory.Hom Fermion.altLeftHanded Fermion.leftHanded

-- Source: PhysLean (Fermion.altLeftBi)
-- [complex signature, not re-axiomatized]
-- fermion_altleftbi : LinearMap (RingHom.id Complex) Fermion.altLeftHanded.V.carrier
--   (LinearMap (RingHom.id Complex) Fermion.leftHanded.V.carrier Complex)

-- Source: PhysLean (StandardModel.GaugeGroupI.toSU3)
-- [complex signature, not re-axiomatized]
-- standardmodel_gaugegroupi_tosu3 : MonoidHom StandardModel.GaugeGroupI
--   (Subtype fun x => SetLike.instMembership.mem (Matrix.specialUnitaryGroup (Fin 3) Complex) x)

end PhysicsGenerator.QuantumMechanics
