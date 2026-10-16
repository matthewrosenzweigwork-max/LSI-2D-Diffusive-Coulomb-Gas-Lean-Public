import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryRawWeakSystem
import Mathlib.Algebra.BigOperators.Option

/-! One common input and the actual scalar/raw exterior weak rows, followed
by the literal output transformation to the scalar adjoint and i<j exterior
error. No global integrability of Su is imposed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators LinearPMap
namespace RepulsiveCoulomb

abbrev CoulombAuxiliaryRawIndex (N : ℕ) := Option (Fin N × Fin N)
abbrev CoulombAuxiliaryJointIndex (N : ℕ) := Option (coulombPairs N)

def coulombAuxiliaryCutoffScalar {N : ℕ} {β R : ℝ} (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β)) :
    Lp ℂ 2 (coulombMeasure N β) :=
  coulombMetricCutoffL2L hR ℂ h - coulombCutoffAdjointErrorL β hR u

def coulombAuxiliaryRawSystemPrincipal {N : ℕ} (β : ℝ) :
    CoulombAuxiliaryRawIndex N → Fin N → (Fin N × Bool) → CoulombConfig N → ℂ
  | none => coulombAuxiliaryScalarDensityPrincipal
  | some p => coulombAuxiliaryRawCurlDensityPrincipal β p.1 p.2

def coulombAuxiliaryRawSystemSource {N : ℕ} {β R : ℝ} (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β)) :
    CoulombAuxiliaryRawIndex N → CoulombConfig N → ℂ
  | none => fun z => (coulombDensity N β z : ℂ) * coulombAuxiliaryCutoffScalar hR u h z
  | some p => coulombAuxiliaryCutoffRawSource R u p

theorem coulombAuxiliaryRawSystemSource_locallyIntegrable {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β))
    (a : CoulombAuxiliaryRawIndex N) :
    LocallyIntegrableOn (coulombAuxiliaryRawSystemSource hR u h a) (coulombDomain N) volume := by
  cases a with
  | none =>
      exact (coulombL2_locallyIntegrableOn hβ (coulombAuxiliaryCutoffScalar hR u h)).continuousOn_mul
        (fun z hz => (coulombComplexDensity_contDiffAt β hz).continuousAt.continuousWithinAt)
        (coulombDomain N).isOpen.isLocallyClosed
  | some p => exact coulombAuxiliaryCutoffRawSource_locallyIntegrable hβ hR u p

theorem coulombAuxiliaryCutoff_joint_raw_weakSystem {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    {u : Lp (CoulombConfig N) 2 (coulombMeasure N β)} {h : Lp ℂ 2 (coulombMeasure N β)}
    (huh : (u, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph)
    (hu : u ∈ coulombAuxiliaryCompatibility N hβ) :
    DbarLocalWeakDivergenceSystem (coulombAuxiliaryRawSystemPrincipal β)
      (fun (_ : CoulombAuxiliaryRawIndex N) (_ : Fin N) (_ : CoulombConfig N) => 0)
      (dbarSystemDirection N)
      (coulombDensityInputComponent β (coulombMetricCutoffL2L hR (CoulombConfig N) u))
      (coulombAuxiliaryRawSystemSource hR u h) := by
  have hs := coulombAuxiliaryDbarAdjoint_scalar_weakSystem hβ
    (coulombAuxiliaryDbarAdjoint_cutoff_graph hβ hR huh)
  have he := coulombAuxiliaryCompatibility_raw_weakSystem hβ hR hu
  intro a φ
  cases a with
  | none => exact hs () φ
  | some p => exact he p φ

def coulombAuxiliaryOutputMultiplier {N : ℕ} (β : ℝ) :
    CoulombAuxiliaryJointIndex N → CoulombAuxiliaryRawIndex N → CoulombConfig N → ℂ
  | none, none => fun z => (coulombDensity N β z : ℂ)⁻¹
  | some p, some a => fun z => coulombInverseRootMatrix z p.1.1 a.1 *
      coulombInverseRootMatrix z p.1.2 a.2
  | _, _ => fun _ => 0

theorem coulombAuxiliaryOutputMultiplier_contDiffAt {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (q : CoulombAuxiliaryJointIndex N) (a : CoulombAuxiliaryRawIndex N)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    ContDiffAt ℝ (⊤ : ℕ∞) (coulombAuxiliaryOutputMultiplier β q a) z := by
  cases q with
  | none =>
      cases a with
      | none =>
          apply (coulombComplexDensity_contDiffAt β hz).inv
          exact_mod_cast (ne_of_gt (coulombDensity_pos_off_collisions hβ hz))
      | some a => exact contDiffAt_const
  | some p =>
      cases a with
      | none => exact contDiffAt_const
      | some a =>
          exact (coulombInverseRootMatrix_entry_contDiffAt p.1.1 a.1 hz).mul
            (coulombInverseRootMatrix_entry_contDiffAt p.1.2 a.2 hz)

def coulombAuxiliaryCutoffJointOutput {N : ℕ} {β R : ℝ} (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β)) :
    CoulombAuxiliaryJointIndex N → CoulombConfig N → ℂ
  | none => coulombAuxiliaryCutoffScalar hR u h
  | some p => fun z => coulombCutoffExteriorError β hR u z p

theorem coulombAuxiliaryOutputMultiplier_source {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β))
    (q : CoulombAuxiliaryJointIndex N) :
    (fun z => ∑ a, coulombAuxiliaryOutputMultiplier β q a z *
      coulombAuxiliaryRawSystemSource hR u h a z) =ᵐ[volume]
        coulombAuxiliaryCutoffJointOutput hR u h q := by
  cases q with
  | none =>
      filter_upwards [coulombDomain_ae N] with z hz
      have hd : (coulombDensity N β z : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (coulombDensity_pos_off_collisions hβ hz))
      simp only [Fintype.sum_option, coulombAuxiliaryOutputMultiplier,
        coulombAuxiliaryRawSystemSource, coulombAuxiliaryCutoffJointOutput,
        zero_mul, Finset.sum_const_zero, add_zero, zero_add]
      rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  | some p =>
      filter_upwards [(coulombMeasure_ae_iff hβ).mp (coulombCutoffExteriorError_coe β hR u)] with z hz
      simp only [Fintype.sum_option, coulombAuxiliaryOutputMultiplier,
        coulombAuxiliaryRawSystemSource, coulombAuxiliaryCutoffJointOutput,
        zero_mul, zero_add, add_zero]
      rw [hz, coulombCutoffExteriorError_raw_pointwise hR z (u z) p]
      simp only [Fintype.sum_prod_type, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro k _
      change (coulombInverseRootMatrix z p.1.1 k * coulombInverseRootMatrix z p.1.2 l) *
        dbarVectorWedge (coulombDbar (fun x => (coulombMetricCutoff R x : ℂ)) z)
          (dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (u z)) k l = _
      ring

theorem coulombAuxiliaryCutoffJointOutput_memLp_volume {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (h : Lp ℂ 2 (coulombMeasure N β))
    (q : CoulombAuxiliaryJointIndex N) :
    MemLp (coulombAuxiliaryCutoffJointOutput hR u h q) 2 volume := by
  cases q with
  | none =>
      exact coulombCompactL2_memLp_volume hβ
        (coulombMetricCutoffSupport_isCompact N hR) (coulombMetricCutoffSupport_subset N hR)
        _ (coulombCutoffAdjointOutput_supported hR u h)
  | some p => exact ((coulombCutoffData_memLp_volume hβ hR u h).2.2).eval_piLp p

end RepulsiveCoulomb
