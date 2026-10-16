module

public import LeanResearch.RepulsiveCoulomb.PointWeightLocalComparison
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

/-! Regularity off exactly the positive-exponent punctures, and actual local
integrability transfer. No uniform compact-set comparison constant is asserted.
-/
noncomputable section
open MeasureTheory Real Filter Set
open scoped ENNReal BigOperators Topology
namespace RepulsiveCoulomb

theorem pointPunctures_finite {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) :
    (pointPunctures a y).Finite := by
  apply (Set.finite_range y).subset
  rintro z ⟨j, _, rfl⟩
  exact ⟨j, rfl⟩

def pointDomain {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) : TopologicalSpace.Opens ℂ :=
  ⟨(pointPunctures a y)ᶜ, (pointPunctures_finite a y).isClosed.isOpen_compl⟩

theorem pointWeight_contDiffAt {m : ℕ} (γ : ℝ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ} (hz : z ∉ pointPunctures a y) :
    ContDiffAt ℝ ⊤ (pointWeight γ a y) z := by
  have hfactor (j : Fin m) : ContDiffAt ℝ ⊤ (fun x : ℂ ↦ ‖x - y j‖ ^ a j) z := by
    by_cases hj : a j = 0
    · simpa only [hj, Real.rpow_zero] using
        (contDiffAt_const : ContDiffAt ℝ ⊤ (fun _ : ℂ ↦ (1 : ℝ)) z)
    · have hpos : 0 < a j := lt_of_le_of_ne (ha j) (Ne.symm hj)
      have hzy : z - y j ≠ 0 := by
        intro heq
        exact hz ⟨j, hpos, sub_eq_zero.mp heq⟩
      exact ((contDiffAt_id.sub contDiffAt_const).norm ℂ hzy).rpow_const_of_ne
        (norm_ne_zero_iff.mpr hzy)
  have hprod : ContDiffAt ℝ ⊤ (fun x : ℂ ↦ ∏ j, ‖x - y j‖ ^ a j) z := by
    fun_prop
  have hgauss : ContDiffAt ℝ ⊤ (fun x : ℂ ↦ Real.exp (-γ * ‖x‖ ^ 2 / 2)) z := by
    have hre : ContDiffAt ℝ ⊤ (fun x : ℂ ↦ x.re) z := Complex.reCLM.contDiff.contDiffAt
    have him : ContDiffAt ℝ ⊤ (fun x : ℂ ↦ x.im) z := Complex.imCLM.contDiff.contDiffAt
    simp only [Complex.sq_norm, Complex.normSq_apply]
    fun_prop
  exact hgauss.mul hprod

theorem pointDensity_contDiffAt {m : ℕ} (γ : ℝ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ} (hz : z ∉ pointPunctures a y) :
    ContDiffAt ℝ ⊤ (pointDensity γ a y) z :=
  contDiffAt_const.mul (pointWeight_contDiffAt γ ha y hz)

theorem pointDensity_contDiffOn {m : ℕ} (γ : ℝ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    ContDiffOn ℝ ⊤ (pointDensity γ a y) (pointDomain a y) := by
  intro z hz
  exact (pointDensity_contDiffAt γ ha y hz).contDiffWithinAt

/-- Membership in any local Lp space is equivalent on a compact set avoiding
positive-exponent punctures. This concerns the same function and the actual
weighted measure, not a reinterpretation of a Haar weak derivative. -/
theorem pointMeasure_memLp_restrict_iff {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {K : Set ℂ} (hK : IsCompact K) (havoid : K ⊆ (pointPunctures a y)ᶜ)
    {F : Type*} [TopologicalSpace F] [ENorm F] (f : ℂ → F) (p : ENNReal) :
    MemLp f p ((pointMeasure γ a y).restrict K) ↔ MemLp f p (volume.restrict K) := by
  obtain ⟨c, C, hc, hC, hlo, hhi⟩ := pointMeasure_restrict_comparison hγ ha y hK havoid
  have hc0 : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hc)
  have hreverse : volume.restrict K ≤ (ENNReal.ofReal c)⁻¹ •
      (pointMeasure γ a y).restrict K := by
    have h := smul_le_smul_left (ENNReal.ofReal c)⁻¹ hlo
    simpa only [smul_smul, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_smul] using h
  exact ⟨fun hf ↦ hf.of_measure_le_smul (ENNReal.inv_ne_top.mpr hc0) hreverse,
    fun hf ↦ hf.of_measure_le_smul ENNReal.ofReal_ne_top hhi⟩

end RepulsiveCoulomb
