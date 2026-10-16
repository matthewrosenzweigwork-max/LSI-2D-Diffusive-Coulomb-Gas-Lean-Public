import LeanResearch.RepulsiveCoulomb.DbarBranchMollifierCR
import LeanResearch.RepulsiveCoulomb.DbarBranchMollifierRepresentation
import LeanResearch.RepulsiveCoulomb.DbarBranchLpLocalLimits
import Mathlib.Analysis.SpecificLimits.Basic

/-! Local holomorphic representatives of actual weak-kernel elements. The
proof uses a concrete shrinking bump sequence, the actual mollified L2 classes,
interior weak-equation preservation and the proved local L2-to-uniform bound. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

def coulombShrinkingBump {N : ℕ} {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ContDiffBump (0 : CoulombConfig N) where
  rIn := (r / ((n : ℝ) + 1)) / 2
  rOut := r / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := half_lt_self (by positivity)

theorem coulombShrinkingBump_rOut_le {N : ℕ} {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (coulombShrinkingBump (N := N) hr n).rOut ≤ r := by
  change r / ((n : ℝ) + 1) ≤ r
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [mul_nonneg hr.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem coulombShrinkingBump_rOut_tendsto {N : ℕ} {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => (coulombShrinkingBump (N := N) hr n).rOut) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul r
  simpa only [coulombShrinkingBump, mul_zero, div_eq_mul_inv, mul_one, one_mul] using h

theorem coulombShrinkingBump_interior_support {N : ℕ} {c z : CoulombConfig N}
    {r : ℝ} (hr : 0 < r) (n : ℕ) (hz : z ∈ ball c (3 * r)) :
    closedBall z (coulombShrinkingBump (N := N) hr n).rOut ⊆ closedBall c (4 * r) := by
  intro y hy
  have hsmall := coulombShrinkingBump_rOut_le (N := N) hr n
  rw [mem_closedBall] at hy ⊢
  rw [mem_ball] at hz
  exact (dist_triangle y z c).trans (by linarith)

theorem coulombWeakKernel_holomorphic_representative_ball {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (f : Lp ℂ 2 (coulombMeasure N β)) (hf : (f, 0) ∈ coulombMaxDbarGraph hβ)
    {c : CoulombConfig N} {r : ℝ} (hr : 0 < r)
    (hKΩ : closedBall c (4 * r) ⊆ coulombDomain N) :
    ∃ g : CoulombConfig N → ℂ, DifferentiableOn ℂ g (ball c r) ∧
      f =ᵐ[volume.restrict (ball c r)] g := by
  let K : Set (CoulombConfig N) := closedBall c (4 * r)
  have hK : IsCompact K := isCompact_closedBall _ _
  let v := coulombL2LocalizeVolume hβ hK hKΩ f
  let ψ : ℕ → ContDiffBump (0 : CoulombConfig N) := coulombShrinkingBump hr
  let u : ℕ → CoulombConfig N → ℂ := fun n => coulombScalarMollify K (ψ n) f
  let uL : ℕ → Lp ℂ 2 (volume : Measure (CoulombConfig N)) := fun n => coulombVolumeLpMollify (ψ n) v
  have hrep : ∀ n, uL n =ᵐ[volume] u n :=
    fun n => coulombScalarMollify_lp_coe hβ hK hKΩ (ψ n) f
  have hcont : ∀ n, Continuous (u n) :=
    fun n => (coulombScalarMollify_contDiff hβ hK hKΩ (ψ n) f).continuous
  have hholo : ∀ n, DifferentiableOn ℂ (u n) (ball c (3 * r)) := by
    intro n z hz
    exact (coulombScalarMollify_complex_differentiableAt hβ hK hKΩ (ψ n) f hf z
      (coulombShrinkingBump_interior_support hr n hz)).differentiableWithinAt
  have hL : Tendsto uL atTop (𝓝 v) :=
    coulombVolumeLpMollify_tendsto ψ (coulombShrinkingBump_rOut_tendsto hr) v
  obtain ⟨g, hg, hvg⟩ := coulomb_holomorphic_L2_local_limit uL v hrep hr hcont hholo hL
  have hvf : v =ᵐ[volume.restrict (ball c r)] f := by
    filter_upwards [ae_restrict_of_ae (coulombL2LocalizeVolume_coe hβ hK hKΩ f),
      ae_restrict_mem measurableSet_ball] with z hv hz
    rw [hv, indicator_of_mem]
    exact (ball_subset_closedBall (ball_subset_ball (by linarith : r ≤ 4 * r) hz))
  exact ⟨g, hg, hvf.symm.trans hvg⟩

theorem coulombWeakKernel_local_holomorphic_representative {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (f : Lp ℂ 2 (coulombMeasure N β)) (hf : (f, 0) ∈ coulombMaxDbarGraph hβ)
    (c : CoulombConfig N) (hc : c ∈ coulombDomain N) :
    ∃ r : ℝ, 0 < r ∧ ball c r ⊆ coulombDomain N ∧
      ∃ g : CoulombConfig N → ℂ, DifferentiableOn ℂ g (ball c r) ∧
        f =ᵐ[volume.restrict (ball c r)] g := by
  obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.mp (coulombDomain N).isOpen c hc
  let r : ℝ := R / 8
  have hr : 0 < r := by dsimp [r]; positivity
  have hKΩ : closedBall c (4 * r) ⊆ coulombDomain N :=
    (closedBall_subset_ball (by dsimp [r]; linarith)).trans hRΩ
  refine ⟨r, hr, ?_, coulombWeakKernel_holomorphic_representative_ball hβ f hf hr hKΩ⟩
  exact (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hKΩ

end RepulsiveCoulomb
