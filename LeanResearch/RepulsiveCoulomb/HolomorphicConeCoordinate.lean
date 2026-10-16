module

public import LeanResearch.RepulsiveCoulomb.HolomorphicRadialEquation
public import LeanResearch.RepulsiveCoulomb.LocalHolomorphicLogarithm

@[expose] public section

/-! Analytic coordinate algebra for a cone density. This module first proves the
exact pullback identity from the proved radial differential equation. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

def holomorphicConeMap (α : ℝ) (p : ℂ) (L : ℂ → ℂ) (z : ℂ) : ℂ :=
  (z - p) * Complex.exp (L z / ((α + 1 : ℝ) : ℂ))

theorem holomorphicConeMap_hasDerivAt (α : ℝ) (p : ℂ) {L : ℂ → ℂ} {z : ℂ}
    (hL : DifferentiableAt ℂ L z) :
    HasDerivAt (holomorphicConeMap α p L)
      (Complex.exp (L z / ((α + 1 : ℝ) : ℂ)) + (z - p) *
        (Complex.exp (L z / ((α + 1 : ℝ) : ℂ)) * (deriv L z / ((α + 1 : ℝ) : ℂ)))) z := by
  convert ((hasDerivAt_id z).sub_const p).mul
    (hL.hasDerivAt.div_const ((α + 1 : ℝ) : ℂ)).cexp using 1
  · ext w
    simp [holomorphicConeMap]
  · simp

theorem holomorphicConeMap_norm_identity {α : ℝ} (hα : 0 ≤ α) (p : ℂ)
    {L : ℂ → ℂ} {z v : ℂ} (hL : DifferentiableAt ℂ L z)
    (heq : ((α + 1 : ℝ) : ℂ) * Complex.exp (L z) +
      (z - p) * (Complex.exp (L z) * deriv L z) = ((α + 1 : ℝ) : ℂ) * v) :
    ‖holomorphicConeMap α p L z‖ ^ α * ‖deriv (holomorphicConeMap α p L) z‖ =
      ‖z - p‖ ^ α * ‖v‖ := by
  let n : ℂ := ((α + 1 : ℝ) : ℂ)
  have hn : n ≠ 0 := by dsimp [n]; exact_mod_cast (show α + 1 ≠ 0 by linarith)
  let D := Complex.exp (L z / n)
  let E := Complex.exp ((α : ℂ) * (L z / n))
  have hDE : D * E = Complex.exp (L z) := by
    dsimp only [D, E]
    rw [← Complex.exp_add]
    congr 1
    have hrel : (1 : ℂ) + (α : ℂ) = n := by simp [n, add_comm]
    calc
      L z / n + (α : ℂ) * (L z / n) = (1 + (α : ℂ)) * (L z / n) := by ring
      _ = n * (L z / n) := by rw [hrel]
      _ = L z := by field_simp
  have hg : (1 + (z - p) * (deriv L z / n)) * Complex.exp (L z) = v := by
    apply mul_left_cancel₀ hn
    calc
      n * ((1 + (z - p) * (deriv L z / n)) * Complex.exp (L z)) =
          n * Complex.exp (L z) + (z - p) * (Complex.exp (L z) * deriv L z) := by
        field_simp
      _ = n * v := heq
  have hd : deriv (holomorphicConeMap α p L) z * E = v := by
    rw [(holomorphicConeMap_hasDerivAt α p hL).deriv]
    change (D + (z - p) * (D * (deriv L z / n))) * E = v
    calc
      _ = (1 + (z - p) * (deriv L z / n)) * (D * E) := by ring
      _ = v := by rw [hDE]; exact hg
  have hnorm : ‖D‖ ^ α = ‖E‖ := by
    dsimp only [D, E]
    rw [Complex.norm_exp, Complex.norm_exp, ← Real.exp_mul]
    congr 1
    simp [Complex.mul_re, mul_comm]
  have hprod : ‖holomorphicConeMap α p L z‖ ^ α = ‖z - p‖ ^ α * ‖E‖ := by
    rw [holomorphicConeMap, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    rw [hnorm]
  rw [hprod]
  calc
    _ = ‖z - p‖ ^ α * ‖deriv (holomorphicConeMap α p L) z * E‖ := by
      rw [norm_mul]
      ring
    _ = _ := by rw [hd]

/-- A genuine holomorphic coordinate with the exact cone-density pullback. -/
theorem exists_holomorphic_cone_coordinate_with_deriv {α : ℝ} (hα : 0 ≤ α) (p : ℂ)
    {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hg : AnalyticOnNhd ℂ g (ball p R)) (hg0 : g p ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, p ∈ e.source ∧ e p = 0 ∧ deriv e p ≠ 0 ∧
      e.source ⊆ ball p R ∧ ∀ z ∈ e.source,
        AnalyticAt ℂ e z ∧ ‖e z‖ ^ α * ‖deriv e z‖ = ‖z - p‖ ^ α * ‖g z‖ := by
  let A := holomorphicRadialAverage α p g
  have hA : AnalyticOnNhd ℂ A (ball p (R / 2)) := holomorphicRadialAverage_analyticOnNhd hα p hR hg
  have hAp : A p ≠ 0 := by simpa [A, holomorphicRadialAverage_center hα] using hg0
  obtain ⟨r, hr, hsub, L, hL, hexp⟩ := exists_holomorphic_log_on_subball
    (by linarith : 0 < R / 2) hA hAp
  let F := holomorphicConeMap α p L
  have hF : AnalyticOnNhd ℂ F (ball p r) := by
    intro z hz
    exact (analyticAt_id.sub analyticAt_const).mul ((hL z hz).div_const.cexp)
  have hFp : F p = 0 := by simp [F, holomorphicConeMap]
  have hFdp : deriv F p ≠ 0 := by
    have hd := (holomorphicConeMap_hasDerivAt α p (hL p (mem_ball_self hr)).differentiableAt).deriv
    simp only [sub_self, zero_mul, add_zero] at hd
    exact hd.trans_ne (Complex.exp_ne_zero _)
  have hidentity (z : ℂ) (hz : z ∈ ball p r) :
      ‖F z‖ ^ α * ‖deriv F z‖ = ‖z - p‖ ^ α * ‖g z‖ := by
    have hevent : (fun w ↦ Complex.exp (L w)) =ᶠ[𝓝 z] A := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      exact hexp w hw
    have hAd : deriv A z = Complex.exp (L z) * deriv L z := by
      rw [← hevent.deriv_eq, ((hL z hz).differentiableAt.hasDerivAt.cexp).deriv]
    have hode := holomorphicRadialAverage_equation hα p hR hg (hsub hz)
    change ((α + 1 : ℝ) : ℂ) * A z + (z - p) * deriv A z = _ at hode
    rw [hAd, ← hexp z hz] at hode
    exact holomorphicConeMap_norm_identity hα p (hL z hz).differentiableAt hode
  have hc : ContDiffAt ℂ 1 F p := (hF p (mem_ball_self hr)).contDiffAt
  have hs := (hc.hasStrictDerivAt one_ne_zero).hasStrictFDerivAt_equiv hFdp
  let e0 := hs.toOpenPartialHomeomorph F
  let e := e0.restrOpen (ball p r) isOpen_ball
  have hsource : e.source ⊆ ball p r := fun _ hz ↦ hz.2
  refine ⟨e, ⟨hs.mem_toOpenPartialHomeomorph_source, mem_ball_self hr⟩, hFp, hFdp,
    hsource.trans (hsub.trans (ball_subset_ball (by linarith))), ?_⟩
  intro z hz
  exact ⟨hF z (hsource hz), hidentity z (hsource hz)⟩

/-- The original public interface, retaining its exact statement. -/
theorem exists_holomorphic_cone_coordinate {α : ℝ} (hα : 0 ≤ α) (p : ℂ)
    {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hg : AnalyticOnNhd ℂ g (ball p R)) (hg0 : g p ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, p ∈ e.source ∧ e p = 0 ∧
      e.source ⊆ ball p R ∧ ∀ z ∈ e.source,
        AnalyticAt ℂ e z ∧ ‖e z‖ ^ α * ‖deriv e z‖ = ‖z - p‖ ^ α * ‖g z‖ := by
  obtain ⟨e, hep, he0, _, hsub, he⟩ := exists_holomorphic_cone_coordinate_with_deriv hα p hR hg hg0
  exact ⟨e, hep, he0, hsub, he⟩

end RepulsiveCoulomb
