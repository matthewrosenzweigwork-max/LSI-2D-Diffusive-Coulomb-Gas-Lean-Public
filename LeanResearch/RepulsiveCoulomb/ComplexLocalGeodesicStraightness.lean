import LeanResearch.RepulsiveCoulomb.LocallyConstantSpeedInterval
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Tactic.Ring

/-! Local constant-speed Euclidean segments globalize on a compact interval.
The proof uses the actual finite-subdivision shortcut corner. Euclidean strict
convexity makes the two minimizing restrictions straight, and local minimizing
across their common point forces the same direction. No injectivity, global
distance formula, curvature certificate, or developing map is assumed. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- A locally constant-speed minimizing complex curve has the correct endpoint
 distance. A hypothetical shortcut contradicts Euclidean betweenness at the
 actual first nonminimizing subdivision corner. -/
theorem complex_locallyConstantSpeedInterval_endpoint_distance
    {c : ℝ} {γ : Icc (0 : ℝ) 1 → ℂ} (hγ : LocallyConstantSpeedInterval c γ) :
    dist (γ ⟨0, by norm_num⟩) (γ ⟨1, by norm_num⟩) = c := by
  apply le_antisymm
  · simpa only [sub_zero, abs_one, mul_one] using
      locallyConstantSpeedInterval_dist_le hγ ⟨0, by norm_num⟩ ⟨1, by norm_num⟩
  · by_contra h
    have hshort : dist (γ ⟨0, by norm_num⟩) (γ ⟨1, by norm_num⟩) < c :=
      lt_of_not_ge h
    have hc : 0 < c := lt_of_le_of_lt dist_nonneg hshort
    obtain ⟨u, v, hu, huv, hpre, hcell, hshortv⟩ :=
      exists_locallyConstantSpeedInterval_shortcut_corner hγ hshort
    obtain ⟨U, hU, huU, hdU⟩ := hγ u
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU u huU
    let δ : ℝ := min u.1 (min (v.1 - u.1) ε) / 2
    have huv' : u.1 < v.1 := huv
    have hδ : 0 < δ := by
      dsimp [δ]
      exact half_pos (lt_min hu (lt_min (sub_pos.mpr huv') hε))
    have hδu : δ < u.1 := by
      have hh := min_le_left u.1 (min (v.1 - u.1) ε)
      dsimp [δ]
      linarith
    have hδv : δ < v.1 - u.1 := by
      have hh := (min_le_right u.1 (min (v.1 - u.1) ε)).trans
        (min_le_left (v.1 - u.1) ε)
      dsimp [δ]
      linarith
    have hδε : δ < ε := by
      have hh := (min_le_right u.1 (min (v.1 - u.1) ε)).trans
        (min_le_right (v.1 - u.1) ε)
      dsimp [δ]
      linarith
    let s : Icc (0 : ℝ) 1 := ⟨u.1 - δ, by constructor <;> linarith [u.2.2]⟩
    let t : Icc (0 : ℝ) 1 := ⟨u.1 + δ, by constructor <;> linarith [u.2.1, v.2.2]⟩
    have hsu : s ≤ u := by change u.1 - δ ≤ u.1; linarith
    have hut : u ≤ t := by change u.1 ≤ u.1 + δ; linarith
    have htv : t ≤ v := by change u.1 + δ ≤ v.1; linarith
    have hsU : s ∈ U := by
      apply hball
      change |(u.1 - δ) - u.1| < ε
      rw [show (u.1 - δ) - u.1 = -δ by ring, abs_neg, abs_of_pos hδ]
      exact hδε
    have htU : t ∈ U := by
      apply hball
      change |(u.1 + δ) - u.1| < ε
      rw [show (u.1 + δ) - u.1 = δ by ring, abs_of_pos hδ]
      exact hδε
    have h0u : dist (γ ⟨0, by norm_num⟩) (γ u) = c * u.1 := by
      simpa only [sub_zero, abs_of_nonneg u.2.1] using
        hpre ⟨0, by norm_num⟩ u u.2.1 le_rfl
    have h0s : dist (γ ⟨0, by norm_num⟩) (γ s) = c * s.1 := by
      simpa only [sub_zero, abs_of_nonneg s.2.1] using
        hpre ⟨0, by norm_num⟩ s u.2.1 hsu
    have hsuD : dist (γ s) (γ u) = c * (u.1 - s.1) := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr (show s.1 ≤ u.1 from hsu))] using
        hpre s u hsu le_rfl
    have hutD : dist (γ u) (γ t) = c * (t.1 - u.1) := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr (show u.1 ≤ t.1 from hut))] using
        hdU u huU t htU
    have hstD : dist (γ s) (γ t) = c * (t.1 - s.1) := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr (show s.1 ≤ t.1 from hsu.trans hut))] using
        hdU s hsU t htU
    have htvD : dist (γ t) (γ v) = c * (v.1 - t.1) := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr (show t.1 ≤ v.1 from htv))] using
        hcell t ⟨hut, htv⟩ v ⟨huv.le, le_rfl⟩
    have huvD : dist (γ u) (γ v) = c * (v.1 - u.1) := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr (show u.1 ≤ v.1 from huv.le))] using
        hcell u ⟨le_rfl, huv.le⟩ v ⟨huv.le, le_rfl⟩
    have hleft : Wbtw ℝ (γ ⟨0, by norm_num⟩) (γ s) (γ u) := by
      apply dist_add_dist_eq_iff.mp
      rw [h0s, hsuD, h0u]
      ring
    have hcorner : Wbtw ℝ (γ s) (γ u) (γ t) := by
      apply dist_add_dist_eq_iff.mp
      rw [hsuD, hutD, hstD]
      ring
    have hright : Wbtw ℝ (γ u) (γ t) (γ v) := by
      apply dist_add_dist_eq_iff.mp
      rw [hutD, htvD, huvD]
      ring
    have hsu_ne : γ s ≠ γ u := by
      apply dist_pos.mp
      rw [hsuD]
      apply mul_pos hc
      change 0 < u.1 - (u.1 - δ)
      linarith
    have hut_ne : γ u ≠ γ t := by
      apply dist_pos.mp
      rw [hutD]
      apply mul_pos hc
      change 0 < (u.1 + δ) - u.1
      linarith
    have hfull : Wbtw ℝ (γ ⟨0, by norm_num⟩) (γ u) (γ v) :=
      (hleft.trans_expand_right hcorner hsu_ne).trans_expand_left hright hut_ne
    have hadd := dist_add_dist_eq_iff.mpr hfull
    rw [h0u, huvD] at hadd
    nlinarith

/-- The actual local Euclidean minimizing condition gives the full pairwise
 distance identity, including the zero-speed case. -/
theorem complex_locallyConstantSpeedInterval_distance
    {c : ℝ} {γ : Icc (0 : ℝ) 1 → ℂ} (hγ : LocallyConstantSpeedInterval c γ)
    (s t : Icc (0 : ℝ) 1) : dist (γ s) (γ t) = c * |t.1 - s.1| := by
  apply locallyConstantSpeedInterval_prefix_distance hγ ⟨1, by norm_num⟩
  · simpa only [mul_one] using complex_locallyConstantSpeedInterval_endpoint_distance hγ
  · exact s.2.2
  · exact t.2.2

/-- The parameter is preserved: a locally constant-speed minimizing complex
 curve is precisely the affine segment between its actual endpoints. -/
theorem complex_locallyConstantSpeedInterval_affine
    {c : ℝ} {γ : Icc (0 : ℝ) 1 → ℂ} (hγ : LocallyConstantSpeedInterval c γ)
    (t : Icc (0 : ℝ) 1) :
    γ t = AffineMap.lineMap (γ ⟨0, by norm_num⟩) (γ ⟨1, by norm_num⟩) t.1 := by
  apply eq_lineMap_of_dist_eq_mul_of_dist_eq_mul
  · rw [complex_locallyConstantSpeedInterval_distance hγ,
      complex_locallyConstantSpeedInterval_endpoint_distance hγ]
    simp only [sub_zero, abs_of_nonneg t.2.1]
    ring
  · rw [complex_locallyConstantSpeedInterval_distance hγ,
      complex_locallyConstantSpeedInterval_endpoint_distance hγ]
    rw [abs_of_nonneg (sub_nonneg.mpr t.2.2)]
    ring

end RepulsiveCoulomb
