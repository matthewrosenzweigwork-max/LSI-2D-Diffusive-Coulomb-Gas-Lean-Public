import LeanResearch.RepulsiveCoulomb.PointCenteredTailSampleBound
import LeanResearch.RepulsiveCoulomb.RationalDirectionRetention
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic

/-! Records-only successor. The actual retained rational-time samples inherit
 the original endpoints' uniform direction bounds. The eventual parameter and
 circle-crossing facts are proved from the expanding metric windows. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem pointConformal_retained_rational_direction_bound
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (γ : ℕ → Icc (0 : ℝ) 1 → ℂ) (τ : ℕ → Icc (0 : ℝ) 1) (L : ℕ → ℝ)
    (hL : ∀ n, 0 < L n)
    (hd : ∀ n s t, (pointSmoothConformalEDist a y (γ n s) (γ n t)).toReal =
      |t.1 - s.1| * L n)
    (hright : ∀ n : ℕ, (n : ℝ) ≤ (1 - (τ n : ℝ)) * L n)
    {A R : ℝ} (hA : 0 < A) (hR : 0 ≤ R)
    (hyA : ∀ j, 2 * ‖y j‖ ≤ A) (hB : 0 < pointExteriorHalfMass a)
    (hD : pointExteriorMoment a y < (1 + pointExteriorHalfMass a) * A)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ A → (pointSmoothConformalEDist a y z 0).toReal ≤ R)
    (hanchor : ∀ n, ‖γ n (τ n)‖ < A)
    (hend : Tendsto (fun n => ‖γ n ⟨1, by norm_num⟩‖) atTop atTop)
    {d : ℂ} (hdir : ∀ n, γ n ⟨1, by norm_num⟩ /
      (‖γ n ⟨1, by norm_num⟩‖ : ℂ) = d)
    {c : ℝ → ℂ} {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (hconv : ∀ q : ℚ, Tendsto
      (fun n => metricCenteredClippedSegment (γ (σ n)) (τ (σ n)) (L (σ n)) q)
      atTop (𝓝 (c q)))
    {q : ℚ} (hq : 2 * R < (q : ℝ)) (hcq : c q ≠ 0)
    (hsmall : tailSineEnvelope A (pointExteriorHalfMass a) (pointExteriorMoment a y)
      ‖c q‖ < 1 / 2) :
    ‖c q / (‖c q‖ : ℂ) - d‖ ≤
      angularTailPotential A (pointExteriorHalfMass a) (pointExteriorMoment a y) ‖c q‖ := by
  have hindex : Tendsto (fun n => (σ n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hσ.tendsto_atTop
  have hnorm := (hconv q).norm
  have hH := (tailSineEnvelope_continuousAt A (pointExteriorHalfMass a)
    (pointExteriorMoment a y) (norm_pos_iff.mpr hcq)).tendsto.comp hnorm
  apply normalized_direction_tail_bound_of_tendsto hcq (hconv q)
  filter_upwards [hindex.eventually (eventually_gt_atTop (q : ℝ)),
    (hend.comp hσ.tendsto_atTop).eventually (eventually_gt_atTop A),
    hH.eventually (Iio_mem_nhds hsmall)] with n hn he hs
  have hb := pointConformal_centered_tail_sample_direction_bound ha y
    (γ (σ n)) (τ (σ n)) (hL (σ n)) (hd (σ n)) hA hR hyA hB hD hbound
    (hanchor (σ n)) he hq (hn.trans_le (hright (σ n))) hs.le
  simpa only [hdir] using hb

theorem pointConformal_direction_of_retained_segments
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (γ : ℕ → Icc (0 : ℝ) 1 → ℂ) (τ : ℕ → Icc (0 : ℝ) 1) (L : ℕ → ℝ)
    (hL : ∀ n, 0 < L n)
    (hd : ∀ n s t, (pointSmoothConformalEDist a y (γ n s) (γ n t)).toReal =
      |t.1 - s.1| * L n)
    (hright : ∀ n : ℕ, (n : ℝ) ≤ (1 - (τ n : ℝ)) * L n)
    {A : ℝ} (hA : 0 < A) (hyA : ∀ j, 2 * ‖y j‖ ≤ A)
    (hB : 0 < pointExteriorHalfMass a)
    (hD : pointExteriorMoment a y < (1 + pointExteriorHalfMass a) * A)
    (hanchor : ∀ n, ‖γ n (τ n)‖ < A)
    (hend : Tendsto (fun n => ‖γ n ⟨1, by norm_num⟩‖) atTop atTop)
    {d : ℂ} (hdir : ∀ n, γ n ⟨1, by norm_num⟩ /
      (‖γ n ⟨1, by norm_num⟩‖ : ℂ) = d)
    {c : ℝ → ℂ} (hc : Continuous c)
    (hcd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (hconv : ∀ q : ℚ, Tendsto
      (fun n => metricCenteredClippedSegment (γ (σ n)) (τ (σ n)) (L (σ n)) q)
      atTop (𝓝 (c q))) :
    Tendsto (fun t => c t / (‖c t‖ : ℂ)) atTop (𝓝 d) := by
  obtain ⟨R, hR, hbound⟩ := exists_pointConformal_disk_distance_bound ha y hA.le
  apply direction_tendsto_of_rational_tail_bounds hc
    (pointMetricLine_norm_tendsto_atTop ha y c hcd)
    (A := A) (D := pointExteriorMoment a y) (T := 2 * R) hB
  intro q hq hn hs
  exact pointConformal_retained_rational_direction_bound ha y γ τ L hL hd hright
    hA hR hyA hB hD hbound hanchor hend hdir hσ hconv hq hn hs

end RepulsiveCoulomb
