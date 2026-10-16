import LeanResearch.RepulsiveCoulomb.PointCompleteLineViaCompactLimits
import LeanResearch.RepulsiveCoulomb.PointRetainedRationalDirection
import LeanResearch.RepulsiveCoulomb.CenteredSegmentReversal
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic

/-! Records-only successor. Both actual end directions of a complete minimizing
 line are constructed from its retained opposite-endpoint approximants. The
 negative direction uses an actual reversal, including the clipped samples. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem pointGeodesicWindowEndpointRadius_pos
    {m : ℕ} (y : Fin m → ℂ) {A C : ℝ} (hA : 0 < A) (hC : 0 < C) (n : ℕ) :
    0 < pointGeodesicWindowEndpointRadius y A C n := by
  have h := pointConformalRadius_pos y
  unfold pointGeodesicWindowEndpointRadius
  positivity

theorem pointGeodesicWindowEndpointRadius_tendsto
    {m : ℕ} (y : Fin m → ℂ) {A C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    Tendsto (pointGeodesicWindowEndpointRadius y A C) atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => C * (n : ℝ)) ?_
    (Filter.Tendsto.const_mul_atTop hC tendsto_natCast_atTop_atTop)
  intro n
  have h := pointConformalRadius_pos y
  unfold pointGeodesicWindowEndpointRadius
  nlinarith

theorem exists_pointConformal_complete_line_with_opposite_end_directions
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hB : 0 < pointExteriorHalfMass a) :
    ∃ c : ℝ → ℂ, Continuous c ∧
      (∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t) ∧
      Tendsto (fun t => c t / (‖c t‖ : ℂ)) atTop (𝓝 (1 : ℂ)) ∧
      Tendsto (fun t => c t / (‖c t‖ : ℂ)) atBot (𝓝 (-1 : ℂ)) := by
  obtain ⟨c, hc, hcd0, A₀, C, γ, τ, L, σ, hA₀, hC, hσ, hwin, hconv⟩ :=
    exists_pointConformal_complete_line_from_opposite_segments ha y hB
  have hcd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t := by
    intro s t
    simpa only [Real.dist_eq, abs_sub_comm] using hcd0 s t
  have hL := fun n => (hwin n).1
  have hanchor₀ := fun n => (hwin n).2.1
  have h0 := fun n => (hwin n).2.2.1
  have h1 := fun n => (hwin n).2.2.2.1
  have hd := fun n => (hwin n).2.2.2.2.1
  have hleft := fun n => (hwin n).2.2.2.2.2.1
  have hright := fun n => (hwin n).2.2.2.2.2.2
  let A := A₀ + pointExteriorPenetrationRadius a y + 1
  obtain ⟨hP, hyP, hDP, _⟩ := pointExteriorPenetrationRadius_bounds ha y hB
  have hA : 0 < A := by dsimp [A]; linarith
  have hPA : pointExteriorPenetrationRadius a y ≤ A := by dsimp [A]; linarith
  have hyA : ∀ j, 2 * ‖y j‖ ≤ A := fun j => (hyP j).trans hPA
  have hD : pointExteriorMoment a y < (1 + pointExteriorHalfMass a) * A :=
    hDP.trans_le (mul_le_mul_of_nonneg_left hPA (by linarith))
  have hanchor : ∀ n, ‖γ n (τ n)‖ < A := by
    intro n
    have h := hanchor₀ n
    dsimp [A]
    linarith
  have hRpos := pointGeodesicWindowEndpointRadius_pos y hA₀ hC
  have hRlim := pointGeodesicWindowEndpointRadius_tendsto y hA₀ hC
  have hnorm1 (n : ℕ) : ‖γ n ⟨1, by norm_num⟩‖ =
      pointGeodesicWindowEndpointRadius y A₀ C n := by
    rw [h1 n, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hRpos n)]
  have hnorm0 (n : ℕ) : ‖γ n ⟨0, by norm_num⟩‖ =
      pointGeodesicWindowEndpointRadius y A₀ C n := by
    rw [h0 n, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hRpos n)]
  have hdir1 (n : ℕ) : γ n ⟨1, by norm_num⟩ / (‖γ n ⟨1, by norm_num⟩‖ : ℂ) = 1 := by
    rw [hnorm1, h1 n]
    exact div_self (Complex.ofReal_ne_zero.mpr (ne_of_gt (hRpos n)))
  have hdir0 (n : ℕ) : γ n ⟨0, by norm_num⟩ / (‖γ n ⟨0, by norm_num⟩‖ : ℂ) = -1 := by
    rw [hnorm0, h0 n, neg_div, div_self (Complex.ofReal_ne_zero.mpr (ne_of_gt (hRpos n)))]
  have hpositive : Tendsto (fun t => c t / (‖c t‖ : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    apply pointConformal_direction_of_retained_segments ha y γ τ L hL hd hright
      hA hyA hB hD hanchor ?_ hdir1 hc hcd hσ hconv
    simpa only [hnorm1] using hRlim
  let γr : ℕ → Icc (0 : ℝ) 1 → ℂ := fun n t => γ n (reverseUnitInterval t)
  let τr : ℕ → Icc (0 : ℝ) 1 := fun n => reverseUnitInterval (τ n)
  have hdr : ∀ n s t, (pointSmoothConformalEDist a y (γr n s) (γr n t)).toReal =
      |t.1 - s.1| * L n := by
    intro n s t
    rw [show γr n s = γ n (reverseUnitInterval s) from rfl,
      show γr n t = γ n (reverseUnitInterval t) from rfl, hd n]
    congr 1
    change |(1 - (t : ℝ)) - (1 - (s : ℝ))| = |(t : ℝ) - s|
    rw [show (1 - (t : ℝ)) - (1 - (s : ℝ)) = -((t : ℝ) - s) by ring, abs_neg]
  have hrightR : ∀ n : ℕ, (n : ℝ) ≤ (1 - (τr n : ℝ)) * L n := by
    intro n
    simpa only [τr, reverseUnitInterval, sub_sub_cancel] using hleft n
  have hanchorR : ∀ n, ‖γr n (τr n)‖ < A := by
    intro n
    simpa only [γr, τr, reverseUnitInterval_reverse] using hanchor n
  have hendR : Tendsto (fun n => ‖γr n ⟨1, by norm_num⟩‖) atTop atTop := by
    simpa only [γr, reverseUnitInterval_one, hnorm0] using hRlim
  have hdirR : ∀ n, γr n ⟨1, by norm_num⟩ / (‖γr n ⟨1, by norm_num⟩‖ : ℂ) = -1 := by
    intro n
    simpa only [γr, reverseUnitInterval_one] using hdir0 n
  have hcdR : ∀ s t, (pointSmoothConformalEDist a y (c (-s)) (c (-t))).toReal = dist s t := by
    intro s t
    simpa only [Real.dist_eq, neg_sub_neg, abs_sub_comm] using hcd (-s) (-t)
  have hconvR : ∀ q : ℚ, Tendsto
      (fun n => metricCenteredClippedSegment (γr (σ n)) (τr (σ n)) (L (σ n)) q)
      atTop (𝓝 (c (-(q : ℝ)))) := by
    intro q
    simpa only [γr, τr, metricCenteredClippedSegment_reverse, Rat.cast_neg] using hconv (-q)
  have hnegativeR := pointConformal_direction_of_retained_segments ha y γr τr L hL hdr hrightR
    hA hyA hB hD hanchorR hendR hdirR (hc.comp continuous_neg) hcdR hσ hconvR
  have hnegative : Tendsto (fun t => c t / (‖c t‖ : ℂ)) atBot (𝓝 (-1 : ℂ)) := by
    simpa only [Function.comp_def, neg_neg] using hnegativeR.comp tendsto_neg_atBot_atTop
  exact ⟨c, hc, hcd, hpositive, hnegative⟩

end RepulsiveCoulomb
