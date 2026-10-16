module

public import LeanResearch.RepulsiveCoulomb.DirectionalTailLimits
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic

@[expose] public section

/-! Uncompiled additive successor. Rational-time direction bounds extend by
actual local continuity, and Euclidean radial escape makes the explicit tail
potential vanish. No global continuity at a zero of c is assumed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem le_of_local_rational_bound {f g : ℝ → ℝ} {t : ℝ} {U : Set ℝ}
    (hU : U ∈ 𝓝 t) (hf : ContinuousAt f t) (hg : ContinuousAt g t)
    (hbound : ∀ q : ℚ, (q : ℝ) ∈ U → f q ≤ g q) : f t ≤ g t := by
  by_contra hn
  have hlt : g t < f t := lt_of_not_ge hn
  have hnear : {x | x ∈ U ∧ g x < f x} ∈ 𝓝 t := by
    filter_upwards [hU, hg.eventually_lt hf hlt] with x hx hltx
    exact ⟨hx, hltx⟩
  obtain ⟨q, hq⟩ := (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).mem_nhds hnear
  exact not_lt_of_ge (hbound q hq.1) hq.2

theorem real_direction_bound_of_rational_tail_bounds
    {c : ℝ → ℂ} (hc : Continuous c) {d : ℂ} {A B D T t : ℝ}
    (hbound : ∀ q : ℚ, T < (q : ℝ) → c q ≠ 0 →
      tailSineEnvelope A B D ‖c q‖ < 1 / 2 →
      ‖c q / (‖c q‖ : ℂ) - d‖ ≤ angularTailPotential A B D ‖c q‖)
    (ht : T < t) (hn : c t ≠ 0) (hsmall : tailSineEnvelope A B D ‖c t‖ < 1 / 2) :
    ‖c t / (‖c t‖ : ℂ) - d‖ ≤ angularTailPotential A B D ‖c t‖ := by
  let U : Set ℝ := {x | T < x ∧ 0 < ‖c x‖ ∧ tailSineEnvelope A B D ‖c x‖ < 1 / 2}
  have hnorm := norm_pos_iff.mpr hn
  have hH : ContinuousAt (fun x => tailSineEnvelope A B D ‖c x‖) t :=
    (tailSineEnvelope_continuousAt A B D hnorm).comp
      (f := fun x : ℝ => ‖c x‖) (x := t) hc.norm.continuousAt
  have hU : U ∈ 𝓝 t := by
    filter_upwards [Ioi_mem_nhds ht,
      continuousAt_const.eventually_lt hc.norm.continuousAt hnorm,
      hH.eventually_lt continuousAt_const hsmall] with x hx hn' hs'
    exact ⟨hx, hn', hs'⟩
  apply le_of_local_rational_bound hU
    (((normalized_direction_continuousAt hn).comp hc.continuousAt).sub_const d).norm
    ((angularTailPotential_continuousAt A B D hnorm).comp
      (f := fun x : ℝ => ‖c x‖) (x := t) hc.norm.continuousAt)
  intro q hq
  exact hbound q hq.1 (norm_pos_iff.mp hq.2.1) hq.2.2

theorem direction_tendsto_of_rational_tail_bounds
    {c : ℝ → ℂ} (hc : Continuous c) (hescape : Tendsto (fun t => ‖c t‖) atTop atTop)
    {d : ℂ} {A B D T : ℝ} (hB : 0 < B)
    (hbound : ∀ q : ℚ, T < (q : ℝ) → c q ≠ 0 →
      tailSineEnvelope A B D ‖c q‖ < 1 / 2 →
      ‖c q / (‖c q‖ : ℂ) - d‖ ≤ angularTailPotential A B D ‖c q‖) :
    Tendsto (fun t => c t / (‖c t‖ : ℂ)) atTop (𝓝 d) := by
  have hG := (angularTailPotential_tendsto_zero_atTop A D hB).comp hescape
  have hH := (tailSineEnvelope_tendsto_zero_atTop A D hB).comp hescape
  have hnorm : ∀ᶠ t in atTop, 0 < ‖c t‖ := hescape.eventually (eventually_gt_atTop 0)
  have hsmall : ∀ᶠ t in atTop, tailSineEnvelope A B D ‖c t‖ < 1 / 2 :=
    hH.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hreal : ∀ᶠ t in atTop, ‖c t / (‖c t‖ : ℂ) - d‖ ≤ angularTailPotential A B D ‖c t‖ := by
    filter_upwards [eventually_gt_atTop T, hnorm, hsmall] with t ht hn hs
    exact real_direction_bound_of_rational_tail_bounds hc hbound ht (norm_pos_iff.mp hn) hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hreal hG

end RepulsiveCoulomb
