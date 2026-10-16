import LeanResearch.RepulsiveCoulomb.IntervalAngleIncrementBridge
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! Uncompiled additive successor. Construct the last actual crossing of a
level and a full radial lift on an arbitrary nonzero compact interval. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exists_last_level_crossing
    {f : ℝ → ℝ} {a b K : ℝ} (hf : Continuous f) (hab : a < b)
    (ha : f a < K) (hb : K < f b) :
    ∃ s ∈ Ioo a b, f s = K ∧ ∀ t ∈ Ioc s b, K < f t := by
  let S : Set ℝ := Icc a b ∩ {t | f t = K}
  have hSc : IsCompact S := isCompact_Icc.inter_right (isClosed_eq hf continuous_const)
  obtain ⟨t, ht, htK⟩ := (intermediate_value_Icc hab.le hf.continuousOn) ⟨ha.le, hb.le⟩
  obtain ⟨s, hsS, hsmax⟩ := hSc.exists_isGreatest (show S.Nonempty from ⟨t, ht, htK⟩)
  have hs : s ∈ Icc a b := hsS.1
  have hsK : f s = K := hsS.2
  have has : a < s := lt_of_le_of_ne hs.1 (by intro heq; rw [← heq] at hsK; linarith)
  have hsb : s < b := lt_of_le_of_ne hs.2 (by intro heq; rw [heq] at hsK; linarith)
  refine ⟨s, ⟨has, hsb⟩, hsK, ?_⟩
  intro x hx
  by_contra hn
  have hxK : f x ≤ K := le_of_not_gt hn
  obtain ⟨v, hv, hvK⟩ := (intermediate_value_Icc hx.2 hf.continuousOn) ⟨hxK, hb.le⟩
  have hvS : v ∈ S := ⟨⟨(hs.1.trans hx.1.le).trans hv.1, hv.2⟩, hvK⟩
  have hvs := hsmax hvS
  linarith [hx.1, hv.1]

theorem exists_global_argument_lift_on_Icc
    {γ : ℝ → ℂ} {a b : ℝ} (hc : Continuous γ) (hab : a < b)
    (hne : ∀ t ∈ Icc a b, γ t ≠ 0) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧ ∀ t ∈ Icc a b,
      Complex.exp ((φ t : ℂ) * Complex.I) = γ t / (‖γ t‖ : ℂ) := by
  let g : ℝ → ℂ := fun t => γ (a + (b - a) * t)
  have hg : Continuous g := hc.comp (by fun_prop)
  have hmap (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : a + (b - a) * t ∈ Icc a b := by
    constructor <;> nlinarith [ht.1, ht.2]
  obtain ⟨β, hβ, hβlift⟩ := exists_global_interval_argument_lift hg
    (fun t ht => hne _ (hmap t ht))
  let φ : ℝ → ℝ := fun t => β ((t - a) / (b - a))
  refine ⟨φ, hβ.comp (by fun_prop), ?_⟩
  intro t ht
  have hparam : (t - a) / (b - a) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr hab.le)
    · apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
      linarith [ht.2]
  have hid : a + (b - a) * ((t - a) / (b - a)) = t := by
    field_simp [sub_ne_zero.mpr hab.ne'] <;> ring
  have h := hβlift ((t - a) / (b - a)) hparam
  simpa only [φ, g, hid] using h

end RepulsiveCoulomb
