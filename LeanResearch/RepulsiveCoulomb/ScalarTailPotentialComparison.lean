module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic

@[expose] public section

/-! Uncompiled additive successor. Two-sided derivative control is integrated
by scalar comparison potentials and the mean-value theorem, with no inverse
radius map and no reparameterization. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem endpoint_le_of_hasDerivAt_nonpos
    {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hn : ∀ t ∈ Ioo a b, f' t ≤ 0) : f b ≤ f a := by
  by_cases heq : a = b
  · subst b
    exact le_rfl
  · have hlt : a < b := lt_of_le_of_ne hab heq
    obtain ⟨t, ht, hslope⟩ := exists_hasDerivAt_eq_slope f f' hlt hc hd
    have hquot : (f b - f a) / (b - a) ≤ 0 := by rw [← hslope]; exact hn t ht
    have hnum : f b - f a ≤ 0 := by
      simpa only [zero_mul] using (div_le_iff₀ (sub_pos.mpr hlt)).mp hquot
    linarith

theorem abs_endpoint_le_of_potential_derivative_bound
    {J H J' H' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hJc : ContinuousOn J (Icc a b)) (hHc : ContinuousOn H (Icc a b))
    (hJd : ∀ t ∈ Ioo a b, HasDerivAt J (J' t) t)
    (hHd : ∀ t ∈ Ioo a b, HasDerivAt H (H' t) t)
    (hbound : ∀ t ∈ Ioo a b, |J' t| ≤ H' t) :
    |J b| ≤ |J a| + H b - H a := by
  have hupper : J b - H b ≤ J a - H a := by
    apply endpoint_le_of_hasDerivAt_nonpos hab (hJc.sub hHc)
      (fun t ht => (hJd t ht).sub (hHd t ht))
    intro t ht
    have h := (le_abs_self (J' t)).trans (hbound t ht)
    linarith
  have hlower : -J b - H b ≤ -J a - H a := by
    apply endpoint_le_of_hasDerivAt_nonpos hab (hJc.neg.sub hHc)
      (fun t ht => ((hJd t ht).neg).sub (hHd t ht))
    intro t ht
    have h := (neg_le_abs (J' t)).trans (hbound t ht)
    linarith
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self (J a), neg_le_abs (J a)]

theorem abs_increment_le_of_decreasing_tail_potential
    {φ G φ' G' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hφc : ContinuousOn φ (Icc a b)) (hGc : ContinuousOn G (Icc a b))
    (hφd : ∀ t ∈ Ioo a b, HasDerivAt φ (φ' t) t)
    (hGd : ∀ t ∈ Ioo a b, HasDerivAt G (G' t) t)
    (hbound : ∀ t ∈ Ioo a b, |φ' t| ≤ -(G' t)) :
    |φ b - φ a| ≤ G a - G b := by
  have h := abs_endpoint_le_of_potential_derivative_bound hab
    (hφc.sub continuousOn_const) hGc.neg
    (fun t ht => (hφd t ht).sub_const (φ a))
    (fun t ht => (hGd t ht).neg) hbound
  change |φ b - φ a| ≤ |φ a - φ a| + (-G b) - (-G a) at h
  simpa only [sub_self, abs_zero, zero_add, add_zero, neg_neg, sub_neg_eq_add, add_comm, sub_eq_add_neg] using h

end RepulsiveCoulomb
