module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic

@[expose] public section

/-! Uncompiled additive successor. A strictly convex exterior portion which
lies above its initial level has strictly positive first derivative. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem deriv_pos_of_deriv2_pos_and_above_left_endpoint
    {f : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hsecond : ∀ t ∈ Ioo a b, 0 < deriv (deriv f) t)
    (hlevel : ∀ t ∈ Ioo a b, f a < f t) :
    ∀ t ∈ Ioo a b, 0 < deriv f t := by
  have hmon : StrictMonoOn (deriv f) (Ioo a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    · intro t ht
      exact (differentiableAt_of_deriv_ne_zero (hsecond t ht).ne').continuousAt.continuousWithinAt
    · intro t ht
      exact hsecond t (by simpa only [interior_Ioo] using ht)
  intro t ht
  obtain ⟨u, hu, hdu⟩ := exists_hasDerivAt_eq_slope f (deriv f) ht.1
    (hc.mono (fun x hx => ⟨hx.1, hx.2.trans ht.2.le⟩))
    (fun x hx => (hd x ⟨hx.1, hx.2.trans ht.2⟩).hasDerivAt)
  have hupos : 0 < deriv f u := by
    rw [hdu]
    exact div_pos (sub_pos.mpr (hlevel t ht)) (sub_pos.mpr ht.1)
  exact hupos.trans (hmon ⟨hu.1, hu.2.trans ht.2⟩ ht hu.2)

end RepulsiveCoulomb
