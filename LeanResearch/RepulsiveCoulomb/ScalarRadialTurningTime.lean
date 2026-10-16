module

public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic

@[expose] public section

/-! Uncompiled additive draft. Rolle plus strictly increasing derivative
constructs the unique interior turning time and its two actual derivative signs.
This is used with the actual radial power whose second derivative was derived
from the constructed point-conformal developing chart. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exists_scalar_turning_time_of_deriv2_pos
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hend : f a = f b)
    (hsecond : ∀ t ∈ Ioo a b, 0 < deriv (deriv f) t) :
    ∃ m ∈ Ioo a b, deriv f m = 0 ∧
      (∀ t ∈ Ioo a m, deriv f t < 0) ∧
      (∀ t ∈ Ioo m b, 0 < deriv f t) ∧
      ∀ t ∈ Ioo a b, deriv f t = 0 → t = m := by
  have hmon : StrictMonoOn (deriv f) (Ioo a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    · intro t ht
      exact (differentiableAt_of_deriv_ne_zero (hsecond t ht).ne').continuousAt.continuousWithinAt
    · intro t ht
      exact hsecond t (by simpa only [interior_Ioo] using ht)
  obtain ⟨m, hm, hmzero⟩ := exists_deriv_eq_zero hab hf hend
  refine ⟨m, hm, hmzero, ?_, ?_, ?_⟩
  · intro t ht
    have h := hmon ⟨ht.1, ht.2.trans hm.2⟩ hm ht.2
    simpa only [hmzero] using h
  · intro t ht
    have h := hmon hm ⟨hm.1.trans ht.1, ht.2⟩ ht.1
    simpa only [hmzero] using h
  · intro t ht hzero
    apply hmon.injOn ht hm
    rw [hzero, hmzero]

end RepulsiveCoulomb
