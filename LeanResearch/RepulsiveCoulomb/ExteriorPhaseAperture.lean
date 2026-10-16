import LeanResearch.RepulsiveCoulomb.ScalarDerivativeBarrier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! Uncompiled additive draft. Exact scalar aperture and backward barrier.
The scalar inputs still need assembly from actual geodesic/lift/convexity data;
this is not an assumed visibility or balanced-line certificate. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem scalar_lower_backward_barrier_of_deriv_neg_below
    {f : ℝ → ℝ} {a b K : ℝ} (hf : Continuous f) (hend : K ≤ f b)
    (hderiv : ∀ u ∈ Ioo a b, f u < K → deriv f u < 0) :
    ∀ t ∈ Icc a b, K ≤ f t := by
  intro t ht
  by_contra hnot
  have htval : f t < K := lt_of_not_ge hnot
  let S : Set ℝ := Icc t b ∩ {u | K ≤ f u}
  have hScompact : IsCompact S :=
    isCompact_Icc.inter_right (isClosed_le continuous_const hf)
  have hSne : S.Nonempty := ⟨b, ⟨⟨ht.2, le_rfl⟩, hend⟩⟩
  obtain ⟨x, hxS, hxmin⟩ := hScompact.exists_isLeast hSne
  have hx : t ≤ x ∧ x ≤ b := hxS.1
  have hxval : K ≤ f x := hxS.2
  have htx : t < x := lt_of_le_of_ne hx.1 (by
    intro h
    rw [← h] at hxval
    linarith)
  have hbelow (u : ℝ) (hu : u ∈ Ioo t x) : f u < K := by
    by_contra hn
    have huS : u ∈ S := ⟨⟨hu.1.le, hu.2.le.trans hx.2⟩, le_of_not_gt hn⟩
    have hxu := hxmin huS
    linarith [hu.2]
  have hanti : StrictAntiOn f (Icc t x) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hf.continuousOn
    intro u hu
    have hu' : u ∈ Ioo t x := by simpa only [interior_Icc] using hu
    exact hderiv u ⟨ht.1.trans_lt hu'.1, hu'.2.trans_le hx.2⟩ (hbelow u hu')
  have hdrop := hanti (show t ∈ Icc t x from ⟨le_rfl, htx.le⟩)
    (show x ∈ Icc t x from ⟨htx.le, le_rfl⟩) htx
  linarith

theorem exterior_phase_argument_bounds
    {a m b p C ε : ℝ} {φ ψ δ w : ℝ → ℝ}
    (ham : a < m) (hmb : m < b) (hp : 0 < p) (hφ : Continuous φ)
    (hphase : ∀ t ∈ Icc a b, p * φ t + ψ t + δ t = C)
    (hδ : ∀ t ∈ Icc a b, |δ t| ≤ ε)
    (hmin : ψ m = Real.pi / 2)
    (hleft : ∀ t ∈ Ico a m, Real.pi / 2 < ψ t ∧ ψ t < 3 * Real.pi / 2)
    (hright : ∀ t ∈ Ioc m b, -Real.pi / 2 < ψ t ∧ ψ t < Real.pi / 2)
    (hderiv : ∀ t ∈ Ioo a b, deriv φ t = w t * Real.sin (ψ t))
    (hw : ∀ t ∈ Ioo a b, 0 < w t) :
    ∀ t ∈ Icc a b, (C - Real.pi - ε) / p ≤ φ t ∧ φ t ≤ (C + ε) / p := by
  let lo := (C - Real.pi - ε) / p
  let hi := (C + ε) / p
  have hmcc : m ∈ Icc a b := ⟨ham.le, hmb.le⟩
  have hmphase := hphase m hmcc
  rw [hmin] at hmphase
  have hmδ := abs_le.mp (hδ m hmcc)
  have hlom : lo < φ m := by
    dsimp [lo]
    apply (div_lt_iff₀ hp).mpr
    nlinarith [Real.pi_pos]
  have hmhi : φ m < hi := by
    dsimp [hi]
    apply (lt_div_iff₀ hp).mpr
    nlinarith [Real.pi_pos]
  have hupper : ∀ t ∈ Icc m b, φ t ≤ hi := by
    apply scalar_upper_barrier_of_deriv_neg_above hφ hmhi.le
    intro t ht habove
    have htab : t ∈ Ioo a b := ⟨ham.trans ht.1, ht.2⟩
    have htcc : t ∈ Icc a b := ⟨htab.1.le, htab.2.le⟩
    have hbranch := hright t ⟨ht.1, ht.2.le⟩
    have hδt := abs_le.mp (hδ t htcc)
    have hphaset := hphase t htcc
    have hbig : C + ε < φ t * p := (div_lt_iff₀ hp).mp habove
    have hψneg : ψ t < 0 := by nlinarith
    have hsin : Real.sin (ψ t) < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt hψneg (by nlinarith [Real.pi_pos])
    rw [hderiv t htab]
    exact mul_neg_of_pos_of_neg (hw t htab) hsin
  have hlower : ∀ t ∈ Icc a m, lo ≤ φ t := by
    apply scalar_lower_backward_barrier_of_deriv_neg_below hφ hlom.le
    intro t ht hbelow
    have htab : t ∈ Ioo a b := ⟨ht.1, ht.2.trans hmb⟩
    have htcc : t ∈ Icc a b := ⟨htab.1.le, htab.2.le⟩
    have hbranch := hleft t ⟨ht.1.le, ht.2⟩
    have hδt := abs_le.mp (hδ t htcc)
    have hphaset := hphase t htcc
    have hsmall : φ t * p < C - Real.pi - ε := (lt_div_iff₀ hp).mp hbelow
    have hψbig : Real.pi < ψ t := by nlinarith
    have hsinpos : 0 < Real.sin (ψ t - Real.pi) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by nlinarith [Real.pi_pos])
    have hsin : Real.sin (ψ t) < 0 := by
      rw [Real.sin_sub_pi] at hsinpos
      linarith
    rw [hderiv t htab]
    exact mul_neg_of_pos_of_neg (hw t htab) hsin
  intro t ht
  rcases lt_trichotomy t m with htm | htm | hmt
  · have hbranch := hleft t ⟨ht.1, htm⟩
    have hδt := abs_le.mp (hδ t ht)
    have hphaset := hphase t ht
    refine ⟨hlower t ⟨ht.1, htm.le⟩, ?_⟩
    apply le_of_lt
    apply (lt_div_iff₀ hp).mpr
    nlinarith [Real.pi_pos]
  · subst t
    exact ⟨hlom.le, hmhi.le⟩
  · have hbranch := hright t ⟨hmt, ht.2⟩
    have hδt := abs_le.mp (hδ t ht)
    have hphaset := hphase t ht
    refine ⟨?_, hupper t ⟨hmt.le, ht.2⟩⟩
    apply le_of_lt
    apply (div_lt_iff₀ hp).mpr
    nlinarith [Real.pi_pos]

theorem exterior_phase_aperture_le
    {a m b p C ε : ℝ} {φ ψ δ w : ℝ → ℝ}
    (ham : a < m) (hmb : m < b) (hp : 0 < p) (hφ : Continuous φ)
    (hphase : ∀ t ∈ Icc a b, p * φ t + ψ t + δ t = C)
    (hδ : ∀ t ∈ Icc a b, |δ t| ≤ ε)
    (hmin : ψ m = Real.pi / 2)
    (hleft : ∀ t ∈ Ico a m, Real.pi / 2 < ψ t ∧ ψ t < 3 * Real.pi / 2)
    (hright : ∀ t ∈ Ioc m b, -Real.pi / 2 < ψ t ∧ ψ t < Real.pi / 2)
    (hderiv : ∀ t ∈ Ioo a b, deriv φ t = w t * Real.sin (ψ t))
    (hw : ∀ t ∈ Ioo a b, 0 < w t)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    |φ t - φ s| ≤ (Real.pi + 2 * ε) / p := by
  have hbnd := exterior_phase_argument_bounds ham hmb hp hφ hphase hδ hmin hleft hright hderiv hw
  have hs' := hbnd s hs
  have ht' := hbnd t ht
  have hwidth : (C + ε) / p - (C - Real.pi - ε) / p =
      (Real.pi + 2 * ε) / p := by ring
  apply abs_le.mpr
  constructor <;> linarith

end RepulsiveCoulomb
