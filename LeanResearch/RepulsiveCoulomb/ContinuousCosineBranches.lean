module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic

@[expose] public section

/-! Uncompiled additive draft. Actual continuous angle lifts cannot jump
between cosine-sign components. This derives the radial tangent branches used
by the aperture argument from continuity and the actual radial derivative signs. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem continuous_negative_cosine_branch_left
    {ψ : ℝ → ℝ} {a m : ℝ} (hψ : Continuous ψ)
    (hmin : ψ m = Real.pi / 2)
    (hcos : ∀ t ∈ Ico a m, Real.cos (ψ t) < 0) :
    ∀ t ∈ Ico a m, Real.pi / 2 < ψ t ∧ ψ t < 3 * Real.pi / 2 := by
  intro t ht
  constructor
  · by_contra hn
    have htupper : ψ t ≤ Real.pi / 2 := le_of_not_gt hn
    by_cases htpos : 0 ≤ ψ t
    · have hnonneg := Real.cos_nonneg_of_mem_Icc
        (show ψ t ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) from
          ⟨by linarith [Real.pi_pos], htupper⟩)
      linarith [hcos t ht]
    · have htneg : ψ t < 0 := lt_of_not_ge htpos
      have hv : 0 ∈ Icc (ψ t) (ψ m) := ⟨htneg.le, by rw [hmin]; positivity⟩
      obtain ⟨u, hu, hu0⟩ := (intermediate_value_Icc ht.2.le hψ.continuousOn) hv
      have hum : u < m := lt_of_le_of_ne hu.2 (by
        intro heq
        rw [heq, hmin] at hu0
        linarith [Real.pi_pos])
      have hc := hcos u ⟨ht.1.trans hu.1, hum⟩
      rw [hu0, Real.cos_zero] at hc
      linarith
  · by_contra hn
    have htbig : 3 * Real.pi / 2 ≤ ψ t := le_of_not_gt hn
    have hv : 3 * Real.pi / 2 ∈ Icc (ψ m) (ψ t) :=
      ⟨by rw [hmin]; linarith [Real.pi_pos], htbig⟩
    obtain ⟨u, hu, huval⟩ := (intermediate_value_Icc' ht.2.le hψ.continuousOn) hv
    have hum : u < m := lt_of_le_of_ne hu.2 (by
      intro heq
      rw [heq, hmin] at huval
      linarith [Real.pi_pos])
    have hc := hcos u ⟨ht.1.trans hu.1, hum⟩
    have hz : Real.cos (ψ u) = 0 := by
      rw [huval, show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring, Real.cos_add]
      simp
    rw [hz] at hc
    linarith

theorem continuous_positive_cosine_branch_right
    {ψ : ℝ → ℝ} {m b : ℝ} (hψ : Continuous ψ)
    (hmin : ψ m = Real.pi / 2)
    (hcos : ∀ t ∈ Ioc m b, 0 < Real.cos (ψ t)) :
    ∀ t ∈ Ioc m b, -Real.pi / 2 < ψ t ∧ ψ t < Real.pi / 2 := by
  intro t ht
  constructor
  · by_contra hn
    have htlow : ψ t ≤ -Real.pi / 2 := le_of_not_gt hn
    have hv : -Real.pi / 2 ∈ Icc (ψ t) (ψ m) :=
      ⟨htlow, by rw [hmin]; linarith [Real.pi_pos]⟩
    obtain ⟨u, hu, huval⟩ := (intermediate_value_Icc' ht.1.le hψ.continuousOn) hv
    have hmu : m < u := lt_of_le_of_ne hu.1 (by
      intro heq
      rw [← heq, hmin] at huval
      linarith [Real.pi_pos])
    have hc := hcos u ⟨hmu, hu.2.trans ht.2⟩
    have hz : Real.cos (ψ u) = 0 := by
      rw [huval, neg_div, Real.cos_neg, Real.cos_pi_div_two]
    rw [hz] at hc
    linarith
  · by_contra hn
    have htbig : Real.pi / 2 ≤ ψ t := le_of_not_gt hn
    by_cases htupper : ψ t ≤ Real.pi
    · have hnonpos := Real.cos_nonpos_of_pi_div_two_le_of_le htbig
        (show ψ t ≤ Real.pi + Real.pi / 2 by linarith [Real.pi_pos])
      linarith [hcos t ht]
    · have htp : Real.pi < ψ t := lt_of_not_ge htupper
      have hv : Real.pi ∈ Icc (ψ m) (ψ t) :=
        ⟨by rw [hmin]; linarith [Real.pi_pos], htp.le⟩
      obtain ⟨u, hu, huval⟩ := (intermediate_value_Icc ht.1.le hψ.continuousOn) hv
      have hmu : m < u := lt_of_le_of_ne hu.1 (by
        intro heq
        rw [← heq, hmin] at huval
        linarith [Real.pi_pos])
      have hc := hcos u ⟨hmu, hu.2.trans ht.2⟩
      rw [huval, Real.cos_pi] at hc
      linarith

end RepulsiveCoulomb
