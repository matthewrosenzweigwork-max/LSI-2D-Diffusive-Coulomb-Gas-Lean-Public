module

public import LeanResearch.RepulsiveCoulomb.PointTranslatedSharpBudget

@[expose] public section

/-!
SOURCE-ONLY, UNCOMPILED. The zero-residual-angle configuration saturates the
whole positive-mass bound. This forces the allocation to equal the negative
part pointwise, including at the two positive corners. No support containment,
whole-region exhaustion, or absence of further marked points is assumed.
-/
noncomputable section
open Set
open scoped BigOperators Classical
namespace RepulsiveCoulomb

/-- Two positive atoms already spending pi leave no allocation surplus at any
point. This is stronger than merely excluding a third positive atom. -/
theorem pointSigned_two_positive_atoms_force_exact_allocation
    {ν α : ℂ →₀ ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    {p z : ℂ} (hpz : p ≠ z) (hp : 0 < ν p) (hz : 0 < ν z)
    (hsum : ν p + ν z = Real.pi) :
    pointSignedPositiveMass ν α = Real.pi ∧
      pointSignedSurplusMass ν α = 0 ∧
      ∀ x, α x = signedBudgetNeg (ν x) := by
  classical
  have hpm : p ∈ pointSignedMarked ν α :=
    (mem_pointSignedMarked ν α p).mpr (Or.inl hp.ne')
  have hzm : z ∈ pointSignedMarked ν α :=
    (mem_pointSignedMarked ν α z).mpr (Or.inl hz.ne')
  have hsub : ({p, z} : Finset ℂ) ⊆ pointSignedMarked ν α := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact hpm
    · exact hzm
  have hle : ∑ q ∈ ({p, z} : Finset ℂ), signedBudgetPos (ν q) ≤
      pointSignedPositiveMass ν α := by
    change ∑ q ∈ ({p, z} : Finset ℂ), signedBudgetPos (ν q) ≤
      ∑ q ∈ pointSignedMarked ν α, signedBudgetPos (ν q)
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun q _ _ ↦ signedBudgetPos_nonneg (ν q))
  have hpair : ∑ q ∈ ({p, z} : Finset ℂ), signedBudgetPos (ν q) = Real.pi := by
    simpa [signedBudgetPos, max_eq_left hp.le, max_eq_left hz.le, hpz] using hsum
  rw [hpair] at hle
  have hmass : pointSignedPositiveMass ν α = Real.pi :=
    le_antisymm hbudget.positiveMass_le_pi hle
  have hs0 : pointSignedSurplusMass ν α = 0 := by
    have htotal := hbudget.surplusMass_add_positiveMass_le_pi
    have hn := hbudget.surplusMass_nonneg
    rw [hmass] at htotal
    linarith
  refine ⟨hmass, hs0, ?_⟩
  intro x
  have hlo := hbudget.dominates x
  have hhi := hbudget.surplusCoeff_le_mass x
  rw [hs0] at hhi
  linarith

/-- The degenerate corner endpoints both have zero allocation; every other
marked point is necessarily a negative atom carrying positive allocation.
It is incorrect to conclude that no other marked points exist from saturation
alone. Their geometric exclusion remains a separate obligation. -/
theorem pointSigned_two_positive_atoms_classify_other_marks
    {ν α : ℂ →₀ ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    {p z : ℂ} (hpz : p ≠ z) (hp : 0 < ν p) (hz : 0 < ν z)
    (hsum : ν p + ν z = Real.pi) :
    α p = 0 ∧ α z = 0 ∧
      ∀ x, x ≠ p → x ≠ z →
        (x ∈ pointSignedMarked ν α ↔ ν x < 0) ∧
        (x ∈ pointSignedMarked ν α → 0 < α x) := by
  obtain ⟨_, _, hα⟩ := pointSigned_two_positive_atoms_force_exact_allocation
    hbudget hpz hp hz hsum
  have hαp : α p = 0 := by
    rw [hα p]
    exact max_eq_right (neg_nonpos.mpr hp.le)
  have hαz : α z = 0 := by
    rw [hα z]
    exact max_eq_right (neg_nonpos.mpr hz.le)
  refine ⟨hαp, hαz, ?_⟩
  intro x hxp hxz
  have hxle := pointSigned_two_positive_atoms_exhaust hbudget hpz hp hz hsum x hxp hxz
  have hmarked : x ∈ pointSignedMarked ν α ↔ ν x < 0 := by
    constructor
    · intro hx
      apply lt_of_le_of_ne hxle
      intro he
      have hzero : α x = 0 := by rw [hα x, he, signedBudgetNeg_zero]
      rcases (mem_pointSignedMarked ν α x).mp hx with hn | hn
      · exact hn he
      · exact hn hzero
    · intro hx
      exact (mem_pointSignedMarked ν α x).mpr (Or.inl hx.ne)
  refine ⟨hmarked, ?_⟩
  intro hx
  have hn := hmarked.mp hx
  rw [hα x]
  exact (neg_pos.mpr hn).trans_le (le_max_left _ _)

/-- Original no-clean-ray information supplies zero allocation at a genuinely
clean marked boundary endpoint. The sign is then derived from domination,
without an angle or positive-turn certificate. -/
theorem pointSigned_marked_zero_budget_positive
    {ν α : ℂ →₀ ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    {p : ℂ} (hmarked : p ∈ pointSignedMarked ν α) (hzero : α p = 0) :
    0 < ν p := by
  have hdom := hbudget.dominates p
  rw [hzero] at hdom
  have hneg : -(ν p) ≤ 0 := (le_max_left _ _).trans hdom
  have hn : ν p ≠ 0 := by
    rcases (mem_pointSignedMarked ν α p).mp hmarked with hν | hα
    · exact hν
    · exact False.elim (hα hzero)
  exact lt_of_le_of_ne (by linarith) (Ne.symm hn)

/-- In the equality case every genuinely clean marked boundary endpoint
other than the original apex must be the translated top origin. The geometric
construction of the opposite end must supply its actual ray and cleanliness;
this theorem does not replace that construction by a certificate. -/
theorem pointSigned_saturated_last_mark_eq_target
    {ν α : ℂ →₀ ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    {p z w : ℂ} (hpz : p ≠ z) (hp : 0 < ν p) (hz : 0 < ν z)
    (hsum : ν p + ν z = Real.pi) (hwp : w ≠ p)
    (hmarked : w ∈ pointSignedMarked ν α) (hzero : α w = 0) : w = z := by
  by_contra hwz
  have hw := pointSigned_marked_zero_budget_positive hbudget hmarked hzero
  exact (not_le_of_gt hw)
    (pointSigned_two_positive_atoms_exhaust hbudget hpz hp hz hsum w hwp hwz)

end RepulsiveCoulomb
