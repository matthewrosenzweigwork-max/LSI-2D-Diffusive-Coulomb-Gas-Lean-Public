module

public import LeanResearch.RepulsiveCoulomb.PointRetainedApexBudgetTransport
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Finset.Card
public import Mathlib.Topology.Closure
public import Mathlib.Tactic

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Discrete outer rank and terminal budget algebra.
No sector family, move existence, rank-decrease certificate, or termination
hypothesis is introduced. The geometric bridge separately proves the interior
coefficient equalities and exposed-mark event used by these elementary lemmas.
-/
noncomputable section
open Set
open scoped BigOperators Classical
namespace RepulsiveCoulomb

def pointCutInteriorMarks (P : Set ℂ) (ν α : ℂ →₀ ℝ) : Finset ℂ := by
  classical
  exact (pointSignedMarked ν α).filter (fun x ↦ x ∈ interior P)

@[simp] theorem mem_pointCutInteriorMarks (P : Set ℂ) (ν α : ℂ →₀ ℝ) (x : ℂ) :
    x ∈ pointCutInteriorMarks P ν α ↔ (ν x ≠ 0 ∨ α x ≠ 0) ∧ x ∈ interior P := by
  classical
  simp [pointCutInteriorMarks]

/-- This is the manuscript's natural-number outer rank, on actual ambient
Finsupp coefficients and the actual region interior. -/
def pointCutOuterRank (P : Set ℂ) (ν α : ℂ →₀ ℝ) : ℕ :=
  ⌊pointSignedBudgetMass ν α / Real.pi⌋₊ + α.support.card +
    (pointCutInteriorMarks P ν α).card

theorem pointCut_budgetCoeff_le_mass {ν α : ℂ →₀ ℝ}
    (hα : ∀ x, 0 ≤ α x) (p : ℂ) : α p ≤ pointSignedBudgetMass ν α := by
  rw [pointSignedBudgetMass_eq_support_sum]
  by_cases hp : p ∈ α.support
  · exact Finset.single_le_sum (fun x _ ↦ hα x) hp
  · rw [Finsupp.notMem_support_iff.mp hp]
    exact Finset.sum_nonneg (fun x _ ↦ hα x)

theorem pointCut_budgetMass_nonneg {ν α : ℂ →₀ ℝ} (hα : ∀ x, 0 ≤ α x) :
    0 ≤ pointSignedBudgetMass ν α := by
  rw [pointSignedBudgetMass_eq_support_sum]
  exact Finset.sum_nonneg (fun x _ ↦ hα x)

/-- Zero mass really means zero at every ambient point; no residual region is
needed for this terminal conclusion. -/
theorem pointCut_budget_eq_zero_iff_mass_eq_zero {ν α : ℂ →₀ ℝ}
    (hα : ∀ x, 0 ≤ α x) : α = 0 ↔ pointSignedBudgetMass ν α = 0 := by
  constructor
  · intro h
    simp [h, pointSignedBudgetMass_eq_support_sum]
  · intro h
    ext x
    have hle : α x ≤ (0 : ℝ) := by
      simpa only [h] using pointCut_budgetCoeff_le_mass (ν:=ν) hα x
    exact le_antisymm hle (hα x)

theorem pointCut_spent_budget_nonneg {α : ℂ →₀ ℝ} {p : ℂ} {β : ℝ}
    (hα : ∀ x, 0 ≤ α x) (hβ : β ≤ α p) :
    ∀ x, 0 ≤ retainedApexBudget α p β x := by
  intro x
  by_cases hx : x = p
  · subst x
    simpa only [retainedApexBudget_at] using sub_nonneg.mpr hβ
  · rw [retainedApexBudget_off α β hx]
    exact hα x

theorem pointCut_spent_budget_support_subset {α : ℂ →₀ ℝ} {p : ℂ} {β : ℝ}
    (hβ0 : 0 < β) (hβ : β ≤ α p) :
    (retainedApexBudget α p β).support ⊆ α.support := by
  intro x hx
  apply Finsupp.mem_support_iff.mpr
  by_cases hxp : x = p
  · subst x
    exact ne_of_gt (hβ0.trans_le hβ)
  · simpa only [retainedApexBudget_off α β hxp] using Finsupp.mem_support_iff.mp hx

theorem pointCut_spent_budget_support_eq_erase (α : ℂ →₀ ℝ) (p : ℂ) :
    (retainedApexBudget α p (α p)).support = α.support.erase p := by
  ext x
  by_cases hx : x = p
  · subst x
    simp [Finsupp.mem_support_iff]
  · simp [Finsupp.mem_support_iff, retainedApexBudget_off α (α p) hx, hx]

theorem pointCut_spent_budget_card_lt {α : ℂ →₀ ℝ} {p : ℂ} {β : ℝ}
    (hβ0 : 0 < β) (hβ : β = α p) :
    (retainedApexBudget α p β).support.card < α.support.card := by
  rw [hβ, pointCut_spent_budget_support_eq_erase]
  exact Finset.card_erase_lt_of_mem (Finsupp.mem_support_iff.mpr (ne_of_gt (hβ ▸ hβ0)))

/-- Exact one-sector terminal budget. Unlike either nonterminal surgery API,
this branch does not demand a nondegenerate complement of the terminal sector. -/
theorem pointCut_terminal_spend {ν α : ℂ →₀ ℝ} {p : ℂ} {β : ℝ}
    (hα : ∀ x, 0 ≤ α x) (hβ : β ≤ α p)
    (hterminal : pointSignedBudgetMass ν α - β = 0) :
    retainedApexBudget α p β = 0 ∧ α = Finsupp.single p β := by
  have hmass := (retainedApex_mass_changes ν α p β).2
  have hzero : retainedApexBudget α p β = 0 :=
    (pointCut_budget_eq_zero_iff_mass_eq_zero (pointCut_spent_budget_nonneg hα hβ)).mpr
      (hmass.trans hterminal)
  exact ⟨hzero, sub_eq_zero.mp hzero⟩

/-- Interior marked support cannot grow when both coefficients agree on the
new interior. This is used only after actual topology and coefficient proofs. -/
theorem pointCutInteriorMarks_subset {P Q : Set ℂ} {ν α μ δ : ℂ →₀ ℝ}
    (hQP : Q ⊆ P) (hν : ∀ x ∈ interior Q, μ x = ν x)
    (hα : ∀ x ∈ interior Q, δ x = α x) :
    pointCutInteriorMarks Q μ δ ⊆ pointCutInteriorMarks P ν α := by
  intro x hx
  obtain ⟨hm, hi⟩ := (mem_pointCutInteriorMarks Q μ δ x).mp hx
  refine (mem_pointCutInteriorMarks P ν α x).mpr ⟨?_, interior_mono hQP hi⟩
  simpa only [hν x hi, hα x hi] using hm

theorem pointCutInteriorMarks_card_lt_of_exposed {P Q : Set ℂ} {ν α μ δ : ℂ →₀ ℝ}
    (hQP : Q ⊆ P) (hν : ∀ x ∈ interior Q, μ x = ν x)
    (hα : ∀ x ∈ interior Q, δ x = α x) {x : ℂ}
    (hm : x ∈ pointSignedMarked ν α) (hi : x ∈ interior P) (hf : x ∈ frontier Q) :
    (pointCutInteriorMarks Q μ δ).card < (pointCutInteriorMarks P ν α).card := by
  have hsub : pointCutInteriorMarks Q μ δ ⊆ (pointCutInteriorMarks P ν α).erase x := by
    intro z hz
    refine Finset.mem_erase.mpr ⟨?_, pointCutInteriorMarks_subset hQP hν hα hz⟩
    intro he
    exact hf.2 (he ▸ ((mem_pointCutInteriorMarks Q μ δ z).mp hz).2)
  exact (Finset.card_le_card hsub).trans_lt
    (Finset.card_erase_lt_of_mem (Finset.mem_filter.mpr ⟨hm, hi⟩))

theorem pointCut_floor_mass_nonincrease {A β : ℝ} (hβ : 0 ≤ β) :
    ⌊(A - β) / Real.pi⌋₊ ≤ ⌊A / Real.pi⌋₊ := by
  apply Nat.floor_mono
  exact div_le_div_of_nonneg_right (sub_le_self A hβ) Real.pi_pos.le

theorem pointCut_floor_mass_lt_of_pi {A : ℝ} (hA : 0 ≤ A - Real.pi) :
    ⌊(A - Real.pi) / Real.pi⌋₊ < ⌊A / Real.pi⌋₊ := by
  have hnonneg : 0 ≤ (A - Real.pi) / Real.pi := div_nonneg hA Real.pi_pos.le
  have he : A / Real.pi = (A - Real.pi) / Real.pi + 1 := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [he, Nat.floor_add_one hnonneg]
  exact Nat.lt_succ_self _

/-- Strict outer progress from exact spending and one of the three actual
geometric events. The next file obtains these events from the constructed
sector and its actual retained/disappearing output, rather than assuming a
rank decrease or a family of future moves. -/
theorem pointCutOuterRank_lt_of_event {P Q : Set ℂ} {ν α μ : ℂ →₀ ℝ}
    {p : ℂ} {β : ℝ} (hβ0 : 0 < β) (hβ : β ≤ α p)
    (hremaining : 0 < pointSignedBudgetMass ν α - β)
    (hA : pointSignedBudgetMass μ (retainedApexBudget α p β) = pointSignedBudgetMass ν α - β)
    (hQP : Q ⊆ P) (hν : ∀ x ∈ interior Q, μ x = ν x)
    (hα : ∀ x ∈ interior Q, retainedApexBudget α p β x = α x)
    (hevent : β = Real.pi ∨ β = α p ∨
      ∃ x, x ∈ pointSignedMarked ν α ∧ x ∈ interior P ∧ x ∈ frontier Q) :
    pointCutOuterRank Q μ (retainedApexBudget α p β) < pointCutOuterRank P ν α := by
  have hf := pointCut_floor_mass_nonincrease (A:=pointSignedBudgetMass ν α) hβ0.le
  have hs := Finset.card_le_card (pointCut_spent_budget_support_subset hβ0 hβ)
  have hi := Finset.card_le_card (pointCutInteriorMarks_subset hQP hν hα)
  unfold pointCutOuterRank
  rw [hA]
  rcases hevent with he | he | ⟨x, hm, hx, hfQ⟩
  · have hd := pointCut_floor_mass_lt_of_pi (A:=pointSignedBudgetMass ν α)
      (by simpa only [he] using hremaining.le)
    subst β
    omega
  · have hd := pointCut_spent_budget_card_lt hβ0 he
    omega
  · have hd := pointCutInteriorMarks_card_lt_of_exposed hQP hν hα hm hx hfQ
    omega

end RepulsiveCoulomb
