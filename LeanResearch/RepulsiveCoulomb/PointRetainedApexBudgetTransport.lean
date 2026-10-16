import LeanResearch.RepulsiveCoulomb.PointSignedSectorBudget
import Mathlib.Data.Finsupp.Basic

/-!
SOURCE-ONLY DRAFT, NOT COMPILED. Algebra for the geometrically established
retained-apex update. The ambient signed coefficient is a GENERAL Finsupp; its
support is not restricted to original cone locations. This file does not claim
to construct a residual region, its topology, or its geometric curvature.
-/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

/-- The actual candidate signed measure after an occupied sector is removed. -/
def retainedApexCurvature (ν : ℂ →₀ ℝ) (p : ℂ) (β : ℝ) : ℂ →₀ ℝ :=
  ν + Finsupp.single p β

/-- Spending the actual sector angle at its retained apex. -/
def retainedApexBudget (α : ℂ →₀ ℝ) (p : ℂ) (β : ℝ) : ℂ →₀ ℝ :=
  α - Finsupp.single p β

@[simp] theorem retainedApexCurvature_at (ν : ℂ →₀ ℝ) (p : ℂ) (β : ℝ) :
    retainedApexCurvature ν p β p = ν p + β := by
  simp [retainedApexCurvature]

@[simp] theorem retainedApexBudget_at (α : ℂ →₀ ℝ) (p : ℂ) (β : ℝ) :
    retainedApexBudget α p β p = α p - β := by
  simp [retainedApexBudget]

theorem retainedApexCurvature_off (ν : ℂ →₀ ℝ) {p x : ℂ} (β : ℝ) (hx : x ≠ p) :
    retainedApexCurvature ν p β x = ν x := by
  simp [retainedApexCurvature,hx,Ne.symm hx]

theorem retainedApexBudget_off (α : ℂ →₀ ℝ) {p x : ℂ} (β : ℝ) (hx : x ≠ p) :
    retainedApexBudget α p β x = α x := by
  simp [retainedApexBudget,hx,Ne.symm hx]

/-- The scalar inequality in Pro Case I, valid with either sign of old turn. -/
theorem retainedApex_negative_domination_scalar {r a β : ℝ}
    (hdom : signedBudgetNeg r ≤ a) (hβ : β ≤ a) :
    signedBudgetNeg (r+β) ≤ a-β := by
  apply max_le
  · have hn : -r ≤ signedBudgetNeg r := le_max_left _ _
    linarith
  · linarith

/-- Every residual coefficient remains dominated, including at a newly created
flat positive-turn atom. No original-atom support constraint is used. -/
theorem retainedApex_budget_dominates {ν α : ℂ →₀ ℝ} {p : ℂ} {β : ℝ}
    (hdom : ∀ x, signedBudgetNeg (ν x) ≤ α x) (hβ : β ≤ α p) :
    ∀ x, signedBudgetNeg (retainedApexCurvature ν p β x) ≤ retainedApexBudget α p β x := by
  intro x
  by_cases hxp : x = p
  · subst x
    simpa only [retainedApexCurvature_at,retainedApexBudget_at] using
      retainedApex_negative_domination_scalar (hdom p) hβ
  · rw [retainedApexCurvature_off ν β hxp,retainedApexBudget_off α β hxp]
    exact hdom x

private theorem retainedApex_sum_on (μ : ℂ →₀ ℝ) (K : Finset ℂ)
    (hK : μ.support ⊆ K) : (∑ x ∈ μ.support, μ x) = ∑ x ∈ K, μ x := by
  classical
  apply Finset.sum_subset hK
  intro x hx hxμ
  exact Finsupp.notMem_support_iff.mp hxμ

/-- Both mass changes are derived on a common finite support. Their sum is
exactly invariant, independently of cancellations at old or new atoms. -/
theorem retainedApex_mass_changes (ν α : ℂ →₀ ℝ) (p : ℂ) (β : ℝ) :
    pointSignedCurvatureMass (retainedApexCurvature ν p β) (retainedApexBudget α p β) =
      pointSignedCurvatureMass ν α + β ∧
    pointSignedBudgetMass (retainedApexCurvature ν p β) (retainedApexBudget α p β) =
      pointSignedBudgetMass ν α - β := by
  classical
  let K := insert p (ν.support ∪ α.support)
  have hpK : p ∈ K := Finset.mem_insert_self _ _
  have hνK : ν.support ⊆ K := fun x hx ↦ Finset.mem_insert_of_mem (Finset.mem_union_left _ hx)
  have hαK : α.support ⊆ K := fun x hx ↦ Finset.mem_insert_of_mem (Finset.mem_union_right _ hx)
  have hsK : (Finsupp.single p β : ℂ →₀ ℝ).support ⊆ K := by
    intro x hx
    by_cases hxp : x = p
    · simpa only [hxp] using hpK
    · have hz : (Finsupp.single p β : ℂ →₀ ℝ) x = 0 := by simp [hxp,Ne.symm hxp]
      exact False.elim ((Finsupp.mem_support_iff.mp hx) hz)
  have hν'K : (retainedApexCurvature ν p β).support ⊆ K := by
    intro x hx
    by_cases hxK : x ∈ K
    · exact hxK
    · have hνx : ν x = 0 := Finsupp.notMem_support_iff.mp (fun hx ↦ hxK (hνK hx))
      have hsx : (Finsupp.single p β : ℂ →₀ ℝ) x = 0 :=
        Finsupp.notMem_support_iff.mp (fun hx ↦ hxK (hsK hx))
      have hz : retainedApexCurvature ν p β x = 0 := by simp [retainedApexCurvature,hνx,hsx]
      exact False.elim ((Finsupp.mem_support_iff.mp hx) hz)
  have hα'K : (retainedApexBudget α p β).support ⊆ K := by
    intro x hx
    by_cases hxK : x ∈ K
    · exact hxK
    · have hαx : α x = 0 := Finsupp.notMem_support_iff.mp (fun hx ↦ hxK (hαK hx))
      have hsx : (Finsupp.single p β : ℂ →₀ ℝ) x = 0 :=
        Finsupp.notMem_support_iff.mp (fun hx ↦ hxK (hsK hx))
      have hz : retainedApexBudget α p β x = 0 := by simp [retainedApexBudget,hαx,hsx]
      exact False.elim ((Finsupp.mem_support_iff.mp hx) hz)
  have hsingle : (∑ x ∈ K, (Finsupp.single p β : ℂ →₀ ℝ) x) = β := by
    rw [Finset.sum_eq_single p]
    · simp
    · intro x hx hxp
      simp [hxp,Ne.symm hxp]
    · exact fun hp ↦ False.elim (hp hpK)
  constructor
  · rw [pointSignedCurvatureMass_eq_support_sum,pointSignedCurvatureMass_eq_support_sum,
      retainedApex_sum_on _ K hν'K,retainedApex_sum_on _ K hνK]
    simp only [retainedApexCurvature,Finsupp.add_apply,Finset.sum_add_distrib,hsingle]
  · rw [pointSignedBudgetMass_eq_support_sum,pointSignedBudgetMass_eq_support_sum,
      retainedApex_sum_on _ K hα'K,retainedApex_sum_on _ K hαK]
    simp only [retainedApexBudget,Finsupp.sub_apply,Finset.sum_sub_distrib,hsingle]

/-- Nonterminal retained-apex surgery preserves the genuine signed invariant.
The geometric identification of retainedApexCurvature with nu_Q is separate. -/
theorem PointSignedBudgetInvariant.retainedApex {ν α : ℂ →₀ ℝ}
    (h : PointSignedBudgetInvariant ν α) (p : ℂ) {β : ℝ}
    (hβ : β ≤ α p) (hremaining : 0 < pointSignedBudgetMass ν α - β) :
    PointSignedBudgetInvariant (retainedApexCurvature ν p β) (retainedApexBudget α p β) := by
  obtain ⟨hV,hA⟩ := retainedApex_mass_changes ν α p β
  refine ⟨retainedApex_budget_dominates h.dominates hβ,?_,?_⟩
  · rwa [hA]
  · rw [hA,hV]
    have hm := h.mass_le
    linarith

/-- Retention of budget support uses the LITERAL residual formula. In Case I
the apex is on T, so even unspent budget at the apex is retained. -/
theorem retainedApex_budget_support_retained {P Q S T : Set ℂ}
    {α : ℂ →₀ ℝ} {p : ℂ} {β : ℝ}
    (hQ : Q = P \ (S \ T)) (hpP : p ∈ P) (hpT : p ∈ T)
    (hbudgetP : ∀ x, α x ≠ 0 → x ∈ P)
    (hclean : ∀ x ∈ S \ T, α x = 0) :
    ∀ x, retainedApexBudget α p β x ≠ 0 → x ∈ Q := by
  intro x hx
  rw [hQ]
  by_cases hxp : x = p
  · subst x
    exact ⟨hpP,fun hw ↦ hw.2 hpT⟩
  · have hαx : α x ≠ 0 := by
      rwa [retainedApexBudget_off α β hxp] at hx
    exact ⟨hbudgetP x hαx,fun hw ↦ hαx (hclean x hw)⟩

end RepulsiveCoulomb
