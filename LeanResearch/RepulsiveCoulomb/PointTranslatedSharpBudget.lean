module

public import LeanResearch.RepulsiveCoulomb.PointSignedSectorBudget

@[expose] public section

/-! SOURCE-ONLY MAXIMAL-WIDTH ALGEBRA. Keep the marked attachment case
separate from the retained-flat initial collar. A zero residual angle consumes
all positive mass at two atoms; the final geometric whole-region argument is
still needed before positive allocation yields a contradiction.
-/
noncomputable section
open Set
open scoped BigOperators Classical
namespace RepulsiveCoulomb

theorem signedBudgetPos_add_le_add {x t:ℝ} (ht:0≤t) :
    signedBudgetPos (x+t)≤signedBudgetPos x+t := by
  change max (x+t) 0≤max x 0+t
  apply max_le
  · linarith [le_max_left x (0 : ℝ)]
  · exact add_nonneg (le_max_right _ _) ht

/-- The marked attachment may contribute ν(z)+t. The old transported atom
has already been charged, and this inequality accounts for that exactly once. -/
theorem pointSigned_translated_attachment_positive_charge
    {ν α:ℂ→₀ℝ} (hbudget:PointSignedBudgetInvariant ν α)
    {p z:ℂ} {t:ℝ} (ht:0≤t) (hp:ν p=t) :
    pointSignedPositiveMass ν α-t-signedBudgetPos (ν z)+signedBudgetPos (ν z+t)≤Real.pi := by
  have hadd:=signedBudgetPos_add_le_add (x:=ν z) ht
  have hmass:=hbudget.positiveMass_le_pi
  linarith

/-- If two distinct positive atoms sum to pi, every other signed atom is
nonpositive. This is the sharp algebra needed in the zero-angle degeneration;
it does not assert that there are no other marked or budget points. -/
theorem pointSigned_two_positive_atoms_exhaust
    {ν α:ℂ→₀ℝ} (hbudget:PointSignedBudgetInvariant ν α)
    {p z:ℂ} (hpz:p≠z) (hp:0<ν p) (hz:0<ν z) (hsum:ν p+ν z=Real.pi) :
    ∀ w:ℂ,w≠p→w≠z→ν w≤0 := by
  classical
  intro w hwp hwz
  by_contra hn
  have hw:0<ν w:=lt_of_not_ge hn
  have hpm:p∈pointSignedMarked ν α:=Finset.mem_union.mpr (Or.inl (Finsupp.mem_support_iff.mpr hp.ne'))
  have hzm:z∈pointSignedMarked ν α:=Finset.mem_union.mpr (Or.inl (Finsupp.mem_support_iff.mpr hz.ne'))
  have hwm:w∈pointSignedMarked ν α:=Finset.mem_union.mpr (Or.inl (Finsupp.mem_support_iff.mpr hw.ne'))
  let S:Finset ℂ:={p,z,w}
  have hsub:S⊆pointSignedMarked ν α:=by
    intro q hq
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl|rfl
    · exact hpm
    · exact hzm
    · exact hwm
  have hle:∑q∈S,signedBudgetPos (ν q)≤pointSignedPositiveMass ν α:=by
    change ∑q∈S,signedBudgetPos (ν q)≤∑q∈pointSignedMarked ν α,signedBudgetPos (ν q)
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _↦signedBudgetPos_nonneg (ν q))
  have hsum3:∑q∈S,signedBudgetPos (ν q)=ν p+ν z+ν w:=by
    simp [S,signedBudgetPos,max_eq_left hp.le,max_eq_left hz.le,max_eq_left hw.le,
      hpz,hwp,hwz,hwp.symm,hwz.symm,add_assoc]
  rw [hsum3] at hle
  have hmass:=hbudget.positiveMass_le_pi
  linarith

/-- Allocation cannot be supported only on points with zero allocation.
In a collapsed residual proof, support containment must first be derived from
actual whole-region coverage and the exact marked-set exclusions. -/
theorem pointSignedBudgetInvariant.not_support_on_two_zero_atoms
    {ν α:ℂ→₀ℝ} (hbudget:PointSignedBudgetInvariant ν α)
    {p z:ℂ} (hp:α p=0) (hz:α z=0) (hsupport:∀x,α x≠0→x=p∨x=z) : False := by
  have hα:α=0:=by
    ext x
    by_cases hx:α x=0
    · simpa using hx
    · rcases hsupport x hx with rfl|rfl
      · exact False.elim (hx hp)
      · exact False.elim (hx hz)
  have hpos:=hbudget.budget_pos
  have hzero:pointSignedBudgetMass ν α=0:=by simp [pointSignedBudgetMass,hα]
  rw [hzero] at hpos
  exact (lt_irrefl 0) hpos

end RepulsiveCoulomb
