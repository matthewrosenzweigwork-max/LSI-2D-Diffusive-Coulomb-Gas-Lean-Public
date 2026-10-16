module

public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchCoulombLabels
public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchHanIntegral
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
Exact reconciliation of the actual Coulomb selected-label charts with the
Fin.succAbove product charts used by the Han--Shearer proof. Reordering the
outside variables is a genuine measurable equivalence and preserves the
conditional KL; the selected physical coordinate is unchanged.
Records-only draft, not staged or checked.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb

theorem conditionalEntropyBranch_cost_map_left_equiv {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (Q : Measure (α × β)) [IsFiniteMeasure Q] (ν : Measure β) [IsProbabilityMeasure ν]
    (e : α ≃ᵐ γ) :
    conditionalEntropyBranchCost (Q.map (Prod.map e id)) ν = conditionalEntropyBranchCost Q ν := by
  apply le_antisymm
  · exact conditionalEntropyBranch_cost_map_left Q ν e.measurable
  · have h := conditionalEntropyBranch_cost_map_left (Q.map (Prod.map e id)) ν e.symm.measurable
    have he : (Q.map (Prod.map e id)).map (Prod.map e.symm id) = Q := by
      exact (e.prodCongr (MeasurableEquiv.refl β)).map_symm_map
    simpa only [he] using h

def conditionalEntropyBranchOutsideSubtype {N : ℕ} (i : Fin (N + 1)) :
    {j : Fin (N + 1) // j ≠ 0} ≃ {j : Fin (N + 1) // j ≠ i} :=
  Equiv.subtypeEquiv (Equiv.swap 0 i) (fun j => by
    constructor
    · intro hj he
      apply hj
      apply (Equiv.swap 0 i).injective
      simpa only [Equiv.swap_apply_left] using he
    · intro hj he
      subst j
      exact hj (Equiv.swap_apply_left 0 i))

def conditionalEntropyBranchOutsidePerm {N : ℕ} (i : Fin (N + 1)) : Equiv.Perm (Fin N) :=
  ((finSuccAboveEquiv 0).trans (conditionalEntropyBranchOutsideSubtype i)).trans
    (finSuccAboveEquiv i).symm

theorem conditionalEntropyBranchOutsidePerm_index {N : ℕ} (i : Fin (N + 1)) (j : Fin N) :
    i.succAbove (conditionalEntropyBranchOutsidePerm i j) = Equiv.swap 0 i j.succ := by
  change ((finSuccAboveEquiv i) ((finSuccAboveEquiv i).symm
    (conditionalEntropyBranchOutsideSubtype i (finSuccAboveEquiv 0 j)))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

def conditionalEntropyBranchOutsideChart {N : ℕ} (i : Fin (N + 1)) :
    (Fin N → ℂ) ≃ᵐ CoulombConfig N :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℂ)
    (conditionalEntropyBranchOutsidePerm i).symm).trans (MeasurableEquiv.toLp 2 (Fin N → ℂ))

theorem conditionalEntropyBranchOutsideChart_apply {N : ℕ} (i : Fin (N + 1))
    (y : Fin N → ℂ) (j : Fin N) :
    conditionalEntropyBranchOutsideChart i y j = y (conditionalEntropyBranchOutsidePerm i j) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (conditionalEntropyBranchOutsidePerm i).symm (β := fun _ : Fin N => ℂ)
      y (conditionalEntropyBranchOutsidePerm i j)
  change MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℂ)
    (conditionalEntropyBranchOutsidePerm i).symm y j =
      y (conditionalEntropyBranchOutsidePerm i j)
  simpa only [Equiv.symm_apply_apply] using h

theorem conditionalEntropyBranch_coulomb_chart_square {N : ℕ} (i : Fin (N + 1))
    (z : CoulombConfig (N + 1)) :
    conditionalEntropyBranchCoulombChart i z =
      Prod.map (conditionalEntropyBranchOutsideChart i) id
        (conditionalEntropyBranchChart i (WithLp.ofLp z)) := by
  apply Prod.ext
  · ext j
    rw [conditionalEntropyBranchCoulombChart_outside]
    change z (Equiv.swap 0 i j.succ) =
      conditionalEntropyBranchOutsideChart i (fun k => z (i.succAbove k)) j
    rw [conditionalEntropyBranchOutsideChart_apply, conditionalEntropyBranchOutsidePerm_index]
  · rw [conditionalEntropyBranchCoulombChart_site]
    rfl

theorem conditionalEntropyBranch_coulomb_chart_map {N : ℕ}
    (Q : Measure (CoulombConfig (N + 1))) (i : Fin (N + 1)) :
    Q.map (conditionalEntropyBranchCoulombChart i) =
      ((Q.map (@WithLp.ofLp 2 (Fin (N + 1) → ℂ))).map (conditionalEntropyBranchChart i)).map
        (Prod.map (conditionalEntropyBranchOutsideChart i) id) := by
  rw [Measure.map_map ((conditionalEntropyBranchOutsideChart i).measurable.prodMap measurable_id)
      (conditionalEntropyBranchChart i).measurable,
    Measure.map_map (((conditionalEntropyBranchOutsideChart i).measurable.prodMap measurable_id).comp
      (conditionalEntropyBranchChart i).measurable) (WithLp.measurable_ofLp 2 _)]
  congr 1
  funext z
  exact conditionalEntropyBranch_coulomb_chart_square i z

theorem conditionalEntropyBranch_coulomb_base_cost {N : ℕ}
    (Q : Measure (CoulombConfig (N + 1))) [IsProbabilityMeasure Q]
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (i : Fin (N + 1)) :
    conditionalEntropyBranchCost (Q.map (conditionalEntropyBranchCoulombChart i)) ν =
      conditionalEntropyBranchSiteCost
        (Q.map (@WithLp.ofLp 2 (Fin (N + 1) → ℂ))) (fun _ => ν) i := by
  rw [conditionalEntropyBranch_coulomb_chart_map Q i,
    conditionalEntropyBranch_cost_map_left_equiv]
  rfl

/-- Relative Han--Shearer in the actual physical Coulomb conditioning charts,
valid for every labeled competitor and retaining infinite entropy. -/
theorem conditionalEntropyBranch_coulomb_han {N : ℕ}
    (Q : Measure (CoulombConfig (N + 1))) [IsProbabilityMeasure Q]
    (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    klDiv (Q.map (@WithLp.ofLp 2 (Fin (N + 1) → ℂ))) (Measure.pi (fun _ : Fin (N + 1) => ν)) ≤
      ∑ i : Fin (N + 1), conditionalEntropyBranchCost
        (Q.map (conditionalEntropyBranchCoulombChart i)) ν := by
  simp_rw [conditionalEntropyBranch_coulomb_base_cost Q ν]
  exact conditionalEntropyBranch_han_shearer N _ _

end RepulsiveCoulomb
