module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Finite signed-sum bookkeeping: integrability of a sum together with genuine
integrable lower bounds implies integrability of every term. This prevents
using cancellation of unproved Coulomb positive/negative parts.
Records-only draft, not staged or checked. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace RepulsiveCoulomb

theorem conditionalEntropyBranch_integrable_of_finite_sum
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] (Q : Measure α)
    {f g : ι → α → ℝ} (hfm : ∀ i, AEStronglyMeasurable (f i) Q)
    (hgi : ∀ i, Integrable (g i) Q) (hlower : ∀ i x, g i x ≤ f i x)
    (hsum : Integrable (fun x => ∑ i, f i x) Q) (i : ι) : Integrable (f i) Q := by
  classical
  have hrest : Integrable (fun x => ∑ j ∈ Finset.univ.erase i, g j x) Q :=
    integrable_finsetSum _ (fun j _ => hgi j)
  apply integrable_of_le_of_le (hfm i) (Eventually.of_forall (hlower i))
    (g₂ := fun x => (∑ j, f j x) - ∑ j ∈ Finset.univ.erase i, g j x)
  · apply Eventually.of_forall
    intro x
    have hle : (∑ j ∈ Finset.univ.erase i, g j x) ≤ ∑ j ∈ Finset.univ.erase i, f j x :=
      Finset.sum_le_sum (fun j _ => hlower j x)
    have he := Finset.sum_erase_add Finset.univ (fun j => f j x) (Finset.mem_univ i)
    linarith
  · exact hgi i
  · exact hsum.sub hrest

end RepulsiveCoulomb
