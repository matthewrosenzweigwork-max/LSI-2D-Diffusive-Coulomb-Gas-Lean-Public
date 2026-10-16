module

public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchDensityKL

@[expose] public section

/-! Exact transport of the literal density law through coordinate charts.
Records-only draft, not staged or checked. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

theorem conditionalEntropyBranch_densityLaw_map {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (P : Measure α)
    (e : α ≃ᵐ β) {F : α → ℝ} (hFm : Measurable F) :
    (conditionalEntropyBranchDensityLaw P F).map e =
      conditionalEntropyBranchDensityLaw (P.map e) (fun y => F (e.symm y)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  unfold conditionalEntropyBranchDensityLaw
  have hD : Measurable (fun y => ENNReal.ofReal (F (e.symm y))) :=
    (hFm.comp e.symm.measurable).ennreal_ofReal
  calc
    (∫⁻ y, g y ∂(P.withDensity (fun x => ENNReal.ofReal (F x))).map e) =
        ∫⁻ x, g (e x) ∂P.withDensity (fun x => ENNReal.ofReal (F x)) :=
      lintegral_map hg e.measurable
    _ = ∫⁻ x, ENNReal.ofReal (F x) * g (e x) ∂P :=
      lintegral_withDensity_eq_lintegral_mul P hFm.ennreal_ofReal (hg.comp e.measurable)
    _ = ∫⁻ x, ENNReal.ofReal (F (e.symm (e x))) * g (e x) ∂P := by
      simp only [MeasurableEquiv.symm_apply_apply]
    _ = ∫⁻ y, ENNReal.ofReal (F (e.symm y)) * g y ∂P.map e :=
      (lintegral_map (hD.mul hg) e.measurable).symm
    _ = ∫⁻ y, g y ∂(P.map e).withDensity (fun y => ENNReal.ofReal (F (e.symm y))) :=
      (lintegral_withDensity_eq_lintegral_mul (P.map e) hD hg).symm

end RepulsiveCoulomb
