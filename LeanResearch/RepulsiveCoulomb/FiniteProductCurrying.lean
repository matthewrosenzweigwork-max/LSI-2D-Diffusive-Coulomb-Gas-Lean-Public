import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! Finite sigma-finite product measure reassociation, including Lebesgue factors. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace RepulsiveCoulomb

theorem finite_pi_uncurry_measurePreserving {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] {X : (i : ι) → κ i → Type*}
    [∀ i j, MeasurableSpace (X i j)] (μ : (i : ι) → (j : κ i) → Measure (X i j))
    [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry X).symm
      (Measure.pi (fun i => Measure.pi (μ i))) (Measure.pi (fun p : Sigma κ => μ p.1 p.2)) := by
  classical
  refine ⟨(MeasurableEquiv.piCurry X).symm.measurable, ?_⟩
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [MeasurableEquiv.map_apply]
  have hpre : (MeasurableEquiv.piCurry X).symm ⁻¹' (univ.pi s) =
      univ.pi (fun i => univ.pi (fun j => s ⟨i, j⟩)) := by
    ext x
    simp only [MeasurableEquiv.coe_piCurry_symm, mem_preimage, mem_univ_pi]
    constructor
    · intro h i j
      exact h ⟨i, j⟩
    · intro h p
      exact h p.1 p.2
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_sigma]

end RepulsiveCoulomb
