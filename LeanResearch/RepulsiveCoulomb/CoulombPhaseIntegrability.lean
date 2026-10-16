import LeanResearch.RepulsiveCoulomb.CoulombPhaseRotation
import LeanResearch.RepulsiveCoulomb.LabeledCoulombNormalization
import Mathlib.MeasureTheory.Integral.Prod

/-! Joint integrability needed for the actual common-phase Fubini argument. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace RepulsiveCoulomb

def coulombPhaseAction (N : ℕ) (θ : ℝ) (z : CoulombConfig N) : CoulombConfig N :=
  (Circle.exp θ : ℂ) • z

theorem coulombPhaseAction_eq_rotation (N : ℕ) (θ : ℝ) (z : CoulombConfig N) :
    coulombPhaseAction N θ z = coulombPhaseRotation N (Circle.exp θ) z :=
  (coulombPhaseRotation_eq_smul N (Circle.exp θ) z).symm

theorem coulombPhaseAction_continuous (N : ℕ) :
    Continuous (fun p : ℝ × CoulombConfig N => coulombPhaseAction N p.1 p.2) := by
  have h : Continuous (fun θ : ℝ => (Circle.exp θ : ℂ)) :=
    continuous_subtype_val.comp Circle.exp.continuous
  exact (h.comp continuous_fst).smul continuous_snd

theorem coulombPhaseAction_integral {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) (θ : ℝ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : CoulombConfig N → E) :
    (∫ z, F (coulombPhaseAction N θ z) ∂coulombMeasure N β) = ∫ z, F z ∂coulombMeasure N β := by
  simp only [coulombPhaseAction_eq_rotation]
  exact coulombPhaseRotation_integral hβ (Circle.exp θ) F

theorem coulomb_phase_product_integrable {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {F : CoulombConfig N → ℂ} (hF : Continuous F) (hi : Integrable F (coulombMeasure N β)) :
    Integrable (fun p : ℝ × CoulombConfig N => F (coulombPhaseAction N p.1 p.2))
      ((volume.restrict (Ioc 0 (2 * Real.pi))).prod (coulombMeasure N β)) := by
  letI := coulombMeasure_isProbability (N := N) hβ
  have hc := hF.comp (coulombPhaseAction_continuous N)
  apply (integrable_prod_iff hc.aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro θ
    simp only [coulombPhaseAction_eq_rotation]
    exact (coulombPhaseRotation_gibbs_preserving hβ.le (Circle.exp θ)).integrable_comp_of_integrable hi
  · have he : (fun θ : ℝ => ∫ z, ‖F (coulombPhaseAction N θ z)‖ ∂coulombMeasure N β) =
        fun _ : ℝ => ∫ z, ‖F z‖ ∂coulombMeasure N β := by
      funext θ
      exact coulombPhaseAction_integral hβ.le θ (fun z => ‖F z‖)
    simp only [Function.comp_apply]
    rw [he]
    exact integrable_const _

end RepulsiveCoulomb
