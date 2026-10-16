import LeanResearch.RepulsiveCoulomb.CoulombPermutation
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.MeanValue

/-! Actual common-phase rotations and Gibbs invariance. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

def coulombPhaseRotation (N : ℕ) (c : Circle) : CoulombConfig N ≃ₗᵢ[ℝ] CoulombConfig N :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin N => rotation c)

theorem coulombPhaseRotation_apply (N : ℕ) (c : Circle) (z : CoulombConfig N) (i : Fin N) :
    coulombPhaseRotation N c z i = (c : ℂ) * z i := rfl

theorem coulombPhaseRotation_eq_smul (N : ℕ) (c : Circle) (z : CoulombConfig N) :
    coulombPhaseRotation N c z = (c : ℂ) • z := by
  ext i
  rfl

theorem coulombWeight_phase {N : ℕ} (β : ℝ) (c : Circle) (z : CoulombConfig N) :
    coulombWeight β (coulombPhaseRotation N c z) = coulombWeight β z := by
  unfold coulombWeight
  rw [(coulombPhaseRotation N c).norm_map]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [coulombPhaseRotation_apply, coulombPhaseRotation_apply, ← mul_sub, norm_mul,
    Circle.norm_coe, one_mul]

theorem coulombPhaseRotation_volume_preserving (N : ℕ) (c : Circle) :
    MeasurePreserving (coulombPhaseRotation N c) (volume : Measure (CoulombConfig N)) volume :=
  (coulombPhaseRotation N c).measurePreserving

theorem coulombPhaseRotation_gibbs_preserving {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) (c : Circle) :
    MeasurePreserving (coulombPhaseRotation N c) (coulombMeasure N β) (coulombMeasure N β) := by
  refine ⟨(coulombPhaseRotation N c).continuous.measurable, ?_⟩
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (coulombPhaseRotation N c).continuous.measurable,
    coulombMeasure_lintegral hβ (F := fun z => F (coulombPhaseRotation N c z))
      (hF.comp (coulombPhaseRotation N c).continuous.measurable),
    coulombMeasure_lintegral hβ hF]
  congr 1
  have hw := (coulombWeight_continuous hβ).measurable.ennreal_ofReal.mul hF
  have he := (coulombPhaseRotation_volume_preserving N c).lintegral_comp hw
  dsimp only [Pi.mul_apply] at he
  simpa only [coulombWeight_phase] using he

theorem coulombPhaseRotation_integral {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) (c : Circle)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : CoulombConfig N → E) :
    (∫ z, F (coulombPhaseRotation N c z) ∂coulombMeasure N β) = ∫ z, F z ∂coulombMeasure N β :=
  (coulombPhaseRotation_gibbs_preserving hβ c).integral_comp
    (coulombPhaseRotation N c).toMeasurableEquiv.measurableEmbedding F

theorem coulomb_entire_phase_average {N : ℕ} {F : CoulombConfig N → ℂ}
    (hF : Differentiable ℂ F) (z : CoulombConfig N) :
    Real.circleAverage (fun w : ℂ => F (w • z)) 0 1 = F 0 := by
  have h : Differentiable ℂ (fun w : ℂ => F (w • z)) :=
    hF.comp (differentiable_id.smul_const z)
  simpa using h.diffContOnCl.circleAverage (c := 0) (R := 1)

end RepulsiveCoulomb
