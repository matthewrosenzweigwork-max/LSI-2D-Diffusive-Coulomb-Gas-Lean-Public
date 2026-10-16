import LeanResearch.RepulsiveCoulomb.CoulombSymmetricPairs
import LeanResearch.RepulsiveCoulomb.CoulombProductVolume

/-! Actual label permutations preserve the physical Euclidean metric and Gibbs law. -/
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators ENNReal
namespace RepulsiveCoulomb

def coulombPermute {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    CoulombConfig N ≃ₗᵢ[ℝ] CoulombConfig N :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℂ σ.symm

theorem coulombPermute_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (z : CoulombConfig N) (i : Fin N) :
    coulombPermute σ z i = z (σ i) := rfl

theorem coulombInteraction_permute {N : ℕ} (α : ℝ) (σ : Equiv.Perm (Fin N)) (z : CoulombConfig N) :
    coulombInteraction α (coulombPermute σ z) = coulombInteraction α z := by
  have hs : coulombInteraction α (coulombPermute σ z) ^ 2 = coulombInteraction α z ^ 2 := by
    rw [coulombInteraction_sq, coulombInteraction_sq]
    simp only [coulombPermute_apply]
    refine Fintype.prod_equiv σ _ _ (fun i => ?_)
    refine Fintype.prod_equiv σ _ _ (fun j => ?_)
    simp only [Equiv.apply_eq_iff_eq]
  nlinarith [coulombInteraction_nonneg α (coulombPermute σ z), coulombInteraction_nonneg α z]

theorem coulombWeight_permute {N : ℕ} (β : ℝ) (σ : Equiv.Perm (Fin N)) (z : CoulombConfig N) :
    coulombWeight β (coulombPermute σ z) = coulombWeight β z := by
  rw [coulombWeight_eq_atExponent, coulombWeight_eq_atExponent]
  unfold coulombWeightAtExponent
  rw [(coulombPermute σ).norm_map, coulombInteraction_permute]

theorem coulombPermute_mem_domain {N : ℕ} (σ : Equiv.Perm (Fin N)) (z : CoulombConfig N) :
    coulombPermute σ z ∈ coulombDomain N ↔ z ∈ coulombDomain N := by
  change coulombVandermonde (coulombPermute σ z) ≠ 0 ↔ coulombVandermonde z ≠ 0
  rw [coulombVandermonde_ne_zero_iff, coulombVandermonde_ne_zero_iff]
  constructor
  · intro h i j hij
    have he := h (σ.symm i) (σ.symm j) (fun hh => hij (σ.symm.injective hh))
    simpa only [coulombPermute_apply, Equiv.apply_symm_apply] using he
  · intro h i j hij
    exact h (σ i) (σ j) (fun hh => hij (σ.injective hh))

theorem coulombPermute_volume_preserving {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (coulombPermute σ) (volume : Measure (CoulombConfig N)) volume :=
  (coulombPermute σ).measurePreserving

theorem coulombMeasure_lintegral {N : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    {F : CoulombConfig N → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z ∂coulombMeasure N β) =
      (coulombPartition N β)⁻¹ * ∫⁻ z, ENNReal.ofReal (coulombWeight β z) * F z := by
  rw [coulombMeasure, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul volume (coulombWeight_continuous hβ).measurable.ennreal_ofReal hF]
  rfl

theorem coulombPermute_gibbs_preserving {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (coulombPermute σ) (coulombMeasure N β) (coulombMeasure N β) := by
  refine ⟨(coulombPermute σ).continuous.measurable, ?_⟩
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (coulombPermute σ).continuous.measurable,
    coulombMeasure_lintegral hβ (F := fun z => F (coulombPermute σ z))
      (hF.comp (coulombPermute σ).continuous.measurable),
    coulombMeasure_lintegral hβ hF]
  congr 1
  have hw := (coulombWeight_continuous hβ).measurable.ennreal_ofReal.mul hF
  have he := (coulombPermute_volume_preserving σ).lintegral_comp hw
  dsimp only [Pi.mul_apply] at he
  simpa only [coulombWeight_permute] using he

end RepulsiveCoulomb

