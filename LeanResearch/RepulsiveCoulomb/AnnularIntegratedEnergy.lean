module

public import LeanResearch.RepulsiveCoulomb.AnnularProductEnergy

@[expose] public section

/-! Integral localization on the actual enlarged annulus. Compact-set
integrability is supplied explicitly, without assuming compact support of psi. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

def enlargedScoreAnnulus (R : ℝ) : Set ℂ := {x | R / 2 < ‖x‖ ∧ ‖x‖ < 4 * R}

theorem enlargedScoreAnnulus_measurable (R : ℝ) : MeasurableSet (enlargedScoreAnnulus R) :=
  (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (isOpen_lt continuous_norm continuous_const).measurableSet

theorem continuous_integrableOn_enlargedScoreAnnulus {f : ℂ → ℝ}
    (hf : Continuous f) (R : ℝ) : IntegrableOn f (enlargedScoreAnnulus R) := by
  apply (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) (4 * R))).mono_set
  intro x hx
  exact mem_closedBall.mpr (by simpa only [dist_zero_right] using hx.2.le)

theorem annular_product_mass_le {R : ℝ} (hR : 0 < R)
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) :
    (∫ x : ℂ, (annularCutoff R x * ψ x) ^ 2) ≤
      ∫ x in enlargedScoreAnnulus R, ψ x ^ 2 := by
  have he : (∫ x in enlargedScoreAnnulus R, (annularCutoff R x * ψ x) ^ 2) =
      ∫ x : ℂ, (annularCutoff R x * ψ x) ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hn : x ∉ tsupport (annularCutoff R) := fun h => hx (annularCutoff_tsupport_strict hR h)
    simp [image_eq_zero_of_notMem_tsupport hn]
  rw [← he]
  apply setIntegral_mono_on
    (continuous_integrableOn_enlargedScoreAnnulus (((annularCutoff_contDiff R).continuous.mul hψ).pow 2) R)
    (continuous_integrableOn_enlargedScoreAnnulus (hψ.pow 2) R)
    (enlargedScoreAnnulus_measurable R)
  intro x hx
  have hc := annularCutoff_mem_Icc R x
  have hsq : (annularCutoff R x) ^ 2 ≤ 1 := by nlinarith [hc.1, hc.2]
  change (annularCutoff R x * ψ x) ^ 2 ≤ ψ x ^ 2
  rw [mul_pow]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq (sq_nonneg (ψ x))

theorem annular_product_energy_le {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hbound : ∀ z : ℂ, ‖gradient (annularCutoff R) z‖ ≤ C / R)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    (∫ x : ℂ, ‖gradient (fun z => annularCutoff R z * ψ z) x‖ ^ 2) ≤
      2 * (∫ x in enlargedScoreAnnulus R, ‖gradient ψ x‖ ^ 2) +
        2 * (C / R) ^ 2 * (∫ x in enlargedScoreAnnulus R, ψ x ^ 2) := by
  have hg : Continuous (gradient ψ) :=
    (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp (hψ.continuous_fderiv one_ne_zero)
  have hp : ContDiff ℝ 1 (fun z => annularCutoff R z * ψ z) :=
    ((annularCutoff_contDiff R).of_le (by simp)).mul hψ
  have hgp : Continuous (gradient (fun z => annularCutoff R z * ψ z)) :=
    (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp (hp.continuous_fderiv one_ne_zero)
  have hi : IntegrableOn (fun x => ‖gradient ψ x‖ ^ 2) (enlargedScoreAnnulus R) :=
    continuous_integrableOn_enlargedScoreAnnulus (hg.norm.pow 2) R
  have hv : IntegrableOn (fun x => ψ x ^ 2) (enlargedScoreAnnulus R) :=
    continuous_integrableOn_enlargedScoreAnnulus (hψ.continuous.pow 2) R
  have he : (∫ x in enlargedScoreAnnulus R, ‖gradient (fun z => annularCutoff R z * ψ z) x‖ ^ 2) =
      ∫ x : ℂ, ‖gradient (fun z => annularCutoff R z * ψ z) x‖ ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [annular_product_gradient_zero_off hR hψ hx]
    simp
  rw [← he]
  calc
    _ ≤ ∫ x in enlargedScoreAnnulus R,
        (2 * ‖gradient ψ x‖ ^ 2 + 2 * (C / R) ^ 2 * ψ x ^ 2) :=
      setIntegral_mono_on (continuous_integrableOn_enlargedScoreAnnulus (hgp.norm.pow 2) R)
        (continuous_integrableOn_enlargedScoreAnnulus (by fun_prop) R)
        (enlargedScoreAnnulus_measurable R) (fun x _ => annular_product_gradient_sq_le hR hC hbound hψ x)
    _ = _ := by rw [integral_add (hi.const_mul 2) (hv.const_mul (2 * (C / R) ^ 2)), integral_const_mul, integral_const_mul]

theorem pointScore_bad_annulus_localized {R C γ Q δ : ℝ} {m : ℕ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (hbound : ∀ z : ℂ, ‖gradient (annularCutoff R) z‖ ≤ C / R)
    (hγ : 0 < γ) (hδ : 0 < δ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hQ : ∑ j, a j ≤ Q)
    (ψ : ℂ → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    R ^ 2 * (∫ x in pointScoreBadAnnulus γ a y R, ψ x ^ 2) ≤
      δ * R ^ 2 * (∫ x in enlargedScoreAnnulus R, ψ x ^ 2) +
      pointScoreAnnularMassConstant γ Q ^ 2 / (4 * δ) *
        (2 * (∫ x in enlargedScoreAnnulus R, ‖gradient ψ x‖ ^ 2) +
          2 * (C / R) ^ 2 * (∫ x in enlargedScoreAnnulus R, ψ x ^ 2)) := by
  apply (pointScore_bad_annulus_mass_young hγ hR hδ ha y hQ ψ hψ).trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (annular_product_mass_le hR hψ.continuous) (by positivity)
  · exact mul_le_mul_of_nonneg_left (annular_product_energy_le hR hC hbound hψ) (by positivity)

theorem exists_uniform_annular_localized_bound : ∃ C : ℝ, 0 < C ∧
    ∀ {m : ℕ} {γ Q R δ : ℝ}, 0 < γ → 0 < R → 0 < δ →
    ∀ {a : Fin m → ℝ}, (∀ j, 0 ≤ a j) → ∀ y : Fin m → ℂ,
    (∑ j, a j ≤ Q) → ∀ ψ : ℂ → ℝ, ContDiff ℝ 1 ψ →
    R ^ 2 * (∫ x in pointScoreBadAnnulus γ a y R, ψ x ^ 2) ≤
      δ * R ^ 2 * (∫ x in enlargedScoreAnnulus R, ψ x ^ 2) +
      pointScoreAnnularMassConstant γ Q ^ 2 / (4 * δ) *
        (2 * (∫ x in enlargedScoreAnnulus R, ‖gradient ψ x‖ ^ 2) +
          2 * (C / R) ^ 2 * (∫ x in enlargedScoreAnnulus R, ψ x ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := exists_annularCutoff_gradient_bound
  refine ⟨C, hC, ?_⟩
  intro m γ Q R δ hγ hR hδ a ha y hQ ψ hψ
  exact pointScore_bad_annulus_localized hR hC.le (hb R hR) hγ hδ ha y hQ ψ hψ

end RepulsiveCoulomb
