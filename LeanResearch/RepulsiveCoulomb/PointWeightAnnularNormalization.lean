module

public import LeanResearch.RepulsiveCoulomb.PointWeightCircularLower
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Annular proof of the configuration-uniform normalization in manuscript
Lemma 3.3. This uses the already established circle Jensen bound rather than
enumerating the unit-disk logarithmic potential. Polar coordinates, their
radial Jacobian, and the angular interval are identified explicitly below.
The annular argument gives another admissible constant, not the manuscript's
particular displayed unit-disk constant.
-/
noncomputable section
open MeasureTheory Real Filter Set
open scoped ENNReal BigOperators Topology
namespace RepulsiveCoulomb

theorem polarCoord_symm_eq_circleMap (R θ : ℝ) :
    Complex.polarCoord.symm (R, θ) = circleMap 0 R θ := by
  simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]

theorem continuous_complex_polarCoord_symm : Continuous Complex.polarCoord.symm := by
  have he : (Complex.polarCoord.symm : ℝ × ℝ → ℂ) =
      (fun p ↦ (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I)) := by
    funext p
    exact Complex.polarCoord_symm_apply p
  rw [he]
  fun_prop

theorem angularIntegral_eq_circleAverage (f : ℂ → ℝ) (R : ℝ) :
    (∫ θ in (-Real.pi)..Real.pi, f (Complex.polarCoord.symm (R, θ))) =
      (2 * Real.pi) * Real.circleAverage f 0 R := by
  simp_rw [polarCoord_symm_eq_circleMap]
  have h := Real.circleAverage_eq_integral_add (f := f) (c := 0) (R := R) (-Real.pi)
  rw [intervalIntegral.integral_comp_add_right (fun θ ↦ f (circleMap 0 R θ)) (-Real.pi)] at h
  have he : 2 * Real.pi + -Real.pi = Real.pi := by ring
  simp only [zero_add, he, smul_eq_mul] at h
  rw [h]
  field_simp

theorem angularLIntegral_eq_circleAverage (f : ℂ → ℝ) (hf : Continuous f)
    (hf0 : ∀ z, 0 ≤ f z) (R : ℝ) :
    (∫⁻ θ in Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal (f (Complex.polarCoord.symm (R, θ)))) =
      ENNReal.ofReal ((2 * Real.pi) * Real.circleAverage f 0 R) := by
  have hc : Continuous (fun θ : ℝ ↦ f (Complex.polarCoord.symm (R, θ))) :=
    hf.comp (continuous_complex_polarCoord_symm.comp (continuous_const.prodMk continuous_id))
  have hi : IntegrableOn (fun θ : ℝ ↦ f (Complex.polarCoord.symm (R, θ)))
      (Ioo (-Real.pi) Real.pi) :=
    hc.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun θ ↦ hf0 _))]
  congr 1
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  exact angularIntegral_eq_circleAverage f R

theorem pointPartition_polar {m : ℕ} (γ : ℝ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    pointPartition γ a y = ∫⁻ R in Ioi (0 : ℝ),
      ENNReal.ofReal R * ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal (pointWeight γ a y (Complex.polarCoord.symm (R, θ))) := by
  rw [pointPartition, ← Complex.lintegral_comp_polarCoord_symm]
  simp only [smul_eq_mul, polarCoord_target]
  change (∫⁻ p : ℝ × ℝ, ENNReal.ofReal p.1 *
      ENNReal.ofReal (pointWeight γ a y (Complex.polarCoord.symm p))
      ∂(volume.prod volume).restrict (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi)) = _
  rw [← Measure.prod_restrict]
  have hm : Measurable (fun p : ℝ × ℝ ↦ ENNReal.ofReal p.1 *
      ENNReal.ofReal (pointWeight γ a y (Complex.polarCoord.symm p))) :=
    measurable_fst.ennreal_ofReal.mul
      (((pointWeight_continuous γ ha y).comp continuous_complex_polarCoord_symm).measurable.ennreal_ofReal)
  rw [lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr
  intro R
  have hθ : Measurable (fun θ : ℝ ↦
      ENNReal.ofReal (pointWeight γ a y (Complex.polarCoord.symm (R, θ)))) :=
    (((pointWeight_continuous γ ha y).comp
      (continuous_complex_polarCoord_symm.comp (continuous_const.prodMk continuous_id))).measurable.ennreal_ofReal)
  exact lintegral_const_mul (ENNReal.ofReal R) hθ


/-- A configuration-independent positive constant from the annulus 1 < |z| ≤ 2.
We use the lower bound one for the radial Jacobian, not omit that Jacobian. -/
def pointLowerConstant (γ Q : ℝ) : ℝ :=
  (2 * Real.pi) * Real.exp (-2 * γ - Q * Real.log 2)

theorem pointLowerConstant_pos (γ Q : ℝ) : 0 < pointLowerConstant γ Q := by
  unfold pointLowerConstant
  positivity

theorem pointPartition_lower_uniform {m : ℕ} {γ Q : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q)
    (y : Fin m → ℂ) :
    ENNReal.ofReal (pointLowerConstant γ Q * pointLocationFactor a y) ≤
      pointPartition γ a y := by
  have havoid : ∀ᵐ R : ℝ, ∀ j, R ≠ ‖y j‖ :=
    ae_all_iff.mpr (fun j ↦ volume.ae_ne (‖y j‖))
  have hpoint : ∀ᵐ R ∂volume.restrict (Ioc (1 : ℝ) 2),
      ENNReal.ofReal (pointLowerConstant γ Q * pointLocationFactor a y) ≤
      ENNReal.ofReal R * ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal (pointWeight γ a y (Complex.polarCoord.symm (R, θ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae havoid] with R hR hav
    have hc := pointWeight_circleAverage_lower hγ ha hQ y hR.1.le hR.2 hav
    have hlow : ENNReal.ofReal (pointLowerConstant γ Q * pointLocationFactor a y) ≤
        ∫⁻ θ in Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal (pointWeight γ a y (Complex.polarCoord.symm (R, θ))) := by
      rw [angularLIntegral_eq_circleAverage _ (pointWeight_continuous γ ha y)
        (pointWeight_nonneg γ a y)]
      apply ENNReal.ofReal_le_ofReal
      calc
        pointLowerConstant γ Q * pointLocationFactor a y =
            (2 * Real.pi) * (Real.exp (-2 * γ - Q * Real.log 2) * pointLocationFactor a y) :=
          mul_assoc _ _ _
        _ ≤ (2 * Real.pi) * Real.circleAverage (pointWeight γ a y) 0 R :=
          mul_le_mul_of_nonneg_left hc Real.two_pi_pos.le
    have hR' : (1 : ENNReal) ≤ ENNReal.ofReal R := by
      simpa using ENNReal.ofReal_le_ofReal hR.1.le
    refine hlow.trans ?_
    calc
      (∫⁻ θ in Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal (pointWeight γ a y (Complex.polarCoord.symm (R, θ)))) =
          1 * (∫⁻ θ in Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal (pointWeight γ a y (Complex.polarCoord.symm (R, θ)))) := (one_mul _).symm
      _ ≤ ENNReal.ofReal R * (∫⁻ θ in Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal (pointWeight γ a y (Complex.polarCoord.symm (R, θ)))) := by gcongr
  calc
    ENNReal.ofReal (pointLowerConstant γ Q * pointLocationFactor a y) =
        ∫⁻ R in Ioc (1 : ℝ) 2,
          ENNReal.ofReal (pointLowerConstant γ Q * pointLocationFactor a y) := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
      norm_num
    _ ≤ ∫⁻ R in Ioc (1 : ℝ) 2, ENNReal.ofReal R *
        ∫⁻ θ in Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal (pointWeight γ a y (Complex.polarCoord.symm (R, θ))) :=
      lintegral_mono_ae hpoint
    _ ≤ ∫⁻ R in Ioi (0 : ℝ), ENNReal.ofReal R *
        ∫⁻ θ in Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal (pointWeight γ a y (Complex.polarCoord.symm (R, θ))) :=
      lintegral_mono_set (fun R hR ↦ lt_trans zero_lt_one hR.1)
    _ = pointPartition γ a y := (pointPartition_polar γ ha y).symm

end RepulsiveCoulomb
