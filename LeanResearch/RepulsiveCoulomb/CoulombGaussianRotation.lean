import LeanResearch.RepulsiveCoulomb.CoulombGaussianExponential
import LeanResearch.RepulsiveCoulomb.CoulombProductVolume

/-! Literal Mehler rotation invariance of two independent planar Gaussian
variables. The rotation is first an isometry of the actual real Euclidean
configuration space; no false product-sup-norm isometry is used. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal BigOperators
namespace RepulsiveCoulomb

def coulombGaussianEuclideanRotate (a b : ℝ) (z : CoulombConfig 2) : CoulombConfig 2 :=
  WithLp.toLp 2 ![a • z 0 + b • z 1, (-b) • z 0 + a • z 1]

theorem coulombGaussianEuclideanRotate_zero (a b : ℝ) (z : CoulombConfig 2) :
    coulombGaussianEuclideanRotate a b z 0 = a • z 0 + b • z 1 := rfl

theorem coulombGaussianEuclideanRotate_one (a b : ℝ) (z : CoulombConfig 2) :
    coulombGaussianEuclideanRotate a b z 1 = (-b) • z 0 + a • z 1 := rfl

def coulombGaussianEuclideanRotateLinear (a b : ℝ) : CoulombConfig 2 →ₗ[ℝ] CoulombConfig 2 where
  toFun := coulombGaussianEuclideanRotate a b
  map_add' z w := by
    ext i
    fin_cases i
    · change a • (z 0 + w 0) + b • (z 1 + w 1) =
        (a • z 0 + b • z 1) + (a • w 0 + b • w 1)
      module
    · change (-b) • (z 0 + w 0) + a • (z 1 + w 1) =
        ((-b) • z 0 + a • z 1) + ((-b) • w 0 + a • w 1)
      module
  map_smul' r z := by
    ext i
    fin_cases i
    · change a • (r • z 0) + b • (r • z 1) = r • (a • z 0 + b • z 1)
      module
    · change (-b) • (r • z 0) + a • (r • z 1) = r • ((-b) • z 0 + a • z 1)
      module

theorem coulombGaussianEuclideanRotate_left_inv {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1)
    (z : CoulombConfig 2) :
    coulombGaussianEuclideanRotate a (-b) (coulombGaussianEuclideanRotate a b z) = z := by
  ext i
  fin_cases i
  · change a • (a • z 0 + b • z 1) + (-b) • ((-b) • z 0 + a • z 1) = z 0
    calc
      _ = (a ^ 2 + b ^ 2) • z 0 := by module
      _ = _ := by rw [hab, one_smul]
  · change (-(-b)) • (a • z 0 + b • z 1) + a • ((-b) • z 0 + a • z 1) = z 1
    rw [neg_neg]
    calc
      _ = (a ^ 2 + b ^ 2) • z 1 := by module
      _ = _ := by rw [hab, one_smul]

theorem coulombGaussianEuclideanRotate_right_inv {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1)
    (z : CoulombConfig 2) :
    coulombGaussianEuclideanRotate a b (coulombGaussianEuclideanRotate a (-b) z) = z := by
  have hn : a ^ 2 + (-b) ^ 2 = 1 := by simpa only [neg_sq] using hab
  simpa only [neg_neg] using coulombGaussianEuclideanRotate_left_inv hn z

theorem coulombGaussianRotate_norm_sq {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (x y : ℂ) :
    ‖a • x + b • y‖ ^ 2 + ‖(-b) • x + a • y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  calc
    _ = (a ^ 2 + b ^ 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.smul_re, Complex.smul_im, smul_eq_mul]
      ring
    _ = _ := by rw [hab, one_mul]

theorem coulombGaussianEuclideanRotate_norm {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1)
    (z : CoulombConfig 2) : ‖coulombGaussianEuclideanRotate a b z‖ = ‖z‖ := by
  have hsq : ‖coulombGaussianEuclideanRotate a b z‖ ^ 2 = ‖z‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
      coulombGaussianEuclideanRotate_zero, coulombGaussianEuclideanRotate_one]
    exact coulombGaussianRotate_norm_sq hab (z 0) (z 1)
  nlinarith [norm_nonneg (coulombGaussianEuclideanRotate a b z), norm_nonneg z]

def coulombGaussianEuclideanRotateEquiv (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    CoulombConfig 2 ≃ₗᵢ[ℝ] CoulombConfig 2 where
  toLinearEquiv :=
    { coulombGaussianEuclideanRotateLinear a b with
      invFun := coulombGaussianEuclideanRotate a (-b)
      left_inv := coulombGaussianEuclideanRotate_left_inv hab
      right_inv := coulombGaussianEuclideanRotate_right_inv hab }
  norm_map' := coulombGaussianEuclideanRotate_norm hab

def coulombGaussianPairChart : CoulombConfig 2 ≃ᵐ ℂ × ℂ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℂ)).symm.trans MeasurableEquiv.finTwoArrow

theorem coulombGaussianPairChart_measurePreserving : MeasurePreserving coulombGaussianPairChart :=
  (volume_preserving_finTwoArrow ℂ).comp (coulomb_coordinates_volume_preserving 2)

def coulombGaussianRotateEquiv (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    (ℂ × ℂ) ≃ᵐ (ℂ × ℂ) :=
  (coulombGaussianPairChart.symm.trans
    (coulombGaussianEuclideanRotateEquiv a b hab).toMeasurableEquiv).trans coulombGaussianPairChart

theorem coulombGaussianRotateEquiv_apply (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (p : ℂ × ℂ) :
    coulombGaussianRotateEquiv a b hab p = (a • p.1 + b • p.2, (-b) • p.1 + a • p.2) := by
  rfl

theorem coulombGaussianRotate_volume (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    MeasurePreserving (coulombGaussianRotateEquiv a b hab)
      (volume : Measure (ℂ × ℂ)) volume :=
  coulombGaussianPairChart_measurePreserving.comp
    ((coulombGaussianEuclideanRotateEquiv a b hab).measurePreserving.comp
      coulombGaussianPairChart_measurePreserving.symm)

theorem coulombGaussianRotate_density (β a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (p : ℂ × ℂ) :
    coulombGaussianDensity β (coulombGaussianRotateEquiv a b hab p).1 *
      coulombGaussianDensity β (coulombGaussianRotateEquiv a b hab p).2 =
        coulombGaussianDensity β p.1 * coulombGaussianDensity β p.2 := by
  rw [coulombGaussianRotateEquiv_apply]
  unfold coulombGaussianDensity
  simp only [Prod.fst, Prod.snd]
  have h := coulombGaussianRotate_norm_sq hab p.1 p.2
  have he : Real.exp (-β * ‖a • p.1 + b • p.2‖ ^ 2 / 2) *
      Real.exp (-β * ‖(-b) • p.1 + a • p.2‖ ^ 2 / 2) =
      Real.exp (-β * ‖p.1‖ ^ 2 / 2) * Real.exp (-β * ‖p.2‖ ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    calc
      _ = -β * (‖a • p.1 + b • p.2‖ ^ 2 + ‖(-b) • p.1 + a • p.2‖ ^ 2) / 2 := by ring
      _ = _ := by rw [h]; ring
  calc
    _ = (β / (2 * Real.pi)) ^ 2 *
        (Real.exp (-β * ‖a • p.1 + b • p.2‖ ^ 2 / 2) *
          Real.exp (-β * ‖(-b) • p.1 + a • p.2‖ ^ 2 / 2)) := by ring
    _ = (β / (2 * Real.pi)) ^ 2 *
        (Real.exp (-β * ‖p.1‖ ^ 2 / 2) * Real.exp (-β * ‖p.2‖ ^ 2 / 2)) := by rw [he]
    _ = _ := by ring

/-- Literal two-Gaussian density as a density against product volume. -/
theorem coulombCenterGaussian_prod_density {β : ℝ} (hβ : 0 < β) :
    (coulombCenterGaussian β).prod (coulombCenterGaussian β) =
      (volume : Measure (ℂ × ℂ)).withDensity (fun p =>
        ENNReal.ofReal (coulombGaussianDensity β p.1) *
          ENNReal.ofReal (coulombGaussianDensity β p.2)) := by
  rw [coulombCenterGaussian_eq_density hβ]
  unfold equilibriumDensityMeasure
  exact prod_withDensity (coulombGaussianDensity_continuous β).measurable.ennreal_ofReal
    (coulombGaussianDensity_continuous β).measurable.ennreal_ofReal

/-- Mehler rotation preserves the actual independent planar Gaussian law. -/
theorem coulombGaussianRotate_measurePreserving {β : ℝ} (hβ : 0 < β)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    MeasurePreserving (coulombGaussianRotateEquiv a b hab)
      ((coulombCenterGaussian β).prod (coulombCenterGaussian β))
      ((coulombCenterGaussian β).prod (coulombCenterGaussian β)) := by
  refine ⟨(coulombGaussianRotateEquiv a b hab).measurable, ?_⟩
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (coulombGaussianRotateEquiv a b hab).measurable,
    coulombCenterGaussian_prod_density hβ]
  let w : ℂ × ℂ → ℝ≥0∞ := fun p => ENNReal.ofReal (coulombGaussianDensity β p.1) *
    ENNReal.ofReal (coulombGaussianDensity β p.2)
  have hw : Measurable w := by
    exact ((coulombGaussianDensity_continuous β).measurable.comp measurable_fst).ennreal_ofReal.mul
      ((coulombGaussianDensity_continuous β).measurable.comp measurable_snd).ennreal_ofReal
  have hinv (p : ℂ × ℂ) : w (coulombGaussianRotateEquiv a b hab p) = w p := by
    dsimp only [w]
    rw [← ENNReal.ofReal_mul (coulombGaussianDensity_pos hβ _).le,
      ← ENNReal.ofReal_mul (coulombGaussianDensity_pos hβ _).le,
      coulombGaussianRotate_density]
  have hFc : Measurable (fun p => F (coulombGaussianRotateEquiv a b hab p)) :=
    hF.comp (coulombGaussianRotateEquiv a b hab).measurable
  change (∫⁻ p, F (coulombGaussianRotateEquiv a b hab p) ∂volume.withDensity w) =
    ∫⁻ p, F p ∂volume.withDensity w
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hFc,
    lintegral_withDensity_eq_lintegral_mul _ hw hF]
  change (∫⁻ p, w p * F (coulombGaussianRotateEquiv a b hab p)) = ∫⁻ p, w p * F p
  calc
    _ = ∫⁻ p, w (coulombGaussianRotateEquiv a b hab p) *
        F (coulombGaussianRotateEquiv a b hab p) :=
      lintegral_congr fun p => by rw [hinv]
    _ = _ := (coulombGaussianRotate_volume a b hab).lintegral_comp (hw.mul hF)

end RepulsiveCoulomb
