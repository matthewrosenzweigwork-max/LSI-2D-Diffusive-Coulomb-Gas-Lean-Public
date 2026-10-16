import LeanResearch.RepulsiveCoulomb.CoulombGaussianInterpolation
import LeanResearch.RepulsiveCoulomb.CoulombGaussianRotatedIntegration
import LeanResearch.RepulsiveCoulomb.CoulombGaussianFisher

/-! Actual differentiation of Gaussian entropy along the Mehler interpolation.
The analytic exchange of derivative and both Gaussian integrals is justified
by explicit bounded-data/first-moment estimates. Rotation and Gaussian IBP
then identify the derivative with Fisher information. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace
namespace RepulsiveCoulomb

/-- Elementary derivative of u log u on a positive branch. -/
theorem coulombGaussian_hasDerivAt_mul_log {u : ℝ → ℝ} {u' s : ℝ}
    (hu : HasDerivAt u u' s) (hp : 0 < u s) :
    HasDerivAt (fun s => u s * Real.log (u s)) ((1 + Real.log (u s)) * u') s := by
  convert hu.mul (hu.log hp.ne') using 1
  field_simp
  ring

/-- The raw entropy derivative, prior to the integration-by-parts identity. -/
theorem coulombGaussianInterpolationEntropy_hasDerivAt_raw {β s : ℝ} (hβ : 0 < β)
    {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {m M D : ℝ}
    (hM : ∀ z, ‖g z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ g z‖ ≤ D)
    (hm : 0 < m) (hfm : ∀ z, m ≤ g z) (hs : 0 < s) (hs1 : s < 1) :
    HasDerivAt (coulombGaussianInterpolationEntropy β g)
      (∫ x, (1 + Real.log (coulombGaussianInterpolation β s g x)) *
        coulombGaussianInterpolationDerivative β s g x ∂coulombCenterGaussian β) s := by
  letI := coulombCenterGaussian_isProbability hβ
  let U : ℝ := (s + 1) / 2
  have hsU : s < U := by dsimp [U]; linarith
  have hU : U < 1 := by dsimp [U]; linarith
  let L : ℝ := 1 + |Real.log m| + |Real.log M|
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0)
  have hD0 : 0 ≤ D := (norm_nonneg (fderiv ℝ g 0)).trans (hD 0)
  have hPc (r : ℝ) : Continuous (coulombGaussianInterpolation β r g) :=
    (coulombGaussianAverage_contDiff_one hβ hg hM hD _ _).continuous
  have hPlo (r : ℝ) (x : ℂ) : m ≤ coulombGaussianInterpolation β r g x :=
    coulombGaussianAverage_lower hβ hg.continuous hM hfm _ _ x
  have hPpos (r : ℝ) (x : ℂ) : 0 < coulombGaussianInterpolation β r g x := hm.trans_le (hPlo r x)
  have hPhi (r : ℝ) : Integrable (fun x => coulombGaussianInterpolation β r g x *
      Real.log (coulombGaussianInterpolation β r g x)) (coulombCenterGaussian β) := by
    apply (integrable_const (M * (|Real.log m| + |Real.log M|))).mono'
      ((hPc r).mul ((hPc r).log (fun x => (hPpos r x).ne'))).aestronglyMeasurable
    filter_upwards [] with x
    dsimp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs (Real.log _)]
    have hPn := coulombGaussianAverage_norm_le hβ hM r (coulombGaussianInterpolationNoise r) x
    have hPu : coulombGaussianInterpolation β r g x ≤ M := (le_abs_self _).trans hPn
    exact mul_le_mul hPn (coulombGaussian_log_bound hm (hPlo r x) hPu) (abs_nonneg _) hM0
  have hi : Integrable (fun x : ℂ => L * (D * (‖x‖ +
      (coulombGaussianInterpolationNoise U)⁻¹ *
        ∫ y : ℂ, ‖y‖ ∂coulombCenterGaussian β))) (coulombCenterGaussian β) :=
    (((coulombGaussian_norm_integrable hβ).add (integrable_const _)).const_mul D).const_mul L
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := coulombCenterGaussian β) (s := Ioo 0 U)
    (F := fun r x => coulombGaussianInterpolation β r g x *
      Real.log (coulombGaussianInterpolation β r g x))
    (F' := fun r x => (1 + Real.log (coulombGaussianInterpolation β r g x)) *
      coulombGaussianInterpolationDerivative β r g x)
    (bound := fun x => L * (D * (‖x‖ + (coulombGaussianInterpolationNoise U)⁻¹ *
      ∫ y : ℂ, ‖y‖ ∂coulombCenterGaussian β)))
    (Ioo_mem_nhds hs hsU)
    (Eventually.of_forall (fun r => (hPhi r).aestronglyMeasurable))
    (hPhi s) ?_ (Eventually.of_forall (fun x r hr => ?_)) hi
    (Eventually.of_forall (fun x r hr => ?_))).2
  · exact ((continuous_const.add ((hPc s).log (fun x => (hPpos s x).ne'))).stronglyMeasurable.mul
      (coulombGaussianInterpolationDerivative_stronglyMeasurable hβ hg s)).aestronglyMeasurable
  · rw [norm_mul]
    exact mul_le_mul
      (coulombGaussianAverage_log_multiplier_bound hβ hg.continuous hm hfm hM _ _ x)
      (coulombGaussianInterpolationDerivative_norm_le hβ hD hr.1.le hr.2.le hU x)
      (norm_nonneg _) hL
  · exact coulombGaussian_hasDerivAt_mul_log
      (coulombGaussianInterpolation_hasDerivAt hβ hg hM hD hr.1 hr.2 hU x) (hPpos r x)

/-- The tangent of the interpolation is the rotated noise direction. -/
theorem coulombGaussianInterpolationVelocity_rotated {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s < 1) (x y : ℂ) :
    coulombGaussianInterpolationVelocity s x y =
      (-(coulombGaussianInterpolationNoise s)⁻¹) •
        ((-coulombGaussianInterpolationNoise s) • x + s • y) := by
  have hb := (coulombGaussianInterpolationNoise_pos hs hs1).ne'
  unfold coulombGaussianInterpolationVelocity
  rw [smul_add, smul_smul, smul_smul]
  simp only [neg_mul_neg, inv_mul_cancel₀ hb, one_smul]
  congr 1
  congr 1
  ring

/-- The exact Fisher representation of the differentiated actual integral. -/
theorem coulombGaussianInterpolationEntropy_raw_eq_fisher {β s : ℝ} (hβ : 0 < β)
    {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {m M D : ℝ}
    (hM : ∀ z, ‖g z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ g z‖ ≤ D)
    (hm : 0 < m) (hfm : ∀ z, m ≤ g z) (hs : 0 < s) (hs1 : s < 1) :
    (∫ x, (1 + Real.log (coulombGaussianInterpolation β s g x)) *
        coulombGaussianInterpolationDerivative β s g x ∂coulombCenterGaussian β) =
      (1 / (β * s)) * ∫ x, coulombGaussianFisherDensity (coulombGaussianInterpolation β s g) x
        ∂coulombCenterGaussian β := by
  let μ := coulombCenterGaussian β
  letI : IsProbabilityMeasure μ := coulombCenterGaussian_isProbability hβ
  let b := coulombGaussianInterpolationNoise s
  let P := coulombGaussianInterpolation β s g
  let h : ℂ → ℝ := fun x => 1 + Real.log (P x)
  let L := 1 + |Real.log m| + |Real.log M|
  let A : ℂ × ℂ → ℝ := fun p => h p.1 *
    fderiv ℝ g (s • p.1 + b • p.2) ((-b) • p.1 + s • p.2)
  let B : ℂ × ℂ → ℝ := fun p =>
    fderiv ℝ h p.1 (gradient g (s • p.1 + b • p.2))
  have hb : 0 < b := coulombGaussianInterpolationNoise_pos hs.le hs1
  have hab : s ^ 2 + b ^ 2 = 1 := coulombGaussianInterpolationNoise_sq hs.le hs1.le
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hD0 : 0 ≤ D := (norm_nonneg (fderiv ℝ g 0)).trans (hD 0)
  have hh : ContDiff ℝ 1 h := coulombGaussianAverage_log_multiplier_contDiff hβ hg hm hfm hM hD s b
  have hMh : ∀ x, ‖h x‖ ≤ L := coulombGaussianAverage_log_multiplier_bound hβ hg.continuous hm hfm hM s b
  have hDh : ∀ x, ‖fderiv ℝ h x‖ ≤ (|s| * D) / m :=
    coulombGaussianAverage_log_multiplier_fderiv_bound hβ hg hm hfm hM hD s b
  have hcg := hg.continuous_fderiv (by norm_num)
  have hch := hh.continuous_fderiv (by norm_num)
  have hcgrad : Continuous (gradient g) := (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp hcg
  have hgrad (z : ℂ) : ‖gradient g z‖ ≤ D := by
    rw [TauCeti.norm_gradient_eq_norm_fderiv]
    exact hD z
  have hAi : Integrable A (μ.prod μ) := by
    apply ((((coulombGaussian_norm_integrable hβ).comp_fst μ).const_mul |b|).add
      (((coulombGaussian_norm_integrable hβ).comp_snd μ).const_mul |s|) |>.const_mul (L * D)).mono'
      (by dsimp [A]; fun_prop)
    filter_upwards [] with p
    dsimp only [A]
    rw [norm_mul]
    have hv : ‖(-b) • p.1 + s • p.2‖ ≤ |b| * ‖p.1‖ + |s| * ‖p.2‖ := by
      simpa [norm_smul, Real.norm_eq_abs] using norm_add_le ((-b) • p.1) (s • p.2)
    have hd := (ContinuousLinearMap.le_opNorm (fderiv ℝ g (s • p.1 + b • p.2))
      ((-b) • p.1 + s • p.2)).trans
      (mul_le_mul (hD (s • p.1 + b • p.2)) hv (norm_nonneg _) hD0)
    exact (mul_le_mul (hMh _) hd (norm_nonneg _) hL).trans_eq (by dsimp only [Pi.add_apply]; ring)
  have hBi : Integrable B (μ.prod μ) := by
    apply (integrable_const (((|s| * D) / m) * D)).mono' (by dsimp [B]; fun_prop)
    filter_upwards [] with p
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hDh _) (hgrad _) (norm_nonneg _) (by positivity))
  have hR : (∫ x, h x * coulombGaussianInterpolationDerivative β s g x ∂μ) =
      -b⁻¹ * ∫ p, A p ∂μ.prod μ := by
    rw [integral_prod _ hAi, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    unfold coulombGaussianInterpolationDerivative
    simp_rw [coulombGaussianInterpolationVelocity_rotated hs.le hs1,
      map_smul, smul_eq_mul]
    rw [integral_const_mul]
    dsimp only [A]
    rw [integral_const_mul]
    dsimp only [b]
    ring
  have hB : s * (∫ p, B p ∂μ.prod μ) =
      ∫ x, coulombGaussianFisherDensity P x ∂μ := by
    rw [integral_prod _ hBi, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    have hgi : Integrable (fun y => gradient g (s • x + b • y)) μ := by
      apply (integrable_const D).mono' (by fun_prop)
      exact Eventually.of_forall (fun y => hgrad _)
    have hgav := coulombGaussianAverage_gradient hβ hg hM hD s b x
    have hdf := coulombGaussianAverage_log_multiplier_fderiv hβ hg hm hfm hM hD s b x
    have hp : 0 < P x := hm.trans_le (coulombGaussianAverage_lower hβ hg.continuous hM hfm s b x)
    dsimp only [B]
    rw [ContinuousLinearMap.integral_comp_comm _ hgi, ← smul_eq_mul,
      ← map_smul, ← hgav]
    change fderiv ℝ (fun z => 1 + Real.log (coulombGaussianAverage β s b g z)) x
        (gradient (coulombGaussianAverage β s b g) x) =
      coulombGaussianFisherDensity (coulombGaussianAverage β s b g) x
    rw [hdf]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ← inner_gradient_left,
      real_inner_self_eq_norm_sq, coulombGaussianFisherDensity,
      TauCeti.norm_gradient_eq_norm_fderiv]
    ring
  have hIBP := coulombGaussian_rotated_integrationByParts hβ hg hh hM hD hMh hDh s b hab
  change β * (∫ p, A p ∂μ.prod μ) = -b * (∫ p, B p ∂μ.prod μ) at hIBP
  change (∫ x, h x * coulombGaussianInterpolationDerivative β s g x ∂μ) = _
  rw [hR, ← hB]
  apply (mul_left_cancel₀ (show β * b ≠ 0 from mul_ne_zero hβ.ne' hb.ne'))
  field_simp [hβ.ne', hb.ne', hs.ne']
  nlinarith [hIBP]

/-- The actual sharp entropy derivative; every exchange, invariance and
integration-by-parts statement used here has been proved for this integral. -/
theorem coulombGaussianInterpolationEntropy_hasDerivAt {β s : ℝ} (hβ : 0 < β)
    {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {m M D : ℝ}
    (hM : ∀ z, ‖g z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ g z‖ ≤ D)
    (hm : 0 < m) (hfm : ∀ z, m ≤ g z) (hs : 0 < s) (hs1 : s < 1) :
    HasDerivAt (coulombGaussianInterpolationEntropy β g)
      ((1 / (β * s)) * ∫ x, coulombGaussianFisherDensity (coulombGaussianInterpolation β s g) x
        ∂coulombCenterGaussian β) s := by
  rw [← coulombGaussianInterpolationEntropy_raw_eq_fisher hβ hg hM hD hm hfm hs hs1]
  exact coulombGaussianInterpolationEntropy_hasDerivAt_raw hβ hg hM hD hm hfm hs hs1

end RepulsiveCoulomb
