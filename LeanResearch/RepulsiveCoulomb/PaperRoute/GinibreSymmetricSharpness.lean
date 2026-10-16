module

public import LeanResearch.RepulsiveCoulomb.CoulombBoundedSmoothDomain
public import LeanResearch.RepulsiveCoulomb.CoulombCenterCylinderGeometry
public import LeanResearch.RepulsiveCoulomb.CoulombHelmertCoordinates
public import LeanResearch.RepulsiveCoulomb.CoulombGaussianIntegrationByParts
public import LeanResearch.RepulsiveCoulomb.PaperRoute.AnalyticLabeledPoincare

@[expose] public section

/-! The literal linear center-of-mass equality modes of the original physical
closed form. The unbounded observable is placed in the prescribed form by
actual ambient outer cutoffs. Its second moment is computed by integrable
Gaussian density integration by parts. No Gaussian sharp-LSI result is used.
-/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace InnerProductSpace ProbabilityTheory
open scoped Topology ENNReal BigOperators
namespace RepulsiveCoulomb.PaperRoute

/-- All planar Gaussian linear observables are genuinely square integrable. -/
theorem paper_gaussian_linear_memLp {β : ℝ} (hβ : 0 < β) (a : ℂ) :
    MemLp (fun c : ℂ => inner ℝ a c) 2 (coulombCenterGaussian β) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  apply ((coulombGaussian_norm_sq_integrable hβ).const_mul (‖a‖ ^ 2)).mono'
    (by fun_prop)
  filter_upwards [] with c
  change ‖inner ℝ a c ^ 2‖ ≤ ‖a‖ ^ 2 * ‖c‖ ^ 2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs, mul_pow] using
    (sq_le_sq₀ (abs_nonneg (inner ℝ a c))
      (mul_nonneg (norm_nonneg a) (norm_nonneg c))).2 (abs_real_inner_le_norm a c)

theorem paper_gaussian_linear_mean {β : ℝ} (hβ : 0 < β) (a : ℂ) :
    (∫ c : ℂ, inner ℝ a c ∂coulombCenterGaussian β) = 0 := by
  rw [integral_coulombCenterGaussian hβ]
  have h := integral_neg_eq_self
    (fun c : ℂ => coulombGaussianDensity β c * inner ℝ a c) volume
  simp only [coulombGaussianDensity_neg, inner_neg_right, mul_neg, integral_neg] at h
  linarith

/-- Integrable Haar integration by parts applies to the unbounded linear
function. In particular no bounded-C¹ Gaussian IBP premise is misapplied. -/
theorem paper_gaussian_linear_second_moment {β : ℝ} (hβ : 0 < β) (a : ℂ) :
    (∫ c : ℂ, inner ℝ a c ^ 2 ∂coulombCenterGaussian β) = ‖a‖ ^ 2 / β := by
  let _ := coulombCenterGaussian_isProbability hβ
  have hL2 := paper_gaussian_linear_memLp hβ a
  have h1 : Integrable (fun c : ℂ => inner ℝ a c) (coulombCenterGaussian β) :=
    MemLp.integrable (by norm_num) hL2
  have h1' := (coulombCenterGaussian_integrable_iff hβ _).mp h1
  have h2' := (coulombCenterGaussian_integrable_iff hβ _).mp hL2.integrable_sq
  have hd (c : ℂ) :
      fderiv ℝ (fun z : ℂ => inner ℝ a z) c a = ‖a‖ ^ 2 := by
    change fderiv ℝ (innerSL ℝ a) c a = ‖a‖ ^ 2
    rw [(innerSL ℝ a).fderiv]
    exact real_inner_self_eq_norm_sq a
  have hs :
      (fun c : ℂ => fderiv ℝ (coulombGaussianDensity β) c a * inner ℝ a c) =
      (fun c : ℂ => -β * (coulombGaussianDensity β c * inner ℝ a c ^ 2)) := by
    funext c
    rw [coulombGaussianDensity_fderiv, real_inner_comm c a]
    ring
  have hi1 : Integrable
      (fun c : ℂ => fderiv ℝ (coulombGaussianDensity β) c a * inner ℝ a c) := by
    rw [hs]
    simpa only [mul_left_comm, mul_comm, mul_assoc] using h2'.const_mul (-β)
  have hi2 : Integrable
      (fun c : ℂ => coulombGaussianDensity β c *
        fderiv ℝ (fun z : ℂ => inner ℝ a z) c a) := by
    simp_rw [hd]
    exact (coulombGaussianDensity_integrable hβ).mul_const _
  have hi0 : Integrable
      (fun c : ℂ => coulombGaussianDensity β c * inner ℝ a c) := by
    simpa only [mul_comm] using h1'
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ)) (f := coulombGaussianDensity β)
    (g := fun c : ℂ => inner ℝ a c) (v := a) hi1 hi2 hi0
    (fun c _ => (coulombGaussianDensity_hasFDerivAt β c).differentiableAt)
    (fun c _ => (innerSL ℝ a).differentiableAt)
  rw [hs] at hibp
  simp_rw [hd] at hibp
  rw [integral_mul_const, coulombGaussianDensity_mass hβ, integral_const_mul] at hibp
  rw [integral_coulombCenterGaussian hβ]
  apply (eq_div_iff hβ.ne').2
  nlinarith [hibp]

/-- The existing ambient cutoff also applies to unbounded square-integrable
smooth functions. Its value error is dominated by the actual square. -/
theorem paper_smooth_L2_cutoff_value (m : ℕ) {β : ℝ} (_hβ : 0 < β)
    (f : CoulombConfig (m + 2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hi : MemLp f 2 (coulombMeasure (m + 2) β)) :
    Tendsto (fun n ↦ ∫ z, (coulombBoundedSmoothCutoff m n f hf z - f z) ^ 2
      ∂coulombMeasure (m + 2) β) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence
    (μ := coulombMeasure (m + 2) β)
    (F := fun n z ↦ (coulombBoundedSmoothCutoff m n f hf z - f z) ^ 2)
    (f := fun _ ↦ (0 : ℝ)) (fun z ↦ f z ^ 2)
    (fun n ↦ ((coulombBoundedSmoothCutoff m n f hf).continuous.sub hf.continuous).pow 2
      |>.aestronglyMeasurable) hi.integrable_sq ?_ ?_
  · simpa only [integral_zero] using h
  · intro n
    exact Eventually.of_forall fun z ↦ by
      have h0 := (coulombOuterBump m (pointOuterRadius n) (pointOuterRadius_pos n)).nonneg (x := z)
      have h1 := (coulombOuterBump m (pointOuterRadius n) (pointOuterRadius_pos n)).le_one (x := z)
      have hq : |coulombOuterTestFunction m n z - 1| ≤ 1 := by
        change |coulombOuterBump m (pointOuterRadius n) (pointOuterRadius_pos n) z - 1| ≤ 1
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      have he : |coulombBoundedSmoothCutoff m n f hf z - f z| ≤ |f z| := by
        change |coulombOuterTestFunction m n z * f z - f z| ≤ |f z|
        rw [← sub_one_mul, abs_mul]
        simpa using mul_le_mul_of_nonneg_right hq (abs_nonneg (f z))
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) he 2
  · exact Eventually.of_forall fun z ↦ by
      have ht := ((coulombOuterTestFunction_tendsto_one m z).mul_const (f z)).sub_const (f z)
      simpa [coulombBoundedSmoothCutoff] using ht.pow 2

private theorem paper_sum_bound_sq {x y z : ℝ} (hx : 0 ≤ x) (h : x ≤ y + z) :
    x ^ 2 ≤ 2 * y ^ 2 + 2 * z ^ 2 := by
  have hs := pow_le_pow_left₀ hx h 2
  nlinarith only [hs, sq_nonneg (y - z)]

set_option maxHeartbeats 1200000 in
/-- Bounded physical gradient and L² value suffice for the gradient convergence
of the genuine ambient cutoffs; the value itself need not be bounded. -/
theorem paper_smooth_L2_cutoff_gradient (m : ℕ) {β : ℝ} (hβ : 0 < β)
    (f : CoulombConfig (m + 2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hi : MemLp f 2 (coulombMeasure (m + 2) β))
    (B : ℝ) (hgb : ∀ z, ‖gradient f z‖ ≤ B) :
    Tendsto (fun n ↦ ∫ z,
      ‖gradient (coulombBoundedSmoothCutoff m n f hf : CoulombConfig (m + 2) → ℝ) z -
        gradient f z‖ ^ 2 ∂coulombMeasure (m + 2) β) atTop (𝓝 0) := by
  let _ := coulombMeasure_isProbability (N := m + 2) hβ
  have hgc : Continuous (gradient f) := (hf.gradient_right (m := 0) (by simp)).continuous
  obtain ⟨C, hC, hc⟩ := coulombOuterBump_gradient_bound m
  have hcut (n : ℕ) (z : CoulombConfig (m + 2)) :
      ‖gradient (coulombOuterTestFunction m n : CoulombConfig (m + 2) → ℝ) z‖ ≤ C := by
    have hR : 1 ≤ pointOuterRadius n := by simp [pointOuterRadius]
    exact (hc (pointOuterRadius n) (pointOuterRadius_pos n) z).trans
      (div_le_self hC.le hR)
  have hconst : Integrable (fun _ : CoulombConfig (m + 2) => 8 * B ^ 2)
      (coulombMeasure (m + 2) β) := integrable_const _
  have hquad : Integrable (fun z : CoulombConfig (m + 2) => (2 * C ^ 2) * f z ^ 2)
      (coulombMeasure (m + 2) β) := hi.integrable_sq.const_mul (2 * C ^ 2)
  have hmajor : Integrable (fun z : CoulombConfig (m + 2) => 8 * B ^ 2 + (2 * C ^ 2) * f z ^ 2)
      (coulombMeasure (m + 2) β) := hconst.add hquad
  have h := tendsto_integral_of_dominated_convergence
    (μ := coulombMeasure (m + 2) β)
    (F := fun n z ↦ ‖gradient (coulombBoundedSmoothCutoff m n f hf :
      CoulombConfig (m + 2) → ℝ) z - gradient f z‖ ^ 2)
    (f := fun _ ↦ (0 : ℝ)) (fun z ↦ 8 * B ^ 2 + (2 * C ^ 2) * f z ^ 2)
    (fun n ↦ ((TauCeti.continuous_gradient_testFunction
      (coulombBoundedSmoothCutoff m n f hf)).sub hgc).norm.pow 2 |>.aestronglyMeasurable)
    hmajor ?_ ?_
  · simpa only [integral_zero] using h
  · intro n
    exact Eventually.of_forall fun z ↦ by
      have h0 := (coulombOuterBump m (pointOuterRadius n) (pointOuterRadius_pos n)).nonneg (x := z)
      have h1 := (coulombOuterBump m (pointOuterRadius n) (pointOuterRadius_pos n)).le_one (x := z)
      have hq : |coulombOuterTestFunction m n z| ≤ 1 := by
        change |coulombOuterBump m (pointOuterRadius n) (pointOuterRadius_pos n) z| ≤ 1
        rwa [abs_of_nonneg h0]
      have hp : ‖gradient (coulombBoundedSmoothCutoff m n f hf :
          CoulombConfig (m + 2) → ℝ) z‖ ≤ B + |f z| * C := by
        rw [coulombBoundedSmoothCutoff_gradient]
        calc
          _ ≤ ‖coulombOuterTestFunction m n z • gradient f z‖ +
              ‖f z • gradient (coulombOuterTestFunction m n : CoulombConfig (m + 2) → ℝ) z‖ :=
            norm_add_le _ _
          _ = |coulombOuterTestFunction m n z| * ‖gradient f z‖ +
              |f z| * ‖gradient (coulombOuterTestFunction m n : CoulombConfig (m + 2) → ℝ) z‖ := by
            simp only [norm_smul, Real.norm_eq_abs]
          _ ≤ 1 * B + |f z| * C := add_le_add
            (mul_le_mul hq (hgb z) (norm_nonneg _) (by norm_num))
            (mul_le_mul_of_nonneg_left (hcut n z) (abs_nonneg _))
          _ = B + |f z| * C := by ring
      have he : ‖gradient (coulombBoundedSmoothCutoff m n f hf :
          CoulombConfig (m + 2) → ℝ) z - gradient f z‖ ≤ 2 * B + |f z| * C := by
        exact (norm_sub_le
          (gradient (coulombBoundedSmoothCutoff m n f hf : CoulombConfig (m + 2) → ℝ) z)
          (gradient f z)).trans (by linarith only [hp, hgb z])
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc
        _ ≤ 2 * (2 * B) ^ 2 + 2 * (|f z| * C) ^ 2 := paper_sum_bound_sq (norm_nonneg _) he
        _ = 8 * B ^ 2 + (2 * C ^ 2) * f z ^ 2 := by simp only [mul_pow, sq_abs]; ring
  · exact Eventually.of_forall fun z ↦ by
      have hfirst := (coulombOuterTestFunction_tendsto_one m z).smul
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ gradient f z) atTop (𝓝 (gradient f z)))
      have hsecond := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ f z) atTop (𝓝 (f z))).smul
        (coulombOuterTestFunction_gradient_tendsto_zero m z)
      have ht := ((hfirst.add hsecond).sub_const (gradient f z)).norm.pow 2
      simpa only [coulombBoundedSmoothCutoff_gradient, one_smul, smul_zero, add_zero,
        sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using ht

/-- A square-integrable globally smooth function with bounded physical gradient
is an actual element of the original collision-free-core closure. -/
theorem paper_smooth_L2_bounded_gradient_lift (m : ℕ) {β : ℝ} (hβ : 0 < β)
    (f : CoulombConfig (m + 2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hi : MemLp f 2 (coulombMeasure (m + 2) β))
    (B : ℝ) (hgb : ∀ z, ‖gradient f z‖ ≤ B) :
    ∃ u : CoulombFormDomain (m + 2) hβ,
      coulombFormValueL (m + 2) hβ u =ᵐ[coulombMeasure (m + 2) β] f ∧
      coulombFormGradientL (m + 2) hβ u =ᵐ[coulombMeasure (m + 2) β] gradient f := by
  let _ := coulombMeasure_isProbability (N := m + 2) hβ
  have hgc : Continuous (gradient f) := (hf.gradient_right (m := 0) (by simp)).continuous
  have hg : MemLp (gradient f) 2 (coulombMeasure (m + 2) β) :=
    MemLp.of_bound hgc.aestronglyMeasurable B (Eventually.of_forall hgb)
  have hj : MemLp (fun z ↦ WithLp.toLp 2 (f z, gradient f z)) 2
      (coulombMeasure (m + 2) β) := by
    apply MemLp.of_fst_of_snd_prodLp
    exact ⟨by simpa only [WithLp.toLp_fst] using hi,
      by simpa only [WithLp.toLp_snd] using hg⟩
  let J : CoulombJetL2 (m + 2) β := hj.toLp _
  have hJ : J =ᵐ[coulombMeasure (m + 2) β]
      (fun z ↦ WithLp.toLp 2 (f z, gradient f z)) := MemLp.coeFn_toLp _
  have hv : coulombJetValueL (m + 2) β J =ᵐ[coulombMeasure (m + 2) β] f := by
    filter_upwards [coulombJetValueL_coe (m + 2) β J, hJ] with z hz hJz
    simpa only [hJz, WithLp.toLp_fst] using hz
  have hgrad : coulombJetGradientL (m + 2) β J =ᵐ[coulombMeasure (m + 2) β] gradient f := by
    filter_upwards [coulombJetGradientL_coe (m + 2) β J, hJ] with z hz hJz
    simpa only [hJz, WithLp.toLp_snd] using hz
  have ht : Tendsto (fun n ↦ coulombAmbientJet m hβ (coulombBoundedSmoothCutoff m n f hf))
      atTop (𝓝 J) := by
    apply coulombJet_tendsto_of_components m
    · apply coulomb_L2_tendsto_of_sq_integral m
      convert paper_smooth_L2_cutoff_value m hβ f hf hi using 1
      ext n
      apply integral_congr_ae
      filter_upwards [coulombAmbientJet_value m hβ (coulombBoundedSmoothCutoff m n f hf), hv]
        with z hz hvz
      simp only [hz, hvz, Real.norm_eq_abs, sq_abs]
    · apply coulomb_L2_tendsto_of_sq_integral m
      convert paper_smooth_L2_cutoff_gradient m hβ f hf hi B hgb using 1
      ext n
      apply integral_congr_ae
      filter_upwards [coulombAmbientJet_gradient m hβ (coulombBoundedSmoothCutoff m n f hf), hgrad]
        with z hz hgz
      simp only [hz, hgz]
  have hclosed : J ∈ coulombCoreGraph (m + 2) hβ :=
    isClosed_closure.mem_of_tendsto ht (Eventually.of_forall fun n ↦
      coulombAmbientJet_mem_closedCore m hβ (coulombBoundedSmoothCutoff m n f hf))
  let u : CoulombFormDomain (m + 2) hβ := ⟨J, by
    change J ∈ (coulombFormSubmodule (m + 2) hβ : Set _)
    rw [coe_coulombFormSubmodule]
    exact hclosed⟩
  exact ⟨u, hv, hgrad⟩

/-- The physical normalized center coordinate, with N=m+2. -/
def paperCenterOfMass (m : ℕ) (z : CoulombConfig (m + 2)) : ℂ :=
  coulombCenterProjection (coulombHelmertRotation (m + 1)) z

theorem paperCenterOfMass_formula (m : ℕ) (z : CoulombConfig (m + 2)) :
    paperCenterOfMass m z =
      ((Real.sqrt (m + 2 : ℝ))⁻¹ : ℂ) * ∑ j, z j := by
  unfold paperCenterOfMass
  rw [coulombCenterProjection_apply, coulombHelmertRotation_apply]
  simpa only [Nat.cast_add, Nat.cast_one,
    show (m : ℝ) + 1 + 1 = (m : ℝ) + 2 by ring] using
    coulombHelmertEquiv_zero (m + 1) z

theorem paperCenterOfMass_permute (m : ℕ) (σ : Equiv.Perm (Fin (m + 2)))
    (z : CoulombConfig (m + 2)) :
    paperCenterOfMass m (coulombPermute σ z) = paperCenterOfMass m z := by
  rw [paperCenterOfMass_formula, paperCenterOfMass_formula]
  congr 1
  simp only [coulombPermute_apply]
  exact Equiv.sum_comp σ (fun j => z j)

def paperCenterLinearObservable (m : ℕ) (a : ℂ) (z : CoulombConfig (m + 2)) : ℝ :=
  inner ℝ a (paperCenterOfMass m z)

theorem paperCenterLinearObservable_contDiff (m : ℕ) (a : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (paperCenterLinearObservable m a) :=
  (innerSL ℝ a).contDiff.comp (coulombCenterProjection (coulombHelmertRotation (m + 1))).contDiff

theorem paper_linear_gradient (a c : ℂ) :
    gradient (fun z : ℂ => inner ℝ a z) c = a := by
  apply (toDual ℝ ℂ).injective
  rw [toDual_gradient]
  change fderiv ℝ (innerSL ℝ a) c = toDual ℝ ℂ a
  rw [(innerSL ℝ a).fderiv]
  rfl

theorem paperCenterLinearObservable_gradient (m : ℕ) (a : ℂ)
    (z : CoulombConfig (m + 2)) :
    gradient (paperCenterLinearObservable m a) z =
      (coulombHelmertRotation (m + 1)).symm (coulombCoordinateInjection (m + 2) 0 a) := by
  unfold paperCenterLinearObservable paperCenterOfMass
  rw [coulombCenter_center_cylinder_gradient (coulombHelmertRotation (m + 1))
    (f := fun c : ℂ => inner ℝ a c) z
    (innerSL ℝ a).differentiableAt, paper_linear_gradient]

theorem paperCenterLinearObservable_gradient_norm (m : ℕ) (a : ℂ)
    (z : CoulombConfig (m + 2)) :
    ‖gradient (paperCenterLinearObservable m a) z‖ = ‖a‖ := by
  rw [paperCenterLinearObservable_gradient, (coulombHelmertRotation (m + 1)).symm.norm_map,
    coulombCoordinateInjection_norm]

theorem paperCenterLinearObservable_memLp (m : ℕ) {β : ℝ} (hβ : 0 < β) (a : ℂ) :
    MemLp (paperCenterLinearObservable m a) 2 (coulombMeasure (m + 2) β) :=
  (paper_gaussian_linear_memLp hβ a).comp_measurePreserving
    (coulombCenterProjection_measurePreserving (coulombHelmertRotation (m + 1))
      (coulombHelmertRotation_axis (m + 1)) hβ)

theorem paperCenterLinearObservable_mean (m : ℕ) {β : ℝ} (hβ : 0 < β) (a : ℂ) :
    (∫ z, paperCenterLinearObservable m a z ∂coulombMeasure (m + 2) β) = 0 := by
  change (∫ z, inner ℝ a (coulombCenterProjection (coulombHelmertRotation (m + 1)) z)
    ∂coulombMeasure (m + 2) β) = 0
  rw [coulombCenter_projection_integral
    (f := fun c : ℂ => inner ℝ a c)
    (coulombCenterProjection_measurePreserving (coulombHelmertRotation (m + 1))
      (coulombHelmertRotation_axis (m + 1)) hβ) (by fun_prop),
    paper_gaussian_linear_mean hβ a]

theorem paperCenterLinearObservable_second_moment (m : ℕ) {β : ℝ}
    (hβ : 0 < β) (a : ℂ) :
    (∫ z, paperCenterLinearObservable m a z ^ 2 ∂coulombMeasure (m + 2) β) = ‖a‖ ^ 2 / β := by
  change (∫ z, inner ℝ a (coulombCenterProjection (coulombHelmertRotation (m + 1)) z) ^ 2
    ∂coulombMeasure (m + 2) β) = _
  rw [coulombCenter_projection_integral
    (f := fun c : ℂ => inner ℝ a c ^ 2)
    (coulombCenterProjection_measurePreserving (coulombHelmertRotation (m + 1))
      (coulombHelmertRotation_axis (m + 1)) hβ) (by fun_prop),
    paper_gaussian_linear_second_moment hβ a]

/-- The literal linear center mode is in the original closed form, is symmetric,
and has exact mean, variance, and physical energy. -/
theorem paper_center_linear_form_witness (m : ℕ) {β : ℝ} (hβ : 0 < β) (a : ℂ) :
    ∃ u : CoulombFormDomain (m + 2) hβ,
      coulombFormValueL (m + 2) hβ u =ᵐ[coulombMeasure (m + 2) β]
        paperCenterLinearObservable m a ∧
      coulombFormGradientL (m + 2) hβ u =ᵐ[coulombMeasure (m + 2) β]
        (fun _ => (coulombHelmertRotation (m + 1)).symm
          (coulombCoordinateInjection (m + 2) 0 a)) ∧
      (∀ σ : Equiv.Perm (Fin (m + 2)),
        coulombValuePermuteL (m + 2) hβ σ (coulombFormValueL (m + 2) hβ u) =
          coulombFormValueL (m + 2) hβ u) ∧
      (∫ z, coulombFormValueL (m + 2) hβ u z ∂coulombMeasure (m + 2) β) = 0 ∧
      variance (coulombFormValueL (m + 2) hβ u : CoulombConfig (m + 2) → ℝ)
        (coulombMeasure (m + 2) β) = ‖a‖ ^ 2 / β ∧
      coulombFormEnergy (m + 2) hβ u = ‖a‖ ^ 2 := by
  let _ := coulombMeasure_isProbability (N := m + 2) hβ
  obtain ⟨u, hv, hg⟩ := paper_smooth_L2_bounded_gradient_lift m hβ
    (paperCenterLinearObservable m a) (paperCenterLinearObservable_contDiff m a)
    (paperCenterLinearObservable_memLp m hβ a) ‖a‖
    (fun z => (paperCenterLinearObservable_gradient_norm m a z).le)
  refine ⟨u, hv, ?_, ?_, ?_, ?_, ?_⟩
  · exact hg.mono fun z hz => hz.trans (paperCenterLinearObservable_gradient m a z)
  · intro σ
    apply Lp.ext
    have hp := (coulombPermute_gibbs_preserving hβ.le σ).quasiMeasurePreserving.ae hv
    filter_upwards [coulombValuePermuteL_coe (m + 2) hβ σ (coulombFormValueL (m + 2) hβ u),
      hv, hp] with z hz hvz hpz
    rw [hz, hvz, hpz]
    unfold paperCenterLinearObservable
    rw [paperCenterOfMass_permute]
  · exact (integral_congr_ae hv).trans (paperCenterLinearObservable_mean m hβ a)
  · rw [variance_congr hv, variance_eq_sub (paperCenterLinearObservable_memLp m hβ a)]
    change (∫ z, paperCenterLinearObservable m a z ^ 2 ∂coulombMeasure (m + 2) β) -
      (∫ z, paperCenterLinearObservable m a z ∂coulombMeasure (m + 2) β) ^ 2 = _
    rw [paperCenterLinearObservable_second_moment m hβ a, paperCenterLinearObservable_mean m hβ a]
    ring
  · rw [coulombFormEnergy_eq_integral]
    calc
      _ = ∫ z, ‖gradient (paperCenterLinearObservable m a) z‖ ^ 2
          ∂coulombMeasure (m + 2) β :=
        integral_congr_ae (hg.mono fun z hz => congrArg (fun v => ‖v‖ ^ 2) hz)
      _ = ‖a‖ ^ 2 := by simp [paperCenterLinearObservable_gradient_norm]

/-- The real part of the literal normalized center is an equality witness. -/
theorem paper_center_real_form_witness (m : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∃ u : CoulombFormDomain (m + 2) hβ,
      coulombFormValueL (m + 2) hβ u =ᵐ[coulombMeasure (m + 2) β]
        (fun z => (paperCenterOfMass m z).re) ∧
      (∀ σ : Equiv.Perm (Fin (m + 2)),
        coulombValuePermuteL (m + 2) hβ σ (coulombFormValueL (m + 2) hβ u) =
          coulombFormValueL (m + 2) hβ u) ∧
      (∫ z, coulombFormValueL (m + 2) hβ u z ∂coulombMeasure (m + 2) β) = 0 ∧
      variance (coulombFormValueL (m + 2) hβ u : CoulombConfig (m + 2) → ℝ)
        (coulombMeasure (m + 2) β) = 1 / β ∧
      coulombFormEnergy (m + 2) hβ u = 1 := by
  obtain ⟨u, hv, _, hs, hm, hvar, hE⟩ := paper_center_linear_form_witness m hβ (1 : ℂ)
  refine ⟨u, ?_, hs, hm, ?_, ?_⟩
  · exact hv.mono fun z hz => by simpa [paperCenterLinearObservable, Complex.inner] using hz
  · simpa using hvar
  · simpa using hE

/-- The imaginary part is a second, equally normalized symmetric witness. -/
theorem paper_center_imaginary_form_witness (m : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∃ u : CoulombFormDomain (m + 2) hβ,
      coulombFormValueL (m + 2) hβ u =ᵐ[coulombMeasure (m + 2) β]
        (fun z => (paperCenterOfMass m z).im) ∧
      (∀ σ : Equiv.Perm (Fin (m + 2)),
        coulombValuePermuteL (m + 2) hβ σ (coulombFormValueL (m + 2) hβ u) =
          coulombFormValueL (m + 2) hβ u) ∧
      (∫ z, coulombFormValueL (m + 2) hβ u z ∂coulombMeasure (m + 2) β) = 0 ∧
      variance (coulombFormValueL (m + 2) hβ u : CoulombConfig (m + 2) → ℝ)
        (coulombMeasure (m + 2) β) = 1 / β ∧
      coulombFormEnergy (m + 2) hβ u = 1 := by
  obtain ⟨u, hv, _, hs, hm, hvar, hE⟩ := paper_center_linear_form_witness m hβ Complex.I
  refine ⟨u, ?_, hs, hm, ?_, ?_⟩
  · exact hv.mono fun z hz => by
      simpa [paperCenterLinearObservable, Complex.inner, Complex.mul_re] using hz
  · simpa using hvar
  · simpa using hE

/-- Every symmetric PI coefficient on the original full form must be at least
1/β, by direct testing on its nonconstant real center mode. -/
theorem paper_symmetric_poincare_coefficient_lower_bound (m : ℕ) {β C : ℝ}
    (hβ : 0 < β)
    (hPI : ∀ u : CoulombFormDomain (m + 2) hβ,
      (∀ σ : Equiv.Perm (Fin (m + 2)),
        coulombValuePermuteL (m + 2) hβ σ (coulombFormValueL (m + 2) hβ u) =
          coulombFormValueL (m + 2) hβ u) →
      variance (coulombFormValueL (m + 2) hβ u : CoulombConfig (m + 2) → ℝ)
        (coulombMeasure (m + 2) β) ≤ C * coulombFormEnergy (m + 2) hβ u) :
    1 / β ≤ C := by
  obtain ⟨u, _, hs, _, hvar, hE⟩ := paper_center_real_form_witness m hβ
  simpa only [hvar, hE, mul_one] using hPI u hs

/-- Included exponent-two endpoint, in the literal unit-droplet normalization. -/
theorem paper_ginibre_symmetric_poincare (m : ℕ)
    (hβ : 0 < 2 * ((m + 2 : ℕ) : ℝ))
    (u : CoulombFormDomain (m + 2) hβ)
    (hs : ∀ σ : Equiv.Perm (Fin (m + 2)),
      coulombValuePermuteL (m + 2) hβ σ (coulombFormValueL (m + 2) hβ u) =
        coulombFormValueL (m + 2) hβ u) :
    variance (coulombFormValueL (m + 2) hβ u : CoulombConfig (m + 2) → ℝ)
      (coulombMeasure (m + 2) (2 * ((m + 2 : ℕ) : ℝ))) ≤
        (1 / (2 * ((m + 2 : ℕ) : ℝ))) * coulombFormEnergy (m + 2) hβ u := by
  apply paper_symmetric_poincare_small_exponent hβ _ u hs
  have hN : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  exact (div_le_iff₀ hN).2 (le_refl _)

/-- Sharpness means exactly that the full symmetric PI holds with C if and
only if C is at least 1/(2N). The lower direction uses the actual linear form
element above, not a Gaussian logarithmic-Sobolev witness. -/
theorem paper_ginibre_symmetric_poincare_iff (m : ℕ)
    (hβ : 0 < 2 * ((m + 2 : ℕ) : ℝ)) (C : ℝ) :
    (∀ u : CoulombFormDomain (m + 2) hβ,
      (∀ σ : Equiv.Perm (Fin (m + 2)),
        coulombValuePermuteL (m + 2) hβ σ (coulombFormValueL (m + 2) hβ u) =
          coulombFormValueL (m + 2) hβ u) →
      variance (coulombFormValueL (m + 2) hβ u : CoulombConfig (m + 2) → ℝ)
        (coulombMeasure (m + 2) (2 * ((m + 2 : ℕ) : ℝ))) ≤
          C * coulombFormEnergy (m + 2) hβ u) ↔ 1 / (2 * ((m + 2 : ℕ) : ℝ)) ≤ C := by
  constructor
  · exact paper_symmetric_poincare_coefficient_lower_bound m hβ
  · intro hC u hs
    exact (paper_ginibre_symmetric_poincare m hβ u hs).trans
      (mul_le_mul_of_nonneg_right hC (coulombFormEnergy_nonneg (m + 2) hβ u))

/-- The arbitrary-N sharp symmetric Ginibre statement has no analytic premise:
its sole particle-count restriction is the original N≥2. -/
theorem paper_ginibre_symmetric_poincare_sharp_all_N (N : ℕ) (hN : 2 ≤ N) (C : ℝ) :
    let hβ : 0 < 2 * (N : ℝ) := by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      exact mul_pos (by norm_num) hNpos
    (∀ u : CoulombFormDomain N hβ,
      (∀ σ : Equiv.Perm (Fin N),
        coulombValuePermuteL N hβ σ (coulombFormValueL N hβ u) =
          coulombFormValueL N hβ u) →
      variance (coulombFormValueL N hβ u : CoulombConfig N → ℝ)
        (coulombMeasure N (2 * (N : ℝ))) ≤ C * coulombFormEnergy N hβ u) ↔
      1 / (2 * (N : ℝ)) ≤ C := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  exact paper_ginibre_symmetric_poincare_iff m (by positivity) C

/-- Explicit real and imaginary equality witnesses at beta=2N. Both modes
have unit physical energy, so their variance is positive and the equality is
attained by nonconstant symmetric original-domain observables. -/
theorem paper_ginibre_center_equality_witnesses (m : ℕ) :
    let β : ℝ := 2 * ((m + 2 : ℕ) : ℝ)
    let hβ : 0 < β := by dsimp [β]; positivity
    ∃ u v : CoulombFormDomain (m + 2) hβ,
      coulombFormValueL (m + 2) hβ u =ᵐ[coulombMeasure (m + 2) β]
        (fun z => (paperCenterOfMass m z).re) ∧
      coulombFormValueL (m + 2) hβ v =ᵐ[coulombMeasure (m + 2) β]
        (fun z => (paperCenterOfMass m z).im) ∧
      (∀ w ∈ ({u, v} : Set (CoulombFormDomain (m + 2) hβ)),
        (∀ σ : Equiv.Perm (Fin (m + 2)),
          coulombValuePermuteL (m + 2) hβ σ (coulombFormValueL (m + 2) hβ w) =
            coulombFormValueL (m + 2) hβ w) ∧
        variance (coulombFormValueL (m + 2) hβ w : CoulombConfig (m + 2) → ℝ)
          (coulombMeasure (m + 2) β) = 1 / (2 * ((m + 2 : ℕ) : ℝ)) ∧
        coulombFormEnergy (m + 2) hβ w = 1) := by
  dsimp only
  have hβ : 0 < 2 * ((m + 2 : ℕ) : ℝ) := by positivity
  obtain ⟨u, hu, hsu, _, hvu, hEu⟩ := paper_center_real_form_witness m hβ
  obtain ⟨v, hv, hsv, _, hvv, hEv⟩ := paper_center_imaginary_form_witness m hβ
  refine ⟨u, v, hu, hv, ?_⟩
  intro w hw
  rcases Set.mem_insert_iff.mp hw with rfl | hw
  · exact ⟨hsu, hvu, hEu⟩
  · have he : w = v := Set.mem_singleton_iff.mp hw
    subst w
    exact ⟨hsv, hvv, hEv⟩

end RepulsiveCoulomb.PaperRoute
