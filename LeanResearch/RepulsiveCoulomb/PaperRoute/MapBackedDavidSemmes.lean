module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.SemmesMetricDoubling
public import LeanResearch.RepulsiveCoulomb.PaperRoute.InverseGradientTransport
public import LeanResearch.RepulsiveCoulomb.PaperRoute.PlanarDSPoincare
public import LeanResearch.RepulsiveCoulomb.PaperRoute.BufferedCoverOscillation
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

/-!
# Supplied-map planar David--Semmes and global-C1 weak Poincare

All objects in this module are attached to the supplied homeomorphism. The
image diameter is controlled by the actual same-map Semmes gauge and doubling,
and the zeroth-order weighted transport is proved from signed area. No raw
point-grid estimate, radial comparison, or downstream PI certificate is used.

The public producer composes analytic QC to weak quasisymmetry, same-map
Semmes gauge and doubling, actual connected-cover oscillation with finite
punctures, and signed-area/cofactor inverse-gradient transport. The additional
inverse hypothesis is local Lipschitz regularity off an explicit finite set;
this is not asserted for general analytic QC maps. All constants are fixed by
K and C before choosing a source ball, test function, or point configuration.
The final Poincare conclusions concern global C1 test functions only.
-/

noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology

namespace RepulsiveCoulomb.PaperRoute

/-- Diameter balls of two points of the closed source ball lie in the exact
open double ball, including when both points are on the boundary. -/
theorem euclideanDiameterBall_subset_doubleBall {c x y : ℂ} {r : ℝ}
    (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    euclideanDiameterBall x y ⊆ ball c (2 * r) := by
  have hm : (x + y) / 2 ∈ closedBall c r := by
    have heq : midpoint ℝ x y = (x + y) / 2 := by
      rw [midpoint_eq_smul_add]
      simp
      ring
    rw [← heq]
    exact (convex_closedBall c r).midpoint_mem hx hy
  have hxy : dist x y ≤ 2 * r := by
    have ht := dist_triangle x c y
    have hx' : dist x c ≤ r := hx
    have hy' : dist c y ≤ r := by simpa only [mem_closedBall, dist_comm] using hy
    linarith
  intro z hz
  have hz' : dist z ((x + y) / 2) < dist x y / 2 := hz
  have hm' : dist ((x + y) / 2) c ≤ r := hm
  have ht := dist_triangle z ((x + y) / 2) c
  show dist z c < 2 * r
  linarith

/-- The target diameter bound is genuinely obtained from the same pullback
metric's diameter gauge and the measure's doubling inequality. -/
theorem image_closedBall_diam_le_of_gauge_doubling
    (F : ℂ ≃ₜ ℂ) {μ : Measure ℂ} {D A : ℝ}
    (hμ : PositiveFiniteBalls μ) (hD : GlobalDoublingWith μ D)
    (hA : GaugeComparable μ (pullbackMetric F) A)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    diam (F '' closedBall c r) ≤ A * Real.sqrt D * Real.sqrt (μ.real (ball c r)) := by
  have hDn : 0 ≤ D := le_trans zero_le_one hD.1
  apply diam_le_of_forall_dist_le (mul_nonneg (mul_nonneg hA.1.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have hmass : (diameterBallMass μ x y).toReal ≤ μ.real (ball c (2 * r)) :=
    ENNReal.toReal_mono (hμ c _ (by positivity)).2.ne
      (measure_mono (euclideanDiameterBall_subset_doubleBall hx hy))
  calc
    dist (F x) (F y) ≤ A * diameterGauge μ x y := by
      simpa only [dist_eq_norm, pullbackMetric_dist] using (hA.2 x y).2
    _ ≤ A * Real.sqrt (μ.real (ball c (2 * r))) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmass) hA.1.le
    _ ≤ A * Real.sqrt (D * μ.real (ball c r)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (PlanarDS.doubling_real hμ hD c hr)) hA.1.le
    _ = A * Real.sqrt D * Real.sqrt (μ.real (ball c r)) := by
      rw [Real.sqrt_mul hDn]
      ring

/-- Nonnegative zeroth-order transport from the lower Jacobian bound, using
actual signed area on the supplied map's image ball. -/
theorem lintegral_weighted_scalar_comp_le_image_ball
    (F : ℂ ≃ₜ ℂ) {w : ℂ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hw : Measurable w)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hRegular : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x)
    (hcompare : ∀ᵐ x ∂volume, w x ≤ C * signedJacobian F x)
    (c : ℂ) (r : ℝ) (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x in ball c r, g (F x) ∂weightMeasure w) ≤
      ENNReal.ofReal C * ∫⁻ z in F '' ball c r, g z := by
  rw [weightMeasure, setLIntegral_withDensity_eq_setLIntegral_mul volume
    (g := fun x => g (F x)) hw.ennreal_ofReal (hg.comp F.continuous.measurable) measurableSet_ball]
  rw [lintegral_image_ball_eq_lintegral_signedJacobian_mul_of_locallyLipschitz
    F.injective hLocal hRegular c r g hg]
  calc
    _ ≤ ∫⁻ x in ball c r,
        ENNReal.ofReal C * (ENNReal.ofReal (signedJacobian F x) * g (F x)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae hcompare] with x hx
      have hb : ENNReal.ofReal (w x) ≤
          ENNReal.ofReal C * ENNReal.ofReal (signedJacobian F x) := by
        simpa only [← ENNReal.ofReal_mul hC] using ENNReal.ofReal_le_ofReal hx
      simpa only [Pi.mul_apply, mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_right hb (g (F x))
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Finite real weighted oscillation transport around any reference value.
Both sides' integrability is independently proved from continuity and compactness. -/
theorem integral_weighted_abs_sub_le_image_ball
    (F : ℂ ≃ₜ ℂ) {f w : ℂ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hw : Measurable w)
    (hμ : PositiveFiniteBalls (weightMeasure w))
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hRegular : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x)
    (hcompare : ∀ᵐ x ∂volume, w x ≤ C * signedJacobian F x)
    (hf : Continuous f) (c : ℂ) {r : ℝ} (hr : 0 < r) (a : ℝ) :
    (∫ x in ball c r, |f x - a| ∂weightMeasure w) ≤
      C * ∫ z in F '' ball c r, |(f ∘ F.symm) z - a| := by
  have hs : IntegrableOn (fun x => |f x - a|) (ball c r) (weightMeasure w) :=
    PlanarDS.continuous_integrableOn_ball hμ (hf.sub continuous_const).abs c hr
  have ht : IntegrableOn (fun z => |(f ∘ F.symm) z - a|) (F '' ball c r) :=
    (((hf.comp F.symm.continuous).sub continuous_const).abs.continuousOn.integrableOn_compact
      (image_closedBall_isCompact F c r)).mono_set (image_mono ball_subset_closedBall)
  have hb := lintegral_weighted_scalar_comp_le_image_ball F hC hw hLocal hRegular hcompare
    c r (fun z => ENNReal.ofReal (|(f ∘ F.symm) z - a|))
    (((hf.comp F.symm.continuous).sub continuous_const).abs.measurable.ennreal_ofReal)
  simp only [Function.comp_apply, F.symm_apply_apply] at hb ht ⊢
  rw [← ofReal_integral_eq_lintegral_ofReal hs
      (Filter.Eventually.of_forall (fun _ => abs_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal ht
      (Filter.Eventually.of_forall (fun _ => abs_nonneg _)),
    ← ENNReal.ofReal_mul hC] at hb
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hC (integral_nonneg (fun _ => abs_nonneg _)))).mp hb

/-- Double oscillation is normalized by the same positive finite measure in
both variables, and can be bounded around an arbitrary real reference. -/
theorem doubleOscillation_le_abs_sub_reference {μ : Measure ℂ}
    (hμ : PositiveFiniteBalls μ) {f : ℂ → ℝ} (hf : Continuous f)
    (c : ℂ) {r : ℝ} (hr : 0 < r) (a : ℝ) :
    PlanarDS.doubleOscillation μ f c r ≤
      2 / μ.real (ball c r) * ∫ x in ball c r, |f x - a| ∂μ := by
  let ν := μ.restrict (ball c r)
  have : IsFiniteMeasure ν := ⟨by simpa [ν] using (hμ c r hr).2⟩
  have : NeZero ν := ⟨by
    intro hz
    have : μ (ball c r) = 0 := by simpa [ν] using congrArg (fun η : Measure ℂ => η univ) hz
    exact (hμ c r hr).1.ne' this⟩
  have hfi : Integrable f ν := PlanarDS.continuous_integrableOn_ball hμ hf c hr
  have hai : Integrable (fun x => |f x - a|) ν := (hfi.sub (integrable_const a)).abs
  have hprod : Integrable (fun p : ℂ × ℂ => |f p.1 - f p.2|) (ν.prod ν) :=
    ((hfi.comp_fst ν).sub (hfi.comp_snd ν)).abs
  have houter : Integrable (fun x => ⨍ y, |f x - f y| ∂ν) ν := by
    simpa only [average_eq, smul_eq_mul] using
      hprod.integral_prod_left.const_mul (ν.real univ)⁻¹
  have hpoint (x : ℂ) : (⨍ y, |f x - f y| ∂ν) ≤
      |f x - a| + ⨍ y, |f y - a| ∂ν := by
    calc
      _ ≤ ⨍ y, |f x - a| + |f y - a| ∂ν := by
        simp only [average_eq, smul_eq_mul]
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
        apply integral_mono ((integrable_const (f x)).sub hfi).abs
          ((integrable_const _).add hai)
        intro y
        calc
          |f x - f y| = |(f x - a) + (a - f y)| := by congr 1; ring
          _ ≤ |f x - a| + |a - f y| := abs_add_le _ _
          _ = |f x - a| + |f y - a| := by rw [abs_sub_comm a]
      _ = _ := by rw [average_fun_add (integrable_const _) hai, average_const]
  calc
    PlanarDS.doubleOscillation μ f c r = ⨍ x, ⨍ y, |f x - f y| ∂ν ∂ν := rfl
    _ ≤ ⨍ x, |f x - a| + ⨍ y, |f y - a| ∂ν ∂ν := by
      simp only [average_eq, smul_eq_mul] at houter hpoint ⊢
      exact mul_le_mul_of_nonneg_left
        (integral_mono houter (hai.add (integrable_const _)) hpoint)
        (inv_nonneg.mpr ENNReal.toReal_nonneg)
    _ = 2 / μ.real (ball c r) * ∫ x in ball c r, |f x - a| ∂μ := by
      rw [average_fun_add hai (integrable_const _), average_const]
      simp only [average_eq, smul_eq_mul, ν, measureReal_restrict_apply_univ]
      ring

/-- The local regularity needed by the punctured target PI follows by actual
composition with the supplied inverse map. -/
theorem locallyLipschitzOn_scalar_comp_symm (F : ℂ ≃ₜ ℂ)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {S : Set ℂ}
    (hlocal : LocallyLipschitzOn S F.symm) :
    LocallyLipschitzOn S (f ∘ F.symm) := by
  rw [locallyLipschitzOn_iff_restrict]
  exact hf.locallyLipschitz.comp hlocal.restrict

/-- Explicit weight doubling produced by the same map's analytic QC bound. -/
def mapBackedDoublingConstant (K C : ℝ) : ℝ :=
  C ^ 2 * semmesDoublingConstant (semmesQCConstant K)

/-- Explicit gauge constant for the literal pullback metric of the same map. -/
def mapBackedGaugeConstant (K C : ℝ) : ℝ :=
  Real.sqrt C * semmesGaugeConstant (semmesQCConstant K)

/-- The exact supplied-map planar David--Semmes constant, fixed before balls
and test functions are selected. -/
def mapBackedDSConstant (K C : ℝ) : ℝ :=
  2 * C * mapBackedGaugeConstant K C *
    bufferedOscillationConstant (weakQSTwoScale (semmesQCConstant K)) *
    Real.sqrt (mapBackedDoublingConstant K C) * Real.sqrt (K * C)

/-- Actual analytic QC and signed Jacobian comparison produce the planar
David--Semmes estimate, with explicit finite-exception inverse regularity.
The latter is an additional geometric hypothesis, discharged separately for
point maps; no inverse regularity is asserted here for general QC maps. -/
theorem planarDSC1_of_analytic_qc_finite_inverse_punctures
    (F : ℂ ≃ₜ ℂ) {w : ℂ → ℝ} {K C : ℝ}
    (hK : 1 ≤ K) (hC : 1 ≤ C) (hw : Continuous w)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hQC : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x ∧
        ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x)
    (hcompare : ∀ᵐ x ∂volume,
      C⁻¹ * w x ≤ signedJacobian F x ∧ signedJacobian F x ≤ C * w x)
    (S : Finset ℂ) (hinverse : LocallyLipschitzOn ((S : Set ℂ)ᶜ) F.symm) :
    PlanarDS.PlanarDSC1 w (mapBackedDSConstant K C) := by
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hQS : WeakQuasisymmetricWith F (semmesQCConstant K) :=
    weakQuasisymmetricWith_of_analytic_qc F hK0 hLocal hQC
  obtain ⟨hμ, hD, hA⟩ := semmes_weight_sameMap_of_analytic_qc F hLocal hK0 hC hQC hcompare
  have hT : 1 ≤ weakQSTwoScale (semmesQCConstant K) := by
    dsimp [weakQSTwoScale]
    nlinarith [hQS.one_le]
  have hRegular : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x :=
    hQC.mono (fun _ hx => ⟨hx.1, hx.2.1⟩)
  have hupper : ∀ᵐ x ∂volume, signedJacobian F x ≤ C * w x :=
    hcompare.mono (fun _ hx => hx.2)
  have hlower : ∀ᵐ x ∂volume, w x ≤ C * signedJacobian F x := by
    filter_upwards [hcompare] with x hx
    have hh : w x / C ≤ signedJacobian F x := by
      simpa only [div_eq_mul_inv, mul_comm] using hx.1
    simpa only [mul_comm] using (div_le_iff₀ hCpos).mp hh
  intro f hf c r hr
  let M := (weightMeasure w).real (ball c r)
  let I := ∫ x in ball c (2 * r), ‖fderiv ℝ f x‖ * Real.sqrt (w x)
  let T := weakQSTwoScale (semmesQCConstant K)
  let A := mapBackedGaugeConstant K C
  let D := mapBackedDoublingConstant K C
  let G := bufferedOscillationConstant T
  have hM : 0 < M := PlanarDS.ballMass_pos hμ c hr
  have hI : 0 ≤ I := integral_nonneg (fun x => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  have hAn : 0 < A := hA.1
  have hDn : 0 ≤ D := le_trans zero_le_one hD.1
  have hGn : 0 ≤ G := by dsimp [G, bufferedOscillationConstant]; positivity
  have hdiam := image_closedBall_diam_le_of_gauge_doubling F hμ hD hA c hr
  obtain ⟨hgradient, htransport⟩ := inverse_gradient_transport_of_contDiff_continuous_weight
    F hK0 hC0 hLocal hRegular (hQC.mono (fun _ hx => hx.2.2)) hupper hf hw c (2 * r)
  have hnt : (F '' closedBall c r).Nontrivial := by
    by_contra hn
    have hz := diam_subsingleton (Set.not_nontrivial_iff.mp hn)
    linarith [image_closedBall_diam_pos F c hr]
  obtain ⟨z, _hz, _hball, hosc⟩ := exists_ballMean_oscillation_le_of_finite_punctures
    (image_closedBall_isCompact F c r) (image_closedBall_isConnected F c hr.le) hnt hT
    (image_ball_isOpen F c (2 * r))
    (fun x hx => hQS.ball_subset_image_doubleBall F.surjective hx)
    (image_ball_isOpen F c r).measurableSet (image_mono ball_subset_closedBall)
    (hf.continuous.comp F.symm.continuous) S
    (locallyLipschitzOn_scalar_comp_symm F hf hinverse) hgradient
  let a := ⨍ y in ball z (4 * BufferedCover.radius (F '' closedBall c r) T), (f ∘ F.symm) y
  have hweighted := integral_weighted_abs_sub_le_image_ball
    F hC0 hw.measurable hμ hLocal hRegular hlower hf.continuous c hr a
  have hs : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
  have hnorm : Real.sqrt M / M = 1 / Real.sqrt M := by
    apply (div_eq_div_iff hM.ne' hs.ne').mpr
    simpa only [one_mul, ← pow_two] using Real.sq_sqrt hM.le
  calc
    PlanarDS.doubleOscillation (weightMeasure w) f c r
        ≤ 2 / M * ∫ x in ball c r, |f x - a| ∂weightMeasure w :=
      doubleOscillation_le_abs_sub_reference hμ hf.continuous c hr a
    _ ≤ 2 / M * (C * ∫ x in F '' ball c r, |(f ∘ F.symm) x - a|) :=
      mul_le_mul_of_nonneg_left hweighted (by positivity)
    _ ≤ 2 / M * (C * (G * diam (F '' closedBall c r) *
        ∫ y in F '' ball c (2 * r), ‖fderiv ℝ (f ∘ F.symm) y‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hosc hC0) (by positivity)
    _ ≤ 2 / M * (C * (G * diam (F '' closedBall c r) * (Real.sqrt (K * C) * I))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htransport (mul_nonneg hGn diam_nonneg)) hC0) (by positivity)
    _ ≤ 2 / M * (C * (G * (A * Real.sqrt D * Real.sqrt M) * (Real.sqrt (K * C) * I))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiam hGn)
          (mul_nonneg (Real.sqrt_nonneg _) hI)) hC0) (by positivity)
    _ = (2 * C * A * G * Real.sqrt D * Real.sqrt (K * C) * I) *
        (Real.sqrt M / M) := by ring
    _ = mapBackedDSConstant K C / Real.sqrt M * I := by
      rw [hnorm]
      dsimp [mapBackedDSConstant, A, D, G, T]
      ring

/-- Positivity of the displayed constant follows from its factors, without
selecting a map, ball, function, or point configuration. -/
theorem mapBackedDSConstant_pos {K C : ℝ} (hK : 1 ≤ K) (hC : 1 ≤ C) :
    0 < mapBackedDSConstant K C := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hH : 0 < semmesQCConstant K := by
    unfold semmesQCConstant
    apply sub_pos.mpr
    apply one_lt_pow₀ _ (by norm_num : (4 : ℕ) ≠ 0)
    linarith [Real.exp_pos (9 * Real.pi ^ 2 * K / (4 * Real.log 2))]
  have hT : 0 < weakQSTwoScale (semmesQCConstant K) := by
    unfold weakQSTwoScale
    positivity
  unfold mapBackedDSConstant mapBackedGaugeConstant mapBackedDoublingConstant
    bufferedOscillationConstant semmesGaugeConstant semmesDoublingConstant
  positivity

/-- Full same-map output: positive finite weighted balls, actual doubling,
the specific pullback metric gauge, the produced DS estimate, and both exact
C1 weak-Poincare dilations. This is the global-C1 test class only. -/
theorem mapBacked_planarDS_and_weakOneTwoC1
    (F : ℂ ≃ₜ ℂ) {w : ℂ → ℝ} {K C : ℝ}
    (hK : 1 ≤ K) (hC : 1 ≤ C) (hw : Continuous w) (hwn : ∀ x, 0 ≤ w x)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hQC : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x ∧
        ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x)
    (hcompare : ∀ᵐ x ∂volume,
      C⁻¹ * w x ≤ signedJacobian F x ∧ signedJacobian F x ≤ C * w x)
    (S : Finset ℂ) (hinverse : LocallyLipschitzOn ((S : Set ℂ)ᶜ) F.symm) :
    PositiveFiniteBalls (weightMeasure w) ∧
    GlobalDoublingWith (weightMeasure w) (mapBackedDoublingConstant K C) ∧
    GaugeComparable (weightMeasure w) (pullbackMetric F) (mapBackedGaugeConstant K C) ∧
    PlanarDS.PlanarDSC1 w (mapBackedDSConstant K C) ∧
    PlanarDS.WeakOneTwoC1 (weightMeasure w)
      (2 * mapBackedDSConstant K C * Real.sqrt (Real.pi * mapBackedDoublingConstant K C)) 2 ∧
    PlanarDS.WeakOneTwoC1 (weightMeasure w)
      (2 * mapBackedDSConstant K C * Real.sqrt (Real.pi * mapBackedDoublingConstant K C) *
        mapBackedDoublingConstant K C) 5 := by
  obtain ⟨hμ, hD, hA⟩ := semmes_weight_sameMap_of_analytic_qc F hLocal
    (le_trans zero_le_one hK) hC hQC hcompare
  have hDS := planarDSC1_of_analytic_qc_finite_inverse_punctures
    F hK hC hw hLocal hQC hcompare S hinverse
  have hL := mapBackedDSConstant_pos hK hC
  exact ⟨hμ, hD, hA, hDS,
    PlanarDS.weakOneTwoC1_of_planarDS hw.measurable (Filter.Eventually.of_forall hwn) hμ hD hL hDS,
    PlanarDS.weakOneTwoC1_five_of_planarDS hw.measurable (Filter.Eventually.of_forall hwn) hμ hD hL hDS⟩

end RepulsiveCoulomb.PaperRoute
