module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.MapBackedDavidSemmes
public import LeanResearch.RepulsiveCoulomb.PaperRoute.LipschitzInverseGradientTransport
public import LeanResearch.RepulsiveCoulomb.PaperRoute.LipschitzPlanarPoincare

@[expose] public section

/-!
# Same-map full locally-Lipschitz weak 2-admissibility

The supplied map's analytic quasiconformal derivative and Jacobian comparison,
compact-ball Lipschitzness, and actual finite-puncture inverse regularity
produce DS for every globally Lipschitz scalar. Source Rademacher and actual
bounded measurable gradients replace global C1. The target estimate remains
the checked finite-puncture PI on the same buffered image cover.

The exact constants are unchanged: L = mapBackedDSConstant K C,
D = mapBackedDoublingConstant K C, and P₂ = 2 L sqrt(pi D), dilation 2.
Real extension on closed 2B then proves the local Lipschitz test interface
and the full globally locally-Lipschitz class. No p < 2 claim is made.
-/
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology
namespace RepulsiveCoulomb.PaperRoute

/-- Actual inverse composition preserves local Lipschitzness off the given
finite exceptional set for a globally Lipschitz source scalar. -/
theorem locallyLipschitzOn_lipschitz_scalar_comp_symm (F : ℂ ≃ₜ ℂ)
    {f : ℂ → ℝ} {Lf : ℝ≥0} (hf : LipschitzWith Lf f) {S : Set ℂ}
    (hlocal : LocallyLipschitzOn S F.symm) :
    LocallyLipschitzOn S (f ∘ F.symm) := by
  rw [locallyLipschitzOn_iff_restrict]
  exact hf.locallyLipschitz.comp hlocal.restrict

/-- Genuine supplied-map DS for the full globally Lipschitz scalar class. -/
theorem planarDSLipschitz_of_analytic_qc_finite_inverse_punctures
    (F : ℂ ≃ₜ ℂ) {w : ℂ → ℝ} {K C : ℝ}
    (hK : 1 ≤ K) (hC : 1 ≤ C) (hw : Continuous w)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hQC : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x ∧
        ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x)
    (hcompare : ∀ᵐ x ∂volume,
      C⁻¹ * w x ≤ signedJacobian F x ∧ signedJacobian F x ≤ C * w x)
    (S : Finset ℂ) (hinverse : LocallyLipschitzOn ((S : Set ℂ)ᶜ) F.symm) :
    PlanarDS.PlanarDSLipschitz w (mapBackedDSConstant K C) := by
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
  intro f Lf hf c r hr
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
  obtain ⟨hgradient, htransport⟩ := inverse_gradient_transport_of_lipschitz_continuous_weight
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
    (locallyLipschitzOn_lipschitz_scalar_comp_symm F hf hinverse) hgradient
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

/-- Positive finite balls, actual doubling, same-map gauge, DS and both full Lipschitz interfaces. -/
theorem mapBacked_planarDS_and_weakOneTwoLocallyLipschitz
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
    PlanarDS.PlanarDSLipschitz w (mapBackedDSConstant K C) ∧
    PlanarDS.WeakOneTwoLipschitz (weightMeasure w)
      (2 * mapBackedDSConstant K C * Real.sqrt (Real.pi * mapBackedDoublingConstant K C)) 2 ∧
    PlanarDS.WeakOneTwoLocallyLipschitz (weightMeasure w)
      (2 * mapBackedDSConstant K C * Real.sqrt (Real.pi * mapBackedDoublingConstant K C)) 2 := by
  obtain ⟨hμ, hD, hA⟩ := semmes_weight_sameMap_of_analytic_qc F hLocal
    (le_trans zero_le_one hK) hC hQC hcompare
  have hDS := planarDSLipschitz_of_analytic_qc_finite_inverse_punctures
    F hK hC hw hLocal hQC hcompare S hinverse
  have hL := mapBackedDSConstant_pos hK hC
  have hPI := PlanarDS.weakOneTwoLipschitz_of_planarDS hw.measurable
    (Filter.Eventually.of_forall hwn) hμ hD hL hDS
  exact ⟨hμ, hD, hA, hDS, hPI, PlanarDS.weakOneTwoLocallyLipschitz_of_lipschitz hPI⟩

/-- The full paper weak-2 test class from analytic same-map assumptions.
No DS, PI, inverse-gradient, or target-integrability certificate is an input. -/
theorem weakOneTwoLocallyLipschitz_of_analytic_qc_finite_inverse_punctures
    (F : ℂ ≃ₜ ℂ) {w : ℂ → ℝ} {K C : ℝ}
    (hK : 1 ≤ K) (hC : 1 ≤ C) (hw : Continuous w) (hwn : ∀ x, 0 ≤ w x)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hQC : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x ∧
        ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x)
    (hcompare : ∀ᵐ x ∂volume,
      C⁻¹ * w x ≤ signedJacobian F x ∧ signedJacobian F x ≤ C * w x)
    (S : Finset ℂ) (hinverse : LocallyLipschitzOn ((S : Set ℂ)ᶜ) F.symm) :
    PlanarDS.WeakOneTwoLocallyLipschitz (weightMeasure w)
      (2 * mapBackedDSConstant K C * Real.sqrt (Real.pi * mapBackedDoublingConstant K C)) 2 :=
  (mapBacked_planarDS_and_weakOneTwoLocallyLipschitz
    F hK hC hw hwn hLocal hQC hcompare S hinverse).2.2.2.2.2

/-- Strong local interface: only the scalar on closed 2B is required to be
Lipschitz; every mean and energy uses the original scalar and derivative. -/
theorem weakOneTwo_closedDoubleBall_of_analytic_qc_finite_inverse_punctures
    (F : ℂ ≃ₜ ℂ) {w : ℂ → ℝ} {K C : ℝ}
    (hK : 1 ≤ K) (hC : 1 ≤ C) (hw : Continuous w) (hwn : ∀ x, 0 ≤ w x)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hQC : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x ∧
        ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x)
    (hcompare : ∀ᵐ x ∂volume,
      C⁻¹ * w x ≤ signedJacobian F x ∧ signedJacobian F x ≤ C * w x)
    (S : Finset ℂ) (hinverse : LocallyLipschitzOn ((S : Set ℂ)ᶜ) F.symm)
    {f : ℂ → ℝ} {Lf : ℝ≥0} (c : ℂ) {r : ℝ} (hr : 0 < r)
    (hf : LipschitzOnWith Lf f (closedBall c (2 * r))) :
    (⨍ x in ball c r,
      |f x - (⨍ z in ball c r, f z ∂weightMeasure w)| ∂weightMeasure w) ≤
      (2 * mapBackedDSConstant K C * Real.sqrt (Real.pi * mapBackedDoublingConstant K C)) *
        r * Real.sqrt (⨍ z in ball c (2 * r), ‖fderiv ℝ f z‖ ^ 2 ∂weightMeasure w) := by
  have hPI := (mapBacked_planarDS_and_weakOneTwoLocallyLipschitz
    F hK hC hw hwn hLocal hQC hcompare S hinverse).2.2.2.2.1
  exact PlanarDS.weakOneTwo_of_lipschitzOn_closedDoubleBall hPI c hr hf

end RepulsiveCoulomb.PaperRoute
