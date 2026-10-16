module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.CompactDensityLogApproximation
public import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalDensityMixture
public import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalInteractionWeakLSC

@[expose] public section

/-! Conditional smooth-Green-to-finite-energy
interaction convexity. The smooth zero-mass positivity premise is explicit
and is discharged in ThermalFiniteEnergyConvexity by the new Green producer. Neither limiting cross
energy nor mixture log integrability is an assumption. -/
noncomputable section
open MeasureTheory Real Metric Set Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb.PaperRoute

/-- Explicit generic smooth Green input, independently constructed by the endpoint wrapper. -/
def ThermalSmoothGreenNonnegative : Prop :=
  ∀ η : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
    (∫ x, η x) = 0 → 0 ≤ thermalDensityLogEnergy η

/-- The conditional bridge consumes actual mass-preserving smooth mollifiers
and their proved real-energy convergence. -/
theorem thermalLogEnergy_nonneg_bounded_compact_of_smoothGreen
    (hGreen : ThermalSmoothGreenNonnegative)
    {η : ℂ → ℝ} {R B : ℝ} (hηm : Measurable η) (hB : 0 ≤ B)
    (hηB : ∀ x, |η x| ≤ B)
    (hηR : ∀ x, x ∉ closedBall (0 : ℂ) R → η x = 0)
    (hmass : (∫ x, η x) = 0) : 0 ≤ thermalDensityLogEnergy η := by
  have hηi := signedDensity_integrable_of_bounded_compact hηm hηB hηR
  have ht : Tendsto (fun n => thermalDensityLogEnergy (compactSignedMollification η n))
      atTop (𝓝 (thermalDensityLogEnergy η)) := by
    simpa only [thermalDensityLogEnergy, thermalDensityLogIntegrand, equilibriumLogKernel] using
      compactSignedMollification_logEnergy_tendsto hηm hηi hB hηB hηR
  apply ge_of_tendsto' ht
  intro n
  apply hGreen (compactSignedMollification η n)
    (compactSignedMollification_contDiff hηi n)
    (compactSignedMollification_hasCompactSupport hηR n)
  rw [compactSignedMollification_integral hηi n, hmass]

/-- At a bounded compact stage, the full interaction identity is integrated
only after every self, mixture and signed-difference energy is integrable.
The algebra does not require a separately expanded cross term. -/
theorem thermalLogEnergy_convex_bounded_compact_of_smoothGreen
    (hGreen : ThermalSmoothGreenNonnegative)
    {ρ σ : ℂ → ℝ} {R B t : ℝ}
    (hρm : Measurable ρ) (hσm : Measurable σ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hσ0 : ∀ x, 0 ≤ σ x)
    (hρi : Integrable ρ) (hσi : Integrable σ)
    (hρmass : (∫ x, ρ x) = 1) (hσmass : (∫ x, σ x) = 1)
    (hB : 0 ≤ B) (hρB : ∀ x, ρ x ≤ B) (hσB : ∀ x, σ x ≤ B)
    (hρR : ∀ x, x ∉ closedBall (0 : ℂ) R → ρ x = 0)
    (hσR : ∀ x, x ∉ closedBall (0 : ℂ) R → σ x = 0)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Integrable (thermalDensityLogIntegrand (thermalDensityMixture t ρ σ)) (volume.prod volume) ∧
    thermalDensityLogEnergy (thermalDensityMixture t ρ σ) ≤
      t * thermalDensityLogEnergy ρ + (1 - t) * thermalDensityLogEnergy σ := by
  have hρabs (x : ℂ) : |ρ x| ≤ B := by rw [abs_of_nonneg (hρ0 x)]; exact hρB x
  have hσabs (x : ℂ) : |σ x| ≤ B := by rw [abs_of_nonneg (hσ0 x)]; exact hσB x
  let η : ℂ → ℝ := fun x => ρ x - σ x
  have hηm : Measurable η := hρm.sub hσm
  have hηB (x : ℂ) : |η x| ≤ 2 * B := by
    calc
      |η x| = ‖ρ x - σ x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖ρ x‖ + ‖σ x‖ := norm_sub_le _ _
      _ ≤ 2 * B := by simpa only [Real.norm_eq_abs, two_mul] using add_le_add (hρabs x) (hσabs x)
  have hηR (x : ℂ) (hx : x ∉ closedBall (0 : ℂ) R) : η x = 0 := by
    simp only [η, hρR x hx, hσR x hx, sub_self]
  have hηmass : (∫ x, η x) = 0 := by rw [show η = fun x => ρ x - σ x from rfl,
    integral_sub hρi hσi, hρmass, hσmass, sub_self]
  have hηE := thermalLogEnergy_nonneg_bounded_compact_of_smoothGreen hGreen
    hηm (mul_nonneg (by norm_num) hB) hηB hηR hηmass
  have hmix0 := thermalDensityMixture_nonneg hρ0 hσ0 ht0 ht1
  have hmixB (x : ℂ) : |thermalDensityMixture t ρ σ x| ≤ B := by
    rw [abs_of_nonneg (hmix0 x)]
    calc
      thermalDensityMixture t ρ σ x ≤ t * B + (1 - t) * B :=
        add_le_add (mul_le_mul_of_nonneg_left (hρB x) ht0)
          (mul_le_mul_of_nonneg_left (hσB x) (sub_nonneg.mpr ht1))
      _ = B := by ring
  have hmixR (x : ℂ) (hx : x ∉ closedBall (0 : ℂ) R) : thermalDensityMixture t ρ σ x = 0 := by
    simp only [thermalDensityMixture, hρR x hx, hσR x hx, mul_zero, add_zero]
  have hρG : Integrable (thermalDensityLogIntegrand ρ) (volume.prod volume) := by
    unfold thermalDensityLogIntegrand equilibriumLogKernel
    exact signedLogEnergy_integrable_of_bounded_compact hρm hB hρabs hρR
  have hσG : Integrable (thermalDensityLogIntegrand σ) (volume.prod volume) := by
    unfold thermalDensityLogIntegrand equilibriumLogKernel
    exact signedLogEnergy_integrable_of_bounded_compact hσm hB hσabs hσR
  have hηG : Integrable (thermalDensityLogIntegrand η) (volume.prod volume) := by
    unfold thermalDensityLogIntegrand equilibriumLogKernel
    exact signedLogEnergy_integrable_of_bounded_compact hηm (mul_nonneg (by norm_num) hB) hηB hηR
  have hmixG : Integrable (thermalDensityLogIntegrand (thermalDensityMixture t ρ σ))
      (volume.prod volume) := by
    unfold thermalDensityLogIntegrand equilibriumLogKernel
    exact signedLogEnergy_integrable_of_bounded_compact
        (thermalDensityMixture_measurable hρm hσm t) hB hmixB hmixR
  refine ⟨hmixG, ?_⟩
  calc
    thermalDensityLogEnergy (thermalDensityMixture t ρ σ) =
        ∫ p, (t * thermalDensityLogIntegrand ρ p + (1 - t) * thermalDensityLogIntegrand σ p -
          t * (1 - t) * thermalDensityLogIntegrand η p) ∂(volume.prod volume) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        dsimp [thermalDensityLogIntegrand, thermalDensityMixture, η]
        ring
    _ = t * thermalDensityLogEnergy ρ + (1 - t) * thermalDensityLogEnergy σ -
        t * (1 - t) * thermalDensityLogEnergy η := by
      have hsum : Integrable (fun p => t * thermalDensityLogIntegrand ρ p +
          (1 - t) * thermalDensityLogIntegrand σ p) (volume.prod volume) :=
        (hρG.const_mul t).add (hσG.const_mul (1 - t))
      rw [integral_sub hsum (hηG.const_mul (t * (1 - t))),
        integral_add (hρG.const_mul t) (hσG.const_mul (1 - t)),
        integral_const_mul, integral_const_mul, integral_const_mul]
      rfl
    _ ≤ _ := sub_le_self _ (mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1)) hηE)

/-- Finite-energy interaction convexity obtained from actual normalized capped
probability densities. Only the two input SELF energies are assumed integrable.
The mixed interaction is proved integrable by weak liminf and a finite cap. -/
theorem thermalDensityLogEnergy_convex_finite_domain_of_smoothGreen
    (hGreen : ThermalSmoothGreenNonnegative)
    {ρ σ : ℂ → ℝ} {t : ℝ}
    (hρm : Measurable ρ) (hσm : Measurable σ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hσ0 : ∀ x, 0 ≤ σ x)
    (hρi : Integrable ρ) (hσi : Integrable σ)
    (hρmass : (∫ x, ρ x) = 1) (hσmass : (∫ x, σ x) = 1)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hσ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * σ x))
    (hρG : Integrable (thermalDensityLogIntegrand ρ) (volume.prod volume))
    (hσG : Integrable (thermalDensityLogIntegrand σ) (volume.prod volume))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Integrable (thermalDensityLogIntegrand (thermalDensityMixture t ρ σ)) (volume.prod volume) ∧
    thermalDensityLogEnergy (thermalDensityMixture t ρ σ) ≤
      t * thermalDensityLogEnergy ρ + (1 - t) * thermalDensityLogEnergy σ := by
  obtain ⟨Nρ, _, hNρ⟩ := thermalDensityCapMass_exists_half_tail hρm hρ0 hρi hρmass
  obtain ⟨Nσ, _, hNσ⟩ := thermalDensityCapMass_exists_half_tail hσm hσ0 hσi hσmass
  let rs : ℕ → ℂ → ℝ := thermalNormalizedDensityCap ρ Nρ
  let ss : ℕ → ℂ → ℝ := thermalNormalizedDensityCap σ Nσ
  let ms : ℕ → ℂ → ℝ := fun n => thermalDensityMixture t (rs n) (ss n)
  let m : ℂ → ℝ := thermalDensityMixture t ρ σ
  have hrm (n : ℕ) : Measurable (rs n) := thermalNormalizedDensityCap_measurable hρm Nρ n
  have hsm (n : ℕ) : Measurable (ss n) := thermalNormalizedDensityCap_measurable hσm Nσ n
  have hr0 (n : ℕ) : ∀ x, 0 ≤ rs n x := thermalNormalizedDensityCap_nonneg hρ0 hNρ n
  have hs0 (n : ℕ) : ∀ x, 0 ≤ ss n x := thermalNormalizedDensityCap_nonneg hσ0 hNσ n
  have hri (n : ℕ) : Integrable (rs n) := thermalNormalizedDensityCap_integrable hρm hρ0 hρi Nρ n
  have hsi (n : ℕ) : Integrable (ss n) := thermalNormalizedDensityCap_integrable hσm hσ0 hσi Nσ n
  have hrmass (n : ℕ) : (∫ x, rs n x) = 1 := thermalNormalizedDensityCap_integral hNρ n
  have hsmass (n : ℕ) : (∫ x, ss n x) = 1 := thermalNormalizedDensityCap_integral hNσ n
  have hr2 (n : ℕ) : Integrable (fun x : ℂ => ‖x‖ ^ 2 * rs n x) :=
    thermalNormalizedDensityCap_secondMoment_integrable hρm hρ0 hρ2 hNρ n
  have hs2 (n : ℕ) : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ss n x) :=
    thermalNormalizedDensityCap_secondMoment_integrable hσm hσ0 hσ2 hNσ n
  have hmsm (n : ℕ) : Measurable (ms n) := thermalDensityMixture_measurable (hrm n) (hsm n) t
  have hms0 (n : ℕ) : ∀ x, 0 ≤ ms n x := thermalDensityMixture_nonneg (hr0 n) (hs0 n) ht0 ht1
  have hmsi (n : ℕ) : Integrable (ms n) := thermalDensityMixture_integrable (hri n) (hsi n) t
  have hmsmass (n : ℕ) : (∫ x, ms n x) = 1 :=
    thermalDensityMixture_integral (hri n) (hsi n) (hrmass n) (hsmass n) t
  have hms2 (n : ℕ) : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ms n x) :=
    thermalDensityMixture_secondMoment_integrable (hr2 n) (hs2 n) t
  have hmm : Measurable m := thermalDensityMixture_measurable hρm hσm t
  have hm0 : ∀ x, 0 ≤ m x := thermalDensityMixture_nonneg hρ0 hσ0 ht0 ht1
  have hmi : Integrable m := thermalDensityMixture_integrable hρi hσi t
  have hmass : (∫ x, m x) = 1 := thermalDensityMixture_integral hρi hσi hρmass hσmass t
  let μs : ℕ → ProbabilityMeasure ℂ := fun n => thermalProbabilityOfDensity (hms0 n) (hmsi n) (hmsmass n)
  let μ : ProbabilityMeasure ℂ := thermalProbabilityOfDensity hm0 hmi hmass
  have hdom (n : ℕ) (x : ℂ) : ms n x ≤ 2 * (ρ x + σ x) := by
    have hr := thermalNormalizedDensityCap_le_two_density hρ0 hNρ n x
    have hs := thermalNormalizedDensityCap_le_two_density hσ0 hNσ n x
    have h1 := mul_le_mul_of_nonneg_right ht1 (hr0 n x)
    have h2 := mul_le_mul_of_nonneg_right (show 1 - t ≤ 1 by linarith) (hs0 n x)
    change t * rs n x + (1 - t) * ss n x ≤ _
    change rs n x ≤ 2 * ρ x at hr
    change ss n x ≤ 2 * σ x at hs
    nlinarith
  have hpoint (x : ℂ) : Tendsto (fun n => ms n x) atTop (𝓝 (m x)) :=
    ((thermalNormalizedDensityCap_tendsto hρm hρ0 hρi hρmass Nρ x).const_mul t).add
      ((thermalNormalizedDensityCap_tendsto hσm hσ0 hσi hσmass Nσ x).const_mul (1 - t))
  have hw : Tendsto μs atTop (𝓝 μ) := thermalProbabilityOfDensity_tendsto_of_dominated
    hmsm hms0 hmsi hmsmass hmm hm0 hmi hmass ((hρi.add hσi).const_mul 2) hdom hpoint
  have hμP2 (n : ℕ) : Integrable (fun x : ℂ => ‖x‖ ^ 2) (μs n) :=
    (equilibriumDensityMeasure_integrable_iff (hmsm n) (hms0 n) _).mpr (hms2 n)
  have hMom (n : ℕ) : (∫ x : ℂ, ‖x‖ ^ 2 ∂(μs n)) ≤
      2 * ((∫ x : ℂ, ‖x‖ ^ 2 * ρ x) + (∫ x : ℂ, ‖x‖ ^ 2 * σ x)) := by
    change (∫ x : ℂ, ‖x‖ ^ 2 ∂equilibriumDensityMeasure (ms n)) ≤ _
    rw [integral_equilibriumDensityMeasure (hmsm n) (hms0 n)]
    simp_rw [mul_comm (ms n _)]
    rw [thermalDensityMixture_secondMoment_integral (hr2 n) (hs2 n) t]
    have hr := thermalNormalizedDensityCap_secondMoment_bound hρm hρ0 hρ2 hNρ n
    have hs := thermalNormalizedDensityCap_secondMoment_bound hσm hσ0 hσ2 hNσ n
    have hMr : 0 ≤ ∫ x : ℂ, ‖x‖ ^ 2 * ρ x := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hρ0 x)
    have hMs : 0 ≤ ∫ x : ℂ, ‖x‖ ^ 2 * σ x := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hσ0 x)
    calc
      _ ≤ t * (2 * ∫ x : ℂ, ‖x‖ ^ 2 * ρ x) + (1 - t) * (2 * ∫ x : ℂ, ‖x‖ ^ 2 * σ x) :=
        add_le_add (mul_le_mul_of_nonneg_left hr ht0)
          (mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr ht1))
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr ht1) hMr, mul_nonneg ht0 hMs]
  have hstage (n : ℕ) : Integrable (thermalDensityLogIntegrand (ms n)) (volume.prod volume) ∧
      thermalDensityLogEnergy (ms n) ≤ t * thermalDensityLogEnergy (rs n) +
        (1 - t) * thermalDensityLogEnergy (ss n) := by
    let R : ℝ := (Nρ + n : ℕ) + (Nσ + n : ℕ)
    have hRρ : ((Nρ + n : ℕ) : ℝ) ≤ R := by
      dsimp [R]
      linarith [Nat.cast_nonneg (Nσ + n) (α := ℝ)]
    have hRσ : ((Nσ + n : ℕ) : ℝ) ≤ R := by
      dsimp [R]
      linarith [Nat.cast_nonneg (Nρ + n) (α := ℝ)]
    apply thermalLogEnergy_convex_bounded_compact_of_smoothGreen hGreen
      (hrm n) (hsm n) (hr0 n) (hs0 n) (hri n) (hsi n) (hrmass n) (hsmass n)
      (R := R) (B := 2 * R) (by dsimp [R]; positivity)
      (fun x => (thermalNormalizedDensityCap_le_index hNρ n x).trans (by linarith))
      (fun x => (thermalNormalizedDensityCap_le_index hNσ n x).trans (by linarith))
      (fun x hx => thermalNormalizedDensityCap_zero_off_ball ρ Nρ n
        (fun hsmall => hx (closedBall_subset_closedBall hRρ hsmall)))
      (fun x hx => thermalNormalizedDensityCap_zero_off_ball σ Nσ n
        (fun hsmall => hx (closedBall_subset_closedBall hRσ hsmall))) ht0 ht1
  have hGs (n : ℕ) : Integrable (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
      ((μs n : Measure ℂ).prod (μs n)) :=
    (thermalDensityLogIntegrand_integrable_iff (hmsm n) (hms0 n)).mp (hstage n).1
  have hcap (n : ℕ) : (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
      ∂((μs n : Measure ℂ).prod (μs n))) ≤
      t * thermalDensityLogEnergy (rs n) + (1 - t) * thermalDensityLogEnergy (ss n) := by
    change (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
      ∂((equilibriumDensityMeasure (ms n)).prod (equilibriumDensityMeasure (ms n)))) ≤ _
    rw [integral_thermalDensityLogIntegrand (hmsm n) (hms0 n) (hstage n).1]
    exact (hstage n).2
  have hc : Tendsto (fun n => t * thermalDensityLogEnergy (rs n) +
        (1 - t) * thermalDensityLogEnergy (ss n)) atTop
      (𝓝 (t * thermalDensityLogEnergy ρ + (1 - t) * thermalDensityLogEnergy σ)) :=
    ((thermalNormalizedDensityCap_logEnergy_tendsto hρm hρ0 hρi hρmass hρG hNρ).const_mul t).add
      ((thermalNormalizedDensityCap_logEnergy_tendsto hσm hσ0 hσi hσmass hσG hNσ).const_mul (1 - t))
  obtain ⟨_, hGμ, hineq⟩ := thermalInteraction_real_limit_bound hw
    (equilibriumDensityMeasure_absolutelyContinuous m)
    (fun n => equilibriumDensityMeasure_absolutelyContinuous (ms n)) hμP2 hMom hGs hc hcap
  have hGm := (thermalDensityLogIntegrand_integrable_iff hmm hm0).mpr hGμ
  refine ⟨hGm, ?_⟩
  change (∫ p : ℂ × ℂ, equilibriumLogKernel (p.1 - p.2)
    ∂((equilibriumDensityMeasure m).prod (equilibriumDensityMeasure m))) ≤ _ at hineq
  rw [integral_thermalDensityLogIntegrand hmm hm0 hGm] at hineq
  exact hineq

end RepulsiveCoulomb.PaperRoute
