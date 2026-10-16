module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDensityMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Tactic

@[expose] public section

/-! Explicit normalized capped compact probability
densities, actual moment control, and weak convergence. No energy, convexity,
cross-integrability, or Green conclusion is assumed by this construction. -/
noncomputable section
open MeasureTheory Real Metric Set Filter
open scoped ENNReal Topology Classical
namespace RepulsiveCoulomb.PaperRoute

def thermalDensityCap (ρ : ℂ → ℝ) (j : ℕ) (x : ℂ) : ℝ :=
  (closedBall (0 : ℂ) (j : ℝ)).indicator (fun x => min (ρ x) (j : ℝ)) x

def thermalDensityCapMass (ρ : ℂ → ℝ) (j : ℕ) : ℝ := ∫ x, thermalDensityCap ρ j x

def thermalNormalizedDensityCap (ρ : ℂ → ℝ) (N n : ℕ) (x : ℂ) : ℝ :=
  thermalDensityCap ρ (N + n) x / thermalDensityCapMass ρ (N + n)

theorem thermalDensityCap_measurable {ρ : ℂ → ℝ} (hρm : Measurable ρ) (j : ℕ) :
    Measurable (thermalDensityCap ρ j) :=
  (hρm.min measurable_const).indicator isClosed_closedBall.measurableSet

theorem thermalDensityCap_nonneg {ρ : ℂ → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (j : ℕ) (x : ℂ) :
    0 ≤ thermalDensityCap ρ j x := by
  apply Set.indicator_nonneg
  intro y hy
  exact le_min (hρ0 y) (Nat.cast_nonneg j)

theorem thermalDensityCap_le_density {ρ : ℂ → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (j : ℕ) (x : ℂ) : thermalDensityCap ρ j x ≤ ρ x := by
  by_cases hx : x ∈ closedBall (0 : ℂ) (j : ℝ)
  · simp only [thermalDensityCap, Set.indicator_of_mem hx]
    exact min_le_left _ _
  · simp only [thermalDensityCap, Set.indicator_of_notMem hx]
    exact hρ0 x

theorem thermalDensityCap_le_index (ρ : ℂ → ℝ) (j : ℕ) (x : ℂ) :
    thermalDensityCap ρ j x ≤ j := by
  by_cases hx : x ∈ closedBall (0 : ℂ) (j : ℝ)
  · simp only [thermalDensityCap, Set.indicator_of_mem hx]
    exact min_le_right _ _
  · simp only [thermalDensityCap, Set.indicator_of_notMem hx]
    exact Nat.cast_nonneg j

theorem thermalDensityCap_eq_zero_off_ball (ρ : ℂ → ℝ) (j : ℕ) {x : ℂ}
    (hx : x ∉ closedBall (0 : ℂ) (j : ℝ)) : thermalDensityCap ρ j x = 0 :=
  Set.indicator_of_notMem hx _

theorem thermalDensityCap_integrable {ρ : ℂ → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ) (j : ℕ) :
    Integrable (thermalDensityCap ρ j) := by
  apply hρi.mono' (thermalDensityCap_measurable hρm j).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (thermalDensityCap_nonneg hρ0 j x)]
    exact thermalDensityCap_le_density hρ0 j x

/-- At every point the unnormalized cap is eventually exactly the density. -/
theorem thermalDensityCap_eventually_eq (ρ : ℂ → ℝ) (x : ℂ) :
    ∀ᶠ j : ℕ in atTop, thermalDensityCap ρ j x = ρ x := by
  obtain ⟨J, hJ⟩ := exists_nat_ge (max ‖x‖ (ρ x))
  filter_upwards [eventually_ge_atTop J] with j hj
  have hJj : (J : ℝ) ≤ j := by exact_mod_cast hj
  have hnorm : ‖x‖ ≤ j := (le_max_left _ _).trans (hJ.trans hJj)
  have hrho : ρ x ≤ j := (le_max_right _ _).trans (hJ.trans hJj)
  have hx : x ∈ closedBall (0 : ℂ) (j : ℝ) := by simpa using hnorm
  simp only [thermalDensityCap, Set.indicator_of_mem hx, min_eq_left hrho]

theorem thermalDensityCap_tendsto (ρ : ℂ → ℝ) (x : ℂ) :
    Tendsto (fun j : ℕ => thermalDensityCap ρ j x) atTop (𝓝 (ρ x)) :=
  tendsto_const_nhds.congr' ((thermalDensityCap_eventually_eq ρ x).mono fun _ h => h.symm)

theorem thermalDensityCapMass_tendsto {ρ : ℂ → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ) (hρmass : (∫ x, ρ x) = 1) :
    Tendsto (thermalDensityCapMass ρ) atTop (𝓝 1) := by
  have h := tendsto_integral_of_dominated_convergence ρ
    (fun j => (thermalDensityCap_measurable hρm j).aestronglyMeasurable) hρi
    (fun j => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (thermalDensityCap_nonneg hρ0 j x)]
      exact thermalDensityCap_le_density hρ0 j x)
    (Eventually.of_forall (thermalDensityCap_tendsto ρ))
  change Tendsto (fun j => ∫ x, thermalDensityCap ρ j x) atTop (𝓝 1)
  simpa only [hρmass] using h

/-- A positive normalization tail is derived from actual mass convergence. -/
theorem thermalDensityCapMass_exists_half_tail {ρ : ℂ → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ) (hρmass : (∫ x, ρ x) = 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ j ≥ N, (1 / 2 : ℝ) ≤ thermalDensityCapMass ρ j := by
  have he := (thermalDensityCapMass_tendsto hρm hρ0 hρi hρmass).eventually
    (le_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨J, hJ⟩ := eventually_atTop.mp he
  exact ⟨max 1 J, le_max_left _ _, fun j hj => hJ j ((le_max_right _ _).trans hj)⟩

theorem thermalNormalizedDensityCap_measurable {ρ : ℂ → ℝ} (hρm : Measurable ρ)
    (N n : ℕ) : Measurable (thermalNormalizedDensityCap ρ N n) :=
  (thermalDensityCap_measurable hρm (N + n)).div_const _

theorem thermalNormalizedDensityCap_nonneg {ρ : ℂ → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    {N : ℕ} (hN : ∀ j ≥ N, (1 / 2 : ℝ) ≤ thermalDensityCapMass ρ j)
    (n : ℕ) (x : ℂ) : 0 ≤ thermalNormalizedDensityCap ρ N n x :=
  div_nonneg (thermalDensityCap_nonneg hρ0 _ x)
    (le_trans (by norm_num) (hN _ (Nat.le_add_right N n)))

theorem thermalNormalizedDensityCap_le_two_density {ρ : ℂ → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) {N : ℕ}
    (hN : ∀ j ≥ N, (1 / 2 : ℝ) ≤ thermalDensityCapMass ρ j)
    (n : ℕ) (x : ℂ) : thermalNormalizedDensityCap ρ N n x ≤ 2 * ρ x := by
  have hmass := hN (N + n) (Nat.le_add_right N n)
  have hp : 0 < thermalDensityCapMass ρ (N + n) := by linarith
  apply (div_le_iff₀ hp).mpr
  have hcap := thermalDensityCap_le_density hρ0 (N + n) x
  nlinarith [hρ0 x]

theorem thermalNormalizedDensityCap_le_index {ρ : ℂ → ℝ} {N : ℕ}
    (hN : ∀ j ≥ N, (1 / 2 : ℝ) ≤ thermalDensityCapMass ρ j)
    (n : ℕ) (x : ℂ) : thermalNormalizedDensityCap ρ N n x ≤ 2 * (N + n : ℕ) := by
  have hmass := hN (N + n) (Nat.le_add_right N n)
  have hp : 0 < thermalDensityCapMass ρ (N + n) := by linarith
  apply (div_le_iff₀ hp).mpr
  have hcap := thermalDensityCap_le_index ρ (N + n) x
  nlinarith [Nat.cast_nonneg (N + n) (α := ℝ)]

theorem thermalNormalizedDensityCap_zero_off_ball (ρ : ℂ → ℝ) (N n : ℕ) {x : ℂ}
    (hx : x ∉ closedBall (0 : ℂ) (N + n : ℕ)) :
    thermalNormalizedDensityCap ρ N n x = 0 := by
  simp only [thermalNormalizedDensityCap, thermalDensityCap_eq_zero_off_ball ρ (N + n) hx, zero_div]

theorem thermalNormalizedDensityCap_integrable {ρ : ℂ → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ) (N n : ℕ) :
    Integrable (thermalNormalizedDensityCap ρ N n) :=
  (thermalDensityCap_integrable hρm hρ0 hρi (N + n)).div_const _

theorem thermalNormalizedDensityCap_integral {ρ : ℂ → ℝ} {N : ℕ}
    (hN : ∀ j ≥ N, (1 / 2 : ℝ) ≤ thermalDensityCapMass ρ j) (n : ℕ) :
    (∫ x, thermalNormalizedDensityCap ρ N n x) = 1 := by
  have hm : thermalDensityCapMass ρ (N + n) ≠ 0 := by
    have h := hN (N + n) (Nat.le_add_right N n)
    linarith
  change (∫ x, thermalDensityCap ρ (N + n) x / thermalDensityCapMass ρ (N + n)) = 1
  rw [integral_div]
  exact div_self hm

theorem thermalNormalizedDensityCap_tendsto {ρ : ℂ → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ) (hρmass : (∫ x, ρ x) = 1)
    (N : ℕ) (x : ℂ) :
    Tendsto (fun n => thermalNormalizedDensityCap ρ N n x) atTop (𝓝 (ρ x)) := by
  have hshift : Tendsto (fun n : ℕ => N + n) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat N
  simpa only [thermalNormalizedDensityCap, div_one, Function.comp_def, Pi.div_def] using
    ((thermalDensityCap_tendsto ρ x).comp hshift).div
      ((thermalDensityCapMass_tendsto hρm hρ0 hρi hρmass).comp hshift) (by norm_num : (1 : ℝ) ≠ 0)

theorem thermalNormalizedDensityCap_secondMoment_integrable {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x)) {N : ℕ}
    (hN : ∀ j ≥ N, (1 / 2 : ℝ) ≤ thermalDensityCapMass ρ j) (n : ℕ) :
    Integrable (fun x : ℂ => ‖x‖ ^ 2 * thermalNormalizedDensityCap ρ N n x) := by
  apply (hρ2.const_mul 2).mono'
    ((continuous_norm.pow 2).measurable.mul
      (thermalNormalizedDensityCap_measurable hρm N n)).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    change ‖‖x‖ ^ 2 * thermalNormalizedDensityCap ρ N n x‖ ≤ 2 * (‖x‖ ^ 2 * ρ x)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (thermalNormalizedDensityCap_nonneg hρ0 hN n x))]
    have h := mul_le_mul_of_nonneg_left
      (thermalNormalizedDensityCap_le_two_density hρ0 hN n x) (sq_nonneg ‖x‖)
    nlinarith

theorem thermalNormalizedDensityCap_secondMoment_bound {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x)) {N : ℕ}
    (hN : ∀ j ≥ N, (1 / 2 : ℝ) ≤ thermalDensityCapMass ρ j) (n : ℕ) :
    (∫ x : ℂ, ‖x‖ ^ 2 * thermalNormalizedDensityCap ρ N n x) ≤
      2 * ∫ x : ℂ, ‖x‖ ^ 2 * ρ x := by
  rw [← integral_const_mul]
  apply integral_mono (thermalNormalizedDensityCap_secondMoment_integrable hρm hρ0 hρ2 hN n)
    (hρ2.const_mul 2)
  intro x
  have h := mul_le_mul_of_nonneg_left
    (thermalNormalizedDensityCap_le_two_density hρ0 hN n x) (sq_nonneg ‖x‖)
  nlinarith

/-- The literal probability law of the normalized capped density. -/
def thermalCappedProbability {ρ : ℂ → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ) (N : ℕ)
    (hN : ∀ j ≥ N, (1 / 2 : ℝ) ≤ thermalDensityCapMass ρ j) (n : ℕ) :
    ProbabilityMeasure ℂ :=
  ⟨equilibriumDensityMeasure (thermalNormalizedDensityCap ρ N n),
    equilibriumDensityMeasure_probability
      (thermalNormalizedDensityCap_nonneg hρ0 hN n)
      (thermalNormalizedDensityCap_integrable hρm hρ0 hρi N n)
      (thermalNormalizedDensityCap_integral hN n)⟩

theorem thermalCappedProbability_absolutelyContinuous {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ) (N : ℕ)
    (hN : ∀ j ≥ N, (1 / 2 : ℝ) ≤ thermalDensityCapMass ρ j) (n : ℕ) :
    ((thermalCappedProbability hρm hρ0 hρi N hN n) : Measure ℂ) ≪ volume :=
  equilibriumDensityMeasure_absolutelyContinuous _

theorem thermalCappedProbability_secondMoment {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x)) (N : ℕ)
    (hN : ∀ j ≥ N, (1 / 2 : ℝ) ≤ thermalDensityCapMass ρ j) (n : ℕ) :
    Integrable (fun x : ℂ => ‖x‖ ^ 2) (thermalCappedProbability hρm hρ0 hρi N hN n) ∧
    (∫ x : ℂ, ‖x‖ ^ 2 ∂(thermalCappedProbability hρm hρ0 hρi N hN n)) ≤
      2 * ∫ x : ℂ, ‖x‖ ^ 2 * ρ x := by
  constructor
  · exact (equilibriumDensityMeasure_integrable_iff
      (thermalNormalizedDensityCap_measurable hρm N n)
      (thermalNormalizedDensityCap_nonneg hρ0 hN n) _).mpr
        (thermalNormalizedDensityCap_secondMoment_integrable hρm hρ0 hρ2 hN n)
  · change (∫ x : ℂ, ‖x‖ ^ 2 ∂equilibriumDensityMeasure (thermalNormalizedDensityCap ρ N n)) ≤ _
    rw [integral_equilibriumDensityMeasure
      (thermalNormalizedDensityCap_measurable hρm N n)
      (thermalNormalizedDensityCap_nonneg hρ0 hN n)]
    simpa only [mul_comm] using thermalNormalizedDensityCap_secondMoment_bound hρm hρ0 hρ2 hN n

theorem thermalCappedProbability_weak_tendsto {ρ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρmass : (∫ x, ρ x) = 1) (N : ℕ)
    (hN : ∀ j ≥ N, (1 / 2 : ℝ) ≤ thermalDensityCapMass ρ j) :
    Tendsto (thermalCappedProbability hρm hρ0 hρi N hN) atTop
      (𝓝 (⟨equilibriumDensityMeasure ρ,
        equilibriumDensityMeasure_probability hρ0 hρi hρmass⟩ : ProbabilityMeasure ℂ)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have ht := tendsto_integral_of_dominated_convergence (fun x => (2 * ‖f‖) * ρ x)
    (fun n => ((thermalNormalizedDensityCap_measurable hρm N n).mul
      f.continuous.measurable).aestronglyMeasurable)
    (hρi.const_mul (2 * ‖f‖))
    (fun n => Eventually.of_forall fun x => by
      change ‖thermalNormalizedDensityCap ρ N n x * f x‖ ≤ (2 * ‖f‖) * ρ x
      rw [norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (thermalNormalizedDensityCap_nonneg hρ0 hN n x)]
      calc
        thermalNormalizedDensityCap ρ N n x * ‖f x‖ ≤ (2 * ρ x) * ‖f‖ :=
          mul_le_mul (thermalNormalizedDensityCap_le_two_density hρ0 hN n x)
            (f.norm_coe_le_norm x) (norm_nonneg _) (mul_nonneg (by norm_num) (hρ0 x))
        _ = _ := by ring)
    (Eventually.of_forall fun x =>
      (thermalNormalizedDensityCap_tendsto hρm hρ0 hρi hρmass N x).mul_const (f x))
  have hn (n : ℕ) : (∫ x, f x ∂(thermalCappedProbability hρm hρ0 hρi N hN n)) =
      ∫ x, thermalNormalizedDensityCap ρ N n x * f x :=
    integral_equilibriumDensityMeasure (thermalNormalizedDensityCap_measurable hρm N n)
      (thermalNormalizedDensityCap_nonneg hρ0 hN n) f
  have hlim : (∫ x, f x ∂(⟨equilibriumDensityMeasure ρ,
        equilibriumDensityMeasure_probability hρ0 hρi hρmass⟩ : ProbabilityMeasure ℂ)) =
      ∫ x, ρ x * f x := integral_equilibriumDensityMeasure hρm hρ0 f
  change Tendsto (fun n => ∫ x, f x ∂equilibriumDensityMeasure (thermalNormalizedDensityCap ρ N n))
    atTop (𝓝 (∫ x, f x ∂equilibriumDensityMeasure ρ))
  simp_rw [integral_equilibriumDensityMeasure
    (thermalNormalizedDensityCap_measurable hρm N _)
    (thermalNormalizedDensityCap_nonneg hρ0 hN _), integral_equilibriumDensityMeasure hρm hρ0]
  simpa only [Pi.mul_apply] using ht


end RepulsiveCoulomb.PaperRoute
