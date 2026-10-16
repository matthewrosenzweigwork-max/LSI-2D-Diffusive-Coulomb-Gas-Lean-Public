import LeanResearch.RepulsiveCoulomb.EquilibriumBranchExtendedCoercivity
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchGaussianObjective
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Instances.EReal.Lemmas

/-! Literal canonical minimizing sequences and their genuine moment compactness.
The sole objective use is the finite Gaussian competitor and exact algebraic
correspondence. No old objective LSC, sublevel compactness, or minimizer producer
is used. -/
noncomputable section
open MeasureTheory Real Metric Set Filter
open scoped ENNReal Topology Classical
namespace RepulsiveCoulomb.PaperRoute

theorem thermalCanonicalFreeEnergy_lower_bound {β : ℝ} (hβ : 0 < β)
    (μ : ProbabilityMeasure ℂ) :
    ((-(2 - Real.log (β / (8 * Real.pi)) / β) : ℝ) : EReal) ≤
      equilibriumCanonicalFreeEnergy β μ := by
  have h := equilibriumCanonicalFreeEnergy_quarter_coercive_extended hβ μ
  have h0 := EReal.sub_le_sub (EReal.coe_ennreal_nonneg
    (ENNReal.ofReal (1 / 4 : ℝ) * (∫⁻ x : ℂ, ENNReal.ofReal (‖x‖ ^ 2) ∂μ)))
    (le_refl ((2 - Real.log (β / (8 * Real.pi)) / β : ℝ) : EReal))
  have h0' : ((-(2 - Real.log (β / (8 * Real.pi)) / β) : ℝ) : EReal) ≤
      ((ENNReal.ofReal (1 / 4 : ℝ) * (∫⁻ x : ℂ, ENNReal.ofReal (‖x‖ ^ 2) ∂μ) : ℝ≥0∞) : EReal) -
        ((2 - Real.log (β / (8 * Real.pi)) / β : ℝ) : EReal) := by
    simpa only [zero_sub, ← EReal.coe_neg] using h0
  exact h0'.trans h

theorem thermalCanonicalFreeEnergy_ne_bot {β : ℝ} (hβ : 0 < β)
    (μ : ProbabilityMeasure ℂ) : equilibriumCanonicalFreeEnergy β μ ≠ ⊥ :=
  ne_of_gt ((EReal.bot_lt_coe _).trans_le (thermalCanonicalFreeEnergy_lower_bound hβ μ))

theorem thermalCanonicalFreeEnergy_ne_top_domain {β : ℝ} {μ : ProbabilityMeasure ℂ}
    (hF : equilibriumCanonicalFreeEnergy β μ ≠ ⊤) :
    (μ : Measure ℂ) ≪ volume ∧ Integrable (fun x : ℂ => ‖x‖ ^ 2) μ := by
  by_contra h
  exact hF (by rw [equilibriumCanonicalFreeEnergy, ite_eq_right h])

theorem thermalCanonicalFreeEnergy_sublevel_secondMoment {β c : ℝ} (hβ : 0 < β)
    {μ : ProbabilityMeasure ℂ} (hF : equilibriumCanonicalFreeEnergy β μ ≤ (c : EReal)) :
    Integrable (fun x : ℂ => ‖x‖ ^ 2) μ ∧
      (∫ x : ℂ, ‖x‖ ^ 2 ∂μ) ≤ 4 * (c + (2 - Real.log (β / (8 * Real.pi)) / β)) := by
  have hf := ne_top_of_le_ne_top (EReal.coe_ne_top c) hF
  have hi := (thermalCanonicalFreeEnergy_ne_top_domain hf).2
  refine ⟨hi, ?_⟩
  have hm0 : 0 ≤ ∫ x : ℂ, ‖x‖ ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg ‖x‖)
  have h := (equilibriumCanonicalFreeEnergy_quarter_coercive_extended hβ μ).trans hF
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun x : ℂ => sq_nonneg ‖x‖),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4),
    EReal.coe_ennreal_ofReal, max_eq_left (mul_nonneg (by norm_num) hm0),
    ← EReal.coe_sub, EReal.coe_le_coe_iff] at h
  linarith

theorem thermalCanonicalFreeEnergy_gaussian_finite {β : ℝ} (hβ : 0 < β) :
    ∃ (γ : ProbabilityMeasure ℂ) (c : ℝ), equilibriumCanonicalFreeEnergy β γ = (c : EReal) := by
  have ha : 0 < β / 4 := by positivity
  let γ := equilibriumGaussianProbability (β / 4) ha
  have hi : Integrable (fun x : ℂ => ‖x‖ ^ 2) γ :=
    equilibriumGaussianMeasure_secondMoment_integrable ha
  have hf : equilibriumNonnegativeObjective β (γ : Measure ℂ) ≠ ∞ :=
    equilibriumGaussianObjective_ne_top hβ
  refine ⟨γ, (equilibriumNonnegativeObjective β γ).toReal - 1 +
    Real.log ((β / 4) / Real.pi) / β, ?_⟩
  rw [equilibriumFreeEnergy_correspondence hβ hi,
    equilibriumNonnegativeFreeEnergy_eq_objective,
    ← EReal.coe_ennreal_toReal hf, ← EReal.coe_sub, ← EReal.coe_add]

/-- A real-valued canonical minimizing sequence, selected from literal finite
canonical values below an actual Gaussian competitor. The universal comparison
includes singular and infinite-energy competitors. -/
theorem thermalCanonicalFreeEnergy_exists_minimizingSequence {β : ℝ} (hβ : 0 < β) :
    ∃ e c M : ℝ, ∃ μs : ℕ → ProbabilityMeasure ℂ,
      (∀ n, equilibriumCanonicalFreeEnergy β (μs n) ≤ (c : EReal)) ∧
      (∀ n, Integrable (fun x : ℂ => ‖x‖ ^ 2) (μs n)) ∧
      (∀ n, (∫ x : ℂ, ‖x‖ ^ 2 ∂(μs n)) ≤ M) ∧
      Tendsto (fun n => equilibriumCanonicalFreeEnergy β (μs n)) atTop (𝓝 (e : EReal)) ∧
      (∀ ν : ProbabilityMeasure ℂ, (e : EReal) ≤ equilibriumCanonicalFreeEnergy β ν) := by
  obtain ⟨γ, c, hc⟩ := thermalCanonicalFreeEnergy_gaussian_finite hβ
  let T : Set ℝ := {r | ∃ μ : ProbabilityMeasure ℂ,
    equilibriumCanonicalFreeEnergy β μ = (r : EReal) ∧ r ≤ c}
  have hcmem : c ∈ T := ⟨γ, hc, le_rfl⟩
  have hT : T.Nonempty := ⟨c, hcmem⟩
  have hlow : BddBelow T := by
    refine ⟨-(2 - Real.log (β / (8 * Real.pi)) / β), ?_⟩
    intro r hr
    obtain ⟨μ, hμ, _⟩ := hr
    have h := thermalCanonicalFreeEnergy_lower_bound hβ μ
    rw [hμ, EReal.coe_le_coe_iff] at h
    exact h
  obtain ⟨r, _, hr, hrt⟩ := exists_seq_tendsto_sInf hT hlow
  choose μs hμs hcap using hrt
  have hF (n : ℕ) : equilibriumCanonicalFreeEnergy β (μs n) ≤ (c : EReal) := by
    rw [hμs n]
    exact EReal.coe_le_coe (hcap n)
  refine ⟨sInf T, c, 4 * (c + (2 - Real.log (β / (8 * Real.pi)) / β)), μs,
    hF, fun n => (thermalCanonicalFreeEnergy_sublevel_secondMoment hβ (hF n)).1,
    fun n => (thermalCanonicalFreeEnergy_sublevel_secondMoment hβ (hF n)).2, ?_, ?_⟩
  · simpa only [hμs, Function.comp_def] using continuous_coe_real_ereal.continuousAt.tendsto.comp hr
  · intro ν
    by_cases hν : equilibriumCanonicalFreeEnergy β ν ≤ (c : EReal)
    · have hn := ne_top_of_le_ne_top (EReal.coe_ne_top c) hν
      have he := EReal.coe_toReal hn (thermalCanonicalFreeEnergy_ne_bot hβ ν)
      have hm : (equilibriumCanonicalFreeEnergy β ν).toReal ∈ T := by
        refine ⟨ν, he.symm, ?_⟩
        rw [← he, EReal.coe_le_coe_iff] at hν
        exact hν
      rw [← he]
      exact EReal.coe_le_coe (csInf_le hlow hm)
    · exact (EReal.coe_le_coe (csInf_le hlow hcmem)).trans (le_of_lt (lt_of_not_ge hν))

/-- Markov tightness from actual integrable second moments. -/
theorem thermal_uniformSecondMoment_isTight {S : Set (ProbabilityMeasure ℂ)} {M : ℝ}
    (hP2 : ∀ μ ∈ S, Integrable (fun x : ℂ => ‖x‖ ^ 2) μ)
    (hM : ∀ μ ∈ S, (∫ x : ℂ, ‖x‖ ^ 2 ∂μ) ≤ M) :
    IsTightMeasureSet ((fun μ : ProbabilityMeasure ℂ => (μ : Measure ℂ)) '' S) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨n, hn, hnε⟩ := ENNReal.exists_nat_pos_inv_mul_lt
    (ENNReal.ofReal_ne_top (r := M)) hε.ne'
  refine ⟨closedBall (0 : ℂ) (Real.sqrt (n : ℝ)), isCompact_closedBall _ _, ?_⟩
  intro ξ hξ
  obtain ⟨μ, hμ, rfl⟩ := hξ
  have hmoment : (∫⁻ x : ℂ, ENNReal.ofReal (‖x‖ ^ 2) ∂μ) ≤ ENNReal.ofReal M := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hP2 μ hμ)
      (Eventually.of_forall fun x : ℂ => sq_nonneg ‖x‖)]
    exact ENNReal.ofReal_le_ofReal (hM μ hμ)
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  have hnT : (n : ℝ≥0∞) ≠ ∞ := by finiteness
  have hset : (closedBall (0 : ℂ) (Real.sqrt (n : ℝ)))ᶜ ⊆
      {x : ℂ | (n : ℝ≥0∞) ≤ ENNReal.ofReal (‖x‖ ^ 2)} := by
    intro x hx
    have hx' : Real.sqrt (n : ℝ) < ‖x‖ := by
      simpa only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hx
    have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hs0 := Real.sqrt_nonneg (n : ℝ)
    have hr : (n : ℝ) ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    change (n : ℝ≥0∞) ≤ ENNReal.ofReal (‖x‖ ^ 2)
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hr
  calc
    (μ : Measure ℂ) (closedBall (0 : ℂ) (Real.sqrt (n : ℝ)))ᶜ ≤
        (μ : Measure ℂ) {x : ℂ | (n : ℝ≥0∞) ≤ ENNReal.ofReal (‖x‖ ^ 2)} := measure_mono hset
    _ ≤ (∫⁻ x : ℂ, ENNReal.ofReal (‖x‖ ^ 2) ∂μ) / n :=
      meas_ge_le_lintegral_div (by fun_prop) hn0 hnT
    _ = (n : ℝ≥0∞)⁻¹ * (∫⁻ x : ℂ, ENNReal.ofReal (‖x‖ ^ 2) ∂μ) := by
      rw [ENNReal.div_eq_inv_mul]
    _ ≤ (n : ℝ≥0∞)⁻¹ * ENNReal.ofReal M := mul_le_mul_right hmoment _
    _ ≤ ε := hnε.le

/-- Weak extraction through genuine Markov tightness and Prokhorov. -/
theorem thermal_uniformSecondMoment_exists_weak_subsequence
    {μs : ℕ → ProbabilityMeasure ℂ} {M : ℝ}
    (hP2 : ∀ n, Integrable (fun x : ℂ => ‖x‖ ^ 2) (μs n))
    (hM : ∀ n, (∫ x : ℂ, ‖x‖ ^ 2 ∂(μs n)) ≤ M) :
    ∃ (μ : ProbabilityMeasure ℂ) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) := by
  have ht := thermal_uniformSecondMoment_isTight (S := Set.range μs)
    (fun μ hμ => by obtain ⟨n, rfl⟩ := hμ; exact hP2 n)
    (fun μ hμ => by obtain ⟨n, rfl⟩ := hμ; exact hM n)
  have hc := isCompact_closure_of_isTightMeasureSet ht
  obtain ⟨μ, _, φ, hφ, hw⟩ := hc.tendsto_subseq
    (fun n => subset_closure (Set.mem_range_self n))
  exact ⟨μ, φ, hφ, hw⟩

end RepulsiveCoulomb.PaperRoute
