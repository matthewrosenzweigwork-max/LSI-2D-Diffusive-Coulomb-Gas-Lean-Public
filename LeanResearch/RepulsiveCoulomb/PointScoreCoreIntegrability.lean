module

public import LeanResearch.RepulsiveCoulomb.PointScoreFiniteMoment

@[expose] public section

/-! Actual score-energy integrability on the original puncture-avoiding core.
Only positive exponents create punctures; coincidences are unrestricted. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem pointScore_continuousAt_off_punctures {m : ℕ} (γ : ℝ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ}
    (hz : z ∉ pointPunctures a y) : ContinuousAt (pointScore γ a y) z := by
  have hj (j : Fin m) : ContinuousAt (fun x : ℂ =>
      a j • ((‖x - y j‖ ^ 2)⁻¹ • (x - y j))) z := by
    by_cases haj : a j = 0
    · simp only [haj, zero_smul]
      exact continuousAt_const
    · have hzy : z ≠ y j := fun he => hz ⟨j, lt_of_le_of_ne (ha j) (Ne.symm haj), he⟩
      have hn : ‖z - y j‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzy))
      exact (((continuous_id.sub continuous_const).norm.pow 2).continuousAt.inv₀ hn).smul
        (continuous_id.sub continuous_const).continuousAt |>.const_smul (a j)
  have hsum (s : Finset (Fin m)) : ContinuousAt (fun x : ℂ =>
      ∑ j ∈ s, a j • ((‖x - y j‖ ^ 2)⁻¹ • (x - y j))) z := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℂ)) z)
    | @insert j s hjs ih =>
      simp only [Finset.sum_insert hjs]
      exact (hj j).add ih
  unfold pointScore pointLogForce
  exact (continuous_id.continuousAt.const_smul γ).sub (hsum Finset.univ)

theorem pointCore_score_energy_continuous {m : ℕ} (γ : ℝ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    Continuous (fun x => ‖pointScore γ a y x‖ ^ 2 * φ x ^ 2) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z ∉ pointPunctures a y
  · exact ((pointScore_continuousAt_off_punctures γ ha y hz).norm.pow 2).mul (φ.continuous.continuousAt.pow 2)
  · have hn : z ∉ tsupport (φ : ℂ → ℝ) := fun ht => hz (φ.tsupport_subset ht)
    have he := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℝ)) z).congr_of_eventuallyEq
    filter_upwards [he] with x hx
    simp [hx]

theorem pointCore_score_energy_integrable {m : ℕ} (γ : ℝ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    Integrable (fun x => ‖pointScore γ a y x‖ ^ 2 * φ x ^ 2) := by
  have hp : HasCompactSupport (fun x => φ x ^ 2) := by
    convert φ.hasCompactSupport.mul_right (f' := (φ : ℂ → ℝ)) using 1
    ext x
    exact pow_two (φ x)
  exact (pointCore_score_energy_continuous γ ha y φ).integrable_of_hasCompactSupport hp.mul_left

theorem pointCore_exists_dyadic_outer_radius {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    ∃ N : ℕ, ∀ x, φ x ^ 2 ≠ 0 → ‖x‖ < dyadicScoreRadius 1 N := by
  obtain ⟨M, hM⟩ := φ.hasCompactSupport.isBounded.exists_norm_le
  obtain ⟨N, _hlo, hN⟩ := exists_nat_pow_near (le_max_right M 1) (by norm_num : (1 : ℝ) < 2)
  refine ⟨N + 1, ?_⟩
  intro x hx
  have hx0 : φ x ≠ 0 := fun h => hx (by simp [h])
  have ht : x ∈ tsupport (φ : ℂ → ℝ) := subset_closure hx0
  simpa only [dyadicScoreRadius, mul_one] using ((hM x ht).trans (le_max_left M 1)).trans_lt hN

end RepulsiveCoulomb
