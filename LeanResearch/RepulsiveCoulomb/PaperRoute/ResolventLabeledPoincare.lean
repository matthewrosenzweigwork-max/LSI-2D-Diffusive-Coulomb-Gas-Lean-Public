module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.AnalyticLabeledPoincare
public import LeanResearch.RepulsiveCoulomb.PaperRoute.RelativeLabeledPoincare
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! Additive original-paper adapter. Compact resolvent, its actual graph inverse,
and the associated-operator constants kernel feed the fixed-N gap. No old
compact-embedding coercivity endpoint is used as a proof premise. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace ProbabilityTheory
open scoped Topology
namespace RepulsiveCoulomb.PaperRoute

/-- The compact Fredholm gap away from the fixed space, proved by the actual
compact image of normalized approximate fixed vectors. -/
theorem compact_resolvent_mean_zero_coercivity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (R : H →L[ℝ] H) (hR : IsCompactOperator R) (M : H →L[ℝ] ℝ)
    (hker : ∀ f : H, M f = 0 → R f = f → f = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : H, M f = 0 → ‖f‖ ≤ C * ‖f - R f‖ := by
  classical
  by_contra hn
  push Not at hn
  choose f hm hbad using fun n : ℕ => hn ((n : ℝ) + 1) (by positivity)
  have hfne (n : ℕ) : f n ≠ 0 := norm_pos_iff.mp
    (lt_of_le_of_lt (mul_nonneg (by positivity) (norm_nonneg _)) (hbad n))
  let v : ℕ → H := fun n => (‖f n‖⁻¹ : ℝ) • f n
  have hvnorm (n : ℕ) : ‖v n‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) (hfne n)
  have hvmean (n : ℕ) : M (v n) = 0 := by simp only [v, map_smul, hm, smul_zero]
  have hvres (n : ℕ) : ‖v n - R (v n)‖ ≤ 1 / ((n : ℝ) + 1) := by
    have hp : 0 < ‖f n‖ := norm_pos_iff.mpr (hfne n)
    have hh : ‖f n - R (f n)‖ / ‖f n‖ ≤ 1 / ((n : ℝ) + 1) := by
      apply (div_le_div_iff₀ hp (by positivity)).mpr
      nlinarith only [hbad n]
    simpa only [v, map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg (f n))), div_eq_inv_mul] using hh
  have hres : Tendsto (fun n => v n - R (v n)) atTop (𝓝 0) :=
    squeeze_zero_norm hvres tendsto_one_div_add_atTop_nhds_zero_nat
  have hc := hR.isCompact_closure_image_closedBall (1 : ℝ)
  obtain ⟨g, _hg, σ, hσ, hRg⟩ := hc.tendsto_subseq
    (fun n => subset_closure ⟨v n, by simpa only [Metric.mem_closedBall,
      dist_zero_right, hvnorm] using (le_refl (1 : ℝ)), rfl⟩)
  have hvg : Tendsto (v ∘ σ) atTop (𝓝 g) := by
    have h := (hres.comp hσ.tendsto_atTop).add hRg
    change Tendsto (fun n => v (σ n) - R (v (σ n)) + R (v (σ n))) atTop (𝓝 (0 + g)) at h
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using h
  have hfix : R g = g := tendsto_nhds_unique ((R.continuous.tendsto g).comp hvg) hRg
  have hmean : M g = 0 := by
    have h := (M.continuous.tendsto g).comp hvg
    have hz : Tendsto (fun n => M (v (σ n))) atTop (𝓝 (0 : ℝ)) := by
      simpa only [hvmean] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique h hz
  have hnorm : ‖g‖ = 1 := by
    have h : Tendsto (fun n => ‖v (σ n)‖) atTop (𝓝 (1 : ℝ)) := by
      simpa only [hvnorm] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    exact tendsto_nhds_unique hvg.norm h
  rw [hker g hmean hfix, norm_zero] at hnorm
  norm_num at hnorm

/-- A fixed point of the genuine resolvent is an associated-operator zero mode. -/
theorem paper_resolvent_mean_zero_fixed {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (f : Lp ℝ 2 (coulombMeasure N β))
    (hm : poleBranchRealMean N hβ f = 0) (hf : coulombFormResolvent N hβ f = f) : f = 0 := by
  let := coulombMeasure_isProbability (N := N) hβ
  have hp : (f, (0 : Lp ℝ 2 (coulombMeasure N β))) ∈ coulombAssociatedGraph N hβ :=
    (coulombAssociatedGraph_inverse hβ f 0).mpr (by simpa only [add_zero] using hf)
  rw [← coulombAssociatedOperator_graph] at hp
  obtain ⟨u, hu, hAu⟩ := (LinearPMap.mem_graph_iff _).mp hp
  obtain ⟨a, ha⟩ := coulombAssociatedOperator_zero_constant N hβ u hAu
  have hfa : f =ᵐ[coulombMeasure N β] fun _ => a := by simpa only [hu] using ha
  have hmean : poleBranchRealMean N hβ f = a := by
    rw [poleBranchRealMean_eq_integral, integral_congr_ae hfa]
    simp
  have ha0 : a = 0 := hmean.symm.trans hm
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hfa] with z hz
  change f z = 0
  exact hz.trans ha0

/-- Actual variational resolvent approximation, controlled by physical energy. -/
theorem paper_resolvent_form_residual {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain N hβ) :
    ‖coulombFormValueL N hβ u - coulombFormResolvent N hβ (coulombFormValueL N hβ u)‖ ≤
      ‖coulombFormGradientL N hβ u‖ := by
  let V := coulombFormValueL N hβ
  let w : CoulombFormDomain N hβ := u - V.adjoint (V u)
  have hw : ‖w‖ ^ 2 = coulombFormEnergyPair N hβ u w := by
    calc
      _ = inner ℝ w w := (real_inner_self_eq_norm_sq w).symm
      _ = inner ℝ u w - inner ℝ (V.adjoint (V u)) w := by
        change inner ℝ (u - V.adjoint (V u)) w = _
        rw [inner_sub_left]
      _ = coulombFormEnergyPair N hβ u w := by
        rw [ContinuousLinearMap.adjoint_inner_left, coulombForm_inner_eq]
        change (inner ℝ (V u) (V w) + coulombFormEnergyPair N hβ u w) -
          inner ℝ (V u) (V w) = _
        ring
  have hle : ‖w‖ ^ 2 ≤ ‖coulombFormGradientL N hβ u‖ * ‖w‖ := by
    rw [hw, coulombFormEnergyPair]
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (coulombFormGradient_norm_le N hβ w) (norm_nonneg _))
  have hn : ‖w‖ ≤ ‖coulombFormGradientL N hβ u‖ := by
    by_cases hz : w = 0
    · simp only [hz, norm_zero, norm_nonneg]
    · have hp : 0 < ‖w‖ := norm_pos_iff.mpr hz
      nlinarith only [hle, hp]
  have hv : V w = coulombFormValueL N hβ u -
      coulombFormResolvent N hβ (coulombFormValueL N hβ u) := by
    change V (u - V.adjoint (V u)) = V u - V (V.adjoint (V u))
    rw [map_sub]
  rw [← hv]
  exact (coulombFormValueL_norm_le N hβ w).trans hn

/-- Fixed-N PI produced through compact R=(I+A)^(-1), its actual inverse graph,
and its constants kernel. It does not invoke the old direct-coercivity PI. -/
theorem paper_fixed_particle_poincare_via_resolvent (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : CoulombFormDomain (N + 2) hβ,
      variance (coulombFormValueL (N + 2) hβ u : CoulombConfig (N + 2) → ℝ)
        (coulombMeasure (N + 2) β) ≤ C * coulombFormEnergy (N + 2) hβ u := by
  obtain ⟨C, hC, hgap⟩ := compact_resolvent_mean_zero_coercivity
    (coulombFormResolvent (N + 2) hβ) (coulombFormResolvent_isCompactOperator (N + 2) hβ)
    (poleBranchRealMean (N + 2) hβ) (paper_resolvent_mean_zero_fixed hβ)
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro u
  let v := coulombFormCenter N hβ u
  have h := hgap (coulombFormValueL (N + 2) hβ v) (coulombFormCenter_mean N hβ u)
  have hr := paper_resolvent_form_residual hβ v
  rw [coulombFormCenter_gradient] at hr
  have hb := h.trans (mul_le_mul_of_nonneg_left hr hC.le)
  rw [← coulombFormCenter_value_norm_sq N hβ u]
  have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC.le (norm_nonneg _))).mpr hb
  simpa only [mul_pow, coulombFormEnergy] using hh

/-- The same optimal Rayleigh supremum is bounded using the resolvent-produced gap. -/
theorem paper_optimal_poincare_via_resolvent (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (u : CoulombFormDomain (N + 2) hβ) :
    variance (coulombFormValueL (N + 2) hβ u : CoulombConfig (N + 2) → ℝ)
      (coulombMeasure (N + 2) β) ≤
      coulombOptimalPoincare (N + 2) hβ * coulombFormEnergy (N + 2) hβ u := by
  obtain ⟨C, hC, hPI⟩ := paper_fixed_particle_poincare_via_resolvent N hβ
  have hbd : BddAbove (coulombPoincareQuotients (N + 2) hβ) :=
    ⟨C, coulombPoincareQuotients_le hβ hC.le hPI⟩
  by_cases hE : 0 < coulombFormEnergy (N + 2) hβ u
  · exact (div_le_iff₀ hE).mp
      (le_csSup hbd (Or.inr ⟨⟨u, hE⟩, rfl⟩) :
        variance (coulombFormValueL (N + 2) hβ u : CoulombConfig (N + 2) → ℝ)
          (coulombMeasure (N + 2) β) / coulombFormEnergy (N + 2) hβ u ≤ _)
  · have hz : coulombFormEnergy (N + 2) hβ u = 0 := by
      have hn := coulombFormEnergy_nonneg (N + 2) hβ u
      linarith
    simpa only [hz, mul_zero] using hPI u

theorem paper_symmetric_poincare_via_resolvent {N : ℕ} (hN : 2 ≤ N) {β : ℝ}
    (hβ : 0 < β) (u : CoulombFormDomain N hβ)
    (hsym : ∀ σ : Equiv.Perm (Fin N),
      coulombValuePermuteL N hβ σ (coulombFormValueL N hβ u) = coulombFormValueL N hβ u) :
    variance (coulombFormValueL N hβ u : CoulombConfig N → ℝ) (coulombMeasure N β) ≤
      poleBranchSymmetricPoincareConstant hβ * coulombFormEnergy N hβ u := by
  by_cases hsmall : (N : ℝ) ≤ β / 2
  · have hmem := (poleBranchExceptionalParticleCounts_mem hβ.le N).mpr ⟨hN, hsmall⟩
    have hcp := poleBranchSymmetricPoincareConstant_optimal_le hβ N hmem
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 2 := ⟨N - 2, by omega⟩
    exact (paper_optimal_poincare_via_resolvent n hβ u).trans
      (mul_le_mul_of_nonneg_right hcp (coulombFormEnergy_nonneg (n + 2) hβ u))
  · have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have ha2 : β / (N : ℝ) ≤ 2 := (div_le_iff₀ hn).mpr (by linarith)
    exact (paper_symmetric_poincare_small_exponent hβ ha2 u hsym).trans
      (mul_le_mul_of_nonneg_right (poleBranchSymmetricPoincareConstant_one_div_le hβ)
        (coulombFormEnergy_nonneg N hβ u))

theorem paper_symmetrized_poincare_via_resolvent {N : ℕ} (hN : 2 ≤ N) {β : ℝ}
    (hβ : 0 < β) (u : CoulombFormDomain N hβ) :
    variance (coulombSymmetrizer N hβ (coulombFormValueL N hβ u) : CoulombConfig N → ℝ)
      (coulombMeasure N β) ≤
      poleBranchSymmetricPoincareConstant hβ * coulombFormEnergy N hβ u := by
  have hsym : ∀ σ : Equiv.Perm (Fin N),
      coulombValuePermuteL N hβ σ
        (coulombFormValueL N hβ (coulombFormSymmetrizer N hβ u)) =
        coulombFormValueL N hβ (coulombFormSymmetrizer N hβ u) := by
    intro σ
    rw [coulombFormSymmetrizer_value]
    exact coulombSymmetrizer_invariant N hβ σ _
  have h := paper_symmetric_poincare_via_resolvent hN hβ (coulombFormSymmetrizer N hβ u) hsym
  rw [coulombFormSymmetrizer_value] at h
  exact h.trans (mul_le_mul_of_nonneg_left (coulombFormSymmetrizer_energy_le N hβ u)
    (poleBranchSymmetricPoincareConstant_pos hβ).le)

/-- Same canonical full PI coefficient, now with resolvent genuinely in its proof path. -/
theorem paper_full_labeled_poincare_via_resolvent {β : ℝ} (hβ : 0 < β)
    (N : ℕ) (hN : 2 ≤ N) (u : CoulombFormDomain N hβ) :
    variance (coulombFormValueL N hβ u : CoulombConfig N → ℝ) (coulombMeasure N β) ≤
      (poleBranchSymmetricPoincareConstant hβ + paperCrel β) * coulombFormEnergy N hβ u := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 2 := ⟨N - 2, by omega⟩
  have hlabel := paper_variance_reduction hβ n u
  rw [coulombFormSymmetrizer_value] at hlabel
  have hs := paper_symmetrized_poincare_via_resolvent (by omega : 2 ≤ n + 2) hβ u
  have h := hlabel.trans (add_le_add hs
    (le_rfl : paperCrel β * coulombFormEnergy (n + 2) hβ u ≤ _))
  simpa only [add_mul] using h

end RepulsiveCoulomb.PaperRoute
