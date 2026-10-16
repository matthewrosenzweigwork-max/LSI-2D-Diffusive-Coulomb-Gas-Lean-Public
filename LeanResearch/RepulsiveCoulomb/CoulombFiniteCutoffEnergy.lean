module

public import LeanResearch.RepulsiveCoulomb.CoulombFiniteCutoff

@[expose] public section

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem coulombAvoidanceCutoff_gradient_bound (N : ℕ) (ε : ℝ) (hε : 0 < ε) (z : CoulombConfig N) :
    ‖gradient (coulombAvoidanceCutoff N ε hε) z‖ ≤
      ∑ p ∈ coulombPairs N, ‖gradient (coulombCollisionBump p.1 p.2 ε hε) z‖ := by
  classical
  have hd (p : Fin N × Fin N) : DifferentiableAt ℝ (coulombCollisionBump p.1 p.2 ε hε) z :=
    (coulombCollisionBump_contDiff p.1 p.2 ε hε).differentiable (by simp) z
  rw [TauCeti.norm_gradient_eq_norm_fderiv]
  unfold coulombAvoidanceCutoff
  rw [fderiv_finsetProd (fun p _ => (hd p).const_sub 1)]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_smul, fderiv_const_sub 1, norm_neg, TauCeti.norm_gradient_eq_norm_fderiv]
  have hp0 : 0 ≤ ∏ q ∈ (coulombPairs N).erase p, (1 - coulombCollisionBump q.1 q.2 ε hε z) :=
    Finset.prod_nonneg (fun q _ => sub_nonneg.mpr (coulombCollisionBump_le_one q.1 q.2 ε hε z))
  have hp1 : (∏ q ∈ (coulombPairs N).erase p, (1 - coulombCollisionBump q.1 q.2 ε hε z)) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro q hq
      exact sub_nonneg.mpr (coulombCollisionBump_le_one q.1 q.2 ε hε z)
    · intro q hq
      linarith [coulombCollisionBump_nonneg q.1 q.2 ε hε z]
  rw [Real.norm_eq_abs, abs_of_nonneg hp0]
  exact mul_le_of_le_one_left (norm_nonneg _) hp1

theorem coulombAvoidanceCutoff_gradient_sq_bound (N : ℕ) (ε : ℝ) (hε : 0 < ε) (z : CoulombConfig N) :
    ‖gradient (coulombAvoidanceCutoff N ε hε) z‖ ^ 2 ≤
      (coulombPairs N).card * ∑ p ∈ coulombPairs N, ‖gradient (coulombCollisionBump p.1 p.2 ε hε) z‖ ^ 2 :=
  (pow_le_pow_left₀ (norm_nonneg _) (coulombAvoidanceCutoff_gradient_bound N ε hε z) 2).trans
    sq_sum_le_card_mul_sum_sq

theorem coulombAvoidanceCutoff_energy_integrable (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun z => ‖gradient (coulombAvoidanceCutoff (N + 2) ε hε) z‖ ^ 2)
      (coulombMeasure (N + 2) β) := by
  have hi := (integrable_finsetSum (coulombPairs (N + 2)) (fun p hp =>
    coulombCollisionBump_energy_integrable hβ p.1 p.2 (ne_of_lt ((mem_coulombPairs p).mp hp)) ε hε)).const_mul
      ((coulombPairs (N + 2)).card : ℝ)
  apply hi.mono'
  · exact (((coulombAvoidanceCutoff_contDiff (N + 2) ε hε).gradient_right
      (m := (⊤ : ℕ∞)) (by simp)).continuous.norm.pow 2).aestronglyMeasurable
  · exact Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact coulombAvoidanceCutoff_gradient_sq_bound (N + 2) ε hε z)

theorem coulombAvoidanceCutoff_energy_le_sum (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (ε : ℝ) (hε : 0 < ε) :
    (∫ z, ‖gradient (coulombAvoidanceCutoff (N + 2) ε hε) z‖ ^ 2 ∂coulombMeasure (N + 2) β) ≤
      (coulombPairs (N + 2)).card * ∑ p ∈ coulombPairs (N + 2),
        ∫ z, ‖gradient (coulombCollisionBump p.1 p.2 ε hε) z‖ ^ 2 ∂coulombMeasure (N + 2) β := by
  have hi := integrable_finsetSum (coulombPairs (N + 2)) (fun p hp =>
    coulombCollisionBump_energy_integrable hβ p.1 p.2 (ne_of_lt ((mem_coulombPairs p).mp hp)) ε hε)
  have h := integral_mono (coulombAvoidanceCutoff_energy_integrable N hβ ε hε)
    (hi.const_mul ((coulombPairs (N + 2)).card : ℝ))
      (coulombAvoidanceCutoff_gradient_sq_bound (N + 2) ε hε)
  have he : (∫ z, ∑ p ∈ coulombPairs (N + 2), ‖gradient (coulombCollisionBump p.1 p.2 ε hε) z‖ ^ 2
      ∂coulombMeasure (N + 2) β) = ∑ p ∈ coulombPairs (N + 2),
        ∫ z, ‖gradient (coulombCollisionBump p.1 p.2 ε hε) z‖ ^ 2 ∂coulombMeasure (N + 2) β :=
    integral_finsetSum _ (fun p hp => coulombCollisionBump_energy_integrable hβ p.1 p.2
      (ne_of_lt ((mem_coulombPairs p).mp hp)) ε hε)
  rw [integral_const_mul, he] at h
  exact h

theorem coulombAvoidanceCutoff_energy_tendsto_zero (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, ‖gradient (coulombAvoidanceCutoff (N + 2) (ε n) (hε n)) z‖ ^ 2
      ∂coulombMeasure (N + 2) β) atTop (𝓝 0) := by
  have hs := tendsto_finsetSum (coulombPairs (N + 2)) (fun p hp =>
    coulombCollisionBump_energy_tendsto_zero hβ p.1 p.2 (ne_of_lt ((mem_coulombPairs p).mp hp)) ε hε hlim)
  apply squeeze_zero (fun n => integral_nonneg (fun z => sq_nonneg _))
    (fun n => coulombAvoidanceCutoff_energy_le_sum N hβ (ε n) (hε n))
  simpa using hs.const_mul ((coulombPairs (N + 2)).card : ℝ)

end RepulsiveCoulomb

