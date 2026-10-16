module

public import LeanResearch.RepulsiveCoulomb.CoulombCollisionGaussian
public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchCompetitorIntegrability

@[expose] public section

/-! The authored collision-log integrability argument: retain one positive
collision power, bound r^alpha*(-log r)_+, and absorb all remaining factors in
a genuine Gaussian majorant. This is independent of exponential moments of A. -/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb.PaperRoute

theorem paper_rpow_positive_log_bound {r α : ℝ} (hr : 0 ≤ r) (hα : 0 < α) :
    r ^ α * max (-Real.log r) 0 ≤ 1 / α := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [Real.zero_rpow hα.ne', hα.le]
  by_cases hr1 : 1 ≤ r
  · rw [max_eq_right (neg_nonpos.mpr (Real.log_nonneg hr1)), mul_zero]
    positivity
  have hl0 : 0 ≤ -Real.log r := neg_nonneg.mpr (Real.log_nonpos hr.le (le_of_not_ge hr1))
  rw [max_eq_left hl0]
  have hl := Real.add_one_le_exp (-α * Real.log r)
  have hm := mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg hr.le α)
  have he : r ^ α * Real.exp (-α * Real.log r) = 1 := by
    rw [Real.rpow_def_of_pos hr, ← Real.exp_add]
    have hz : Real.log r * α + -α * Real.log r = 0 := by ring
    rw [hz, Real.exp_zero]
  rw [he] at hm
  apply (le_div_iff₀ hα).mpr
  nlinarith [Real.rpow_nonneg hr.le α]

theorem paper_coulomb_positive_log_density_gaussian_bound {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (p : Fin N × Fin N) (hp : p ∈ coulombPairs N) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : CoulombConfig N,
      coulombDensity N β z * equilibriumLogPositive (z p.1 - z p.2) ≤
        C * Real.exp (-(β / 4) * ‖z‖ ^ 2) := by
  have hn : 0 < N := by have := p.1.isLt; omega
  have hα : 0 < β / (N : ℝ) := div_pos hβ (by exact_mod_cast hn)
  obtain ⟨C, hC, hb⟩ := coulombDensity_le_gaussian_collision_power hβ p hp
  refine ⟨C / (β / (N : ℝ)), div_pos hC hα, ?_⟩
  intro z
  have hlog := paper_rpow_positive_log_bound (norm_nonneg (z p.1 - z p.2)) hα
  change ‖z p.1 - z p.2‖ ^ (β / (N : ℝ)) * equilibriumLogPositive (z p.1 - z p.2) ≤
    1 / (β / (N : ℝ)) at hlog
  have h1 := mul_le_mul_of_nonneg_right (hb z) (equilibriumLogPositive_nonneg (z p.1 - z p.2))
  have h2 := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg hC.le (Real.exp_pos (-(β / 4) * ‖z‖ ^ 2)).le)
  calc
    _ ≤ (C * Real.exp (-(β / 4) * ‖z‖ ^ 2) *
        ‖z p.1 - z p.2‖ ^ (β / (N : ℝ))) * equilibriumLogPositive (z p.1 - z p.2) := h1
    _ ≤ _ := by convert h2 using 1 <;> ring

theorem paper_coulomb_positive_log_integrable_of_pair {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (p : Fin N × Fin N) (hp : p ∈ coulombPairs N) :
    Integrable (fun z : CoulombConfig N => equilibriumLogPositive (z p.1 - z p.2))
      (coulombMeasure N β) := by
  obtain ⟨C, _hC, hb⟩ := paper_coulomb_positive_log_density_gaussian_bound hβ p hp
  have hm : Measurable (fun z : CoulombConfig N => equilibriumLogPositive (z p.1 - z p.2)) :=
    equilibriumLogPositive_measurable.comp
      ((coulombCoordinate p.1).continuous.measurable.sub (coulombCoordinate p.2).continuous.measurable)
  have hi : Integrable (fun z : CoulombConfig N =>
      coulombDensity N β z * equilibriumLogPositive (z p.1 - z p.2)) := by
    apply ((integrable_coulomb_gaussian N (by positivity : 0 < β / 4)).const_mul C).mono'
      ((coulombDensity_continuous hβ.le).measurable.mul hm).aestronglyMeasurable
    filter_upwards with z
    change ‖coulombDensity N β z * equilibriumLogPositive (z p.1 - z p.2)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (coulombDensity_nonneg β z)
      (equilibriumLogPositive_nonneg (z p.1 - z p.2))) ]
    exact hb z
  rw [coulombMeasure_eq_withDensity hβ]
  apply (integrable_withDensity_iff
    (coulombDensity_continuous hβ.le).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  simpa only [ENNReal.toReal_ofReal (coulombDensity_nonneg β _), smul_eq_mul, mul_comm] using hi

theorem paper_coulomb_pair_positive_log_integrable {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (i j : Fin N) :
    Integrable (fun z : CoulombConfig N => equilibriumLogPositive (z i - z j))
      (coulombMeasure N β) := by
  let := coulombMeasure_isProbability (N := N) hβ
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact paper_coulomb_positive_log_integrable_of_pair hβ (i,j) ((mem_coulombPairs _).mpr hij)
  · simpa only [sub_self, equilibriumLogPositive, equilibriumLogKernel, norm_zero,
      Real.log_zero, neg_zero, max_self] using (integrable_const (μ := coulombMeasure N β) (0 : ℝ))
  · apply (paper_coulomb_positive_log_integrable_of_pair hβ (j,i)
      ((mem_coulombPairs _).mpr hji)).congr
    filter_upwards with z
    simp only [equilibriumLogPositive, equilibriumLogKernel, norm_sub_rev]

theorem paper_coulomb_pair_log_integrable {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (i j : Fin N) :
    Integrable (fun z : CoulombConfig N => equilibriumLogKernel (z i - z j))
      (coulombMeasure N β) := by
  let := coulombMeasure_isProbability (N := N) hβ
  have hQ2 := (coulomb_finite_entropy_quadratic_moment hβ
    (Q := coulombMeasure N β) (by simp)).1
  have hm : Measurable (fun z : CoulombConfig N => equilibriumLogKernel (z i - z j)) :=
    equilibriumLogKernel_measurable.comp
      ((coulombCoordinate i).continuous.measurable.sub (coulombCoordinate j).continuous.measurable)
  apply integrable_of_le_of_le hm.aestronglyMeasurable
    (g₁ := fun z => -equilibriumLogMoment (z i) - equilibriumLogMoment (z j))
    (g₂ := fun z => equilibriumLogPositive (z i - z j))
  · exact Eventually.of_forall (fun z => equilibriumLogKernel_sub_lower (z i) (z j))
  · exact Eventually.of_forall (fun _ => le_max_left _ _)
  · exact (conditionalEntropyBranch_log_coordinate_integrable hQ2 i).neg.sub
      (conditionalEntropyBranch_log_coordinate_integrable hQ2 j)
  · exact paper_coulomb_pair_positive_log_integrable hβ i j

/-- The actual A and B integrability now follows by finite sums and the
one-body potential bound, with the positive collision logarithms controlled
by the retained density power rather than a modulated-energy moment. -/
theorem paper_thermal_B_gibbs_integrable_positive_log {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β) :
    Integrable (conditionalEntropyBranchThermalB R) (coulombMeasure N β) := by
  classical
  let := coulombMeasure_isProbability (N := N) hβ
  have hQ2 := (coulomb_finite_entropy_quadratic_moment hβ
    (Q := coulombMeasure N β) (by simp)).1
  have hu := conditionalEntropyBranch_thermal_sum_integrable R hQ2
  have hs : Integrable (fun z : CoulombConfig N =>
      equilibriumOrderedOffDiagonalSum (fun i j => equilibriumLogKernel (z i - z j)))
      (coulombMeasure N β) := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    apply integrable_finsetSum Finset.univ
    intro j hj
    by_cases hij : i = j
    · simp only [hij, ite_true]
      exact integrable_zero _ _ _
    · simpa only [hij, ite_false] using paper_coulomb_pair_log_integrable hβ i j
  have hA := ((hs.div_const (2 * (N : ℝ))).sub hu).add
    (integrable_const ((N : ℝ) * equilibriumDensityInteraction R.density / 2))
  exact hA.add (hu.div_const (N : ℝ))

end RepulsiveCoulomb.PaperRoute
