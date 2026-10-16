import LeanResearch.RepulsiveCoulomb.PaperRoute.AtomicRieszMaximal
import LeanResearch.RepulsiveCoulomb.PointLogForceWeakL2
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! The canonical finite-atomic maximal-function proof of the physical
logarithmic force weak L2 estimate. The old weak L2 theorem and kernel
truncation producer are not used: from that file only the literal force
and its elementary triangle inequality are used.

The totalized inverse-distance representative is zero at a site. The site
set is proved Lebesgue null below, so the pointwise result also represents
the usual physical force defined off the sites. Arbitrary coincidences,
zero exponents and the empty family are allowed. -/
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb.PaperRoute

/-- The actual finite atomic measure occurring in the manuscript. -/
def pointAtomicMeasure {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) : Measure ℂ :=
  ∑ j, ENNReal.ofReal (a j) • Measure.dirac (y j)

instance pointAtomicMeasure_isFinite {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) :
    IsFiniteMeasure (pointAtomicMeasure a y) := by
  constructor
  simp only [pointAtomicMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.ofReal_lt_top)

theorem pointAtomicMeasure_univ {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    pointAtomicMeasure a y univ = ENNReal.ofReal (∑ j, a j) := by
  simp only [pointAtomicMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  exact (ENNReal.ofReal_sum_of_nonneg (fun j _ => ha j)).symm

theorem pointAtomicMeasure_ball {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x : ℂ) (r : ℝ) :
    pointAtomicMeasure a y (ball x r) =
      ENNReal.ofReal (∑ j, if ‖x - y j‖ < r then a j else 0) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by split_ifs; exact ha j; exact le_rfl)]
  simp only [pointAtomicMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : ‖x - y j‖ < r
  · have hmem : y j ∈ ball x r := by simpa [mem_ball, dist_comm, dist_eq_norm] using hj
    simp [hmem, hj]
  · have hmem : y j ∉ ball x r := by simpa [mem_ball, dist_comm, dist_eq_norm] using hj
    simp [hmem, hj]

theorem volume_point_sites_zero {m : ℕ} (y : Fin m → ℂ) : volume (range y) = 0 :=
  (finite_range y).measure_zero volume

theorem ae_off_point_sites {m : ℕ} (y : Fin m → ℂ) :
    ∀ᵐ z : ℂ, z ∉ range y := by
  rw [ae_iff]
  convert volume_point_sites_zero y using 2
  ext z
  simp

/-- At a site the totalized single logarithmic-force summand is zero. -/
theorem logForceKernel_zero_representative : ((‖(0 : ℂ)‖ ^ 2)⁻¹ : ℝ) • (0 : ℂ) = 0 :=
  by simp

/-- Riesz near/far splitting from the literal atomic measure's maximal value. -/
theorem pointLogForce_le_mass_div_add_maximal {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x : ℂ) {b R : ℝ}
    (hb : 0 ≤ b) (hR : 0 < R)
    (hmax : planarMeasureMaximal (pointAtomicMeasure a y) x ≤ ENNReal.ofReal b) :
    ‖pointLogForce a y x‖ ≤ (∑ j, a j) / R + Real.pi * b * R := by
  apply (norm_pointLogForce_le ha y x).trans
  apply finite_inverse_sum_le_of_ball_growth a (fun j => ‖x - y j‖) ha
    (fun j => norm_nonneg _) (mul_nonneg Real.pi_pos.le hb) hR
  intro r hr
  have h := planarMeasureMaximal_ball_growth (pointAtomicMeasure a y) x hr hmax
  rw [pointAtomicMeasure_ball ha y, planar_ball_volume_eq x hr.le,
    ← ENNReal.ofReal_mul hb] at h
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp at h
  nlinarith [h]

/-- Optimization at R=2q/t; this is the canonical Hedberg superlevel inclusion. -/
theorem pointLogForce_superlevel_subset_maximal {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hq : 0 < ∑ j, a j)
    {t : ℝ} (ht : 0 < t) :
    {x : ℂ | t < ‖pointLogForce a y x‖} ⊆
      {x | ENNReal.ofReal (t ^ 2 / (4 * Real.pi * (∑ j, a j))) <
        planarMeasureMaximal (pointAtomicMeasure a y) x} := by
  intro x hx
  by_contra hnot
  have hmax : planarMeasureMaximal (pointAtomicMeasure a y) x ≤
      ENNReal.ofReal (t ^ 2 / (4 * Real.pi * (∑ j, a j))) := le_of_not_gt hnot
  have h := pointLogForce_le_mass_div_add_maximal ha y x
    (R := 2 * (∑ j, a j) / t) (by positivity) (by positivity) hmax
  have heq : (∑ j, a j) / (2 * (∑ j, a j) / t) +
      Real.pi * (t ^ 2 / (4 * Real.pi * (∑ j, a j))) * (2 * (∑ j, a j) / t) = t := by
    field_simp [ht.ne', hq.ne', Real.pi_ne_zero]
    ring
  rw [heq] at h
  exact (not_lt_of_ge h) hx

/-- Actual finite-point weak L2 estimate, produced by the finite-measure maximal proof. -/
theorem pointLogForce_weak_l2_atomic_maximal {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {t : ℝ} (ht : 0 < t) :
    volume {x : ℂ | t < ‖pointLogForce a y x‖} ≤
      ENNReal.ofReal (64 * Real.pi * (∑ j, a j) ^ 2 / t ^ 2) := by
  classical
  have hq : 0 ≤ ∑ j, a j := Finset.sum_nonneg (fun j _ => ha j)
  by_cases hq0 : ∑ j, a j = 0
  · have hazero : ∀ j, a j = 0 := by
      intro j
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => ha j)).mp hq0 j (Finset.mem_univ j)
    simp [pointLogForce, hazero, not_lt_of_ge ht.le]
  · have hqpos : 0 < ∑ j, a j := lt_of_le_of_ne hq (Ne.symm hq0)
    have hlevel : 0 < t ^ 2 / (4 * Real.pi * (∑ j, a j)) := by positivity
    calc
      volume {x : ℂ | t < ‖pointLogForce a y x‖} ≤
          volume {x | ENNReal.ofReal (t ^ 2 / (4 * Real.pi * (∑ j, a j))) <
            planarMeasureMaximal (pointAtomicMeasure a y) x} :=
        measure_mono (pointLogForce_superlevel_subset_maximal ha y hqpos ht)
      _ ≤ (16 * pointAtomicMeasure a y univ) /
          ENNReal.ofReal (t ^ 2 / (4 * Real.pi * (∑ j, a j))) :=
        planarMeasureMaximal_weak_measure (pointAtomicMeasure a y) hlevel
      _ = ENNReal.ofReal (64 * Real.pi * (∑ j, a j) ^ 2 / t ^ 2) := by
        rw [pointAtomicMeasure_univ ha y]
        rw [show (16 : ℝ≥0∞) = ENNReal.ofReal (16 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_div_of_pos hlevel]
        congr 1
        field_simp [ht.ne', hqpos.ne', Real.pi_ne_zero]
        ring

/-- Configuration-uniform maximal-route endpoint under a prescribed total cap. -/
theorem pointLogForce_weak_l2_atomic_maximal_of_total_le {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {Q t : ℝ}
    (hQ : ∑ j, a j ≤ Q) (ht : 0 < t) :
    volume {x : ℂ | t < ‖pointLogForce a y x‖} ≤
      ENNReal.ofReal (64 * Real.pi * Q ^ 2 / t ^ 2) := by
  apply (pointLogForce_weak_l2_atomic_maximal ha y ht).trans
  apply ENNReal.ofReal_le_ofReal
  have hq : 0 ≤ ∑ j, a j := Finset.sum_nonneg (fun j _ => ha j)
  have hsq : (∑ j, a j) ^ 2 ≤ Q ^ 2 := by nlinarith
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity)) (sq_nonneg t)

end RepulsiveCoulomb.PaperRoute
