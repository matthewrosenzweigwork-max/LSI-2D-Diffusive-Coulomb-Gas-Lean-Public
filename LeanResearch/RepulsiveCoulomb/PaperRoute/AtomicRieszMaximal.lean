import LeanResearch.RepulsiveCoulomb.PaperRoute.FiniteMeasurePlanarMaximal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! A finite-distance layer-cake proof of the near/far Riesz estimate used by
the canonical finite-atomic maximal argument. Each integrated summand has
support bounded away from zero. The singular inverse at distance zero uses
Lean's zero representative; its layer summand is zero as well. -/
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal BigOperators Interval
namespace RepulsiveCoulomb.PaperRoute

/-- One bounded, positive-distance layer. There is no improper integral at zero. -/
def positiveDistanceLayer (d R t : ℝ) : ℝ :=
  if 0 < d then (Ioc d R).indicator (fun s : ℝ => s ^ (-2 : ℤ)) t else 0

theorem positiveDistanceLayer_integrable (d R : ℝ) :
    Integrable (positiveDistanceLayer d R) := by
  unfold positiveDistanceLayer
  by_cases hd : 0 < d
  · by_cases hdR : d ≤ R
    · have hnot : (0 : ℝ) ∉ [[d, R]] := by
        rw [uIcc_of_le hdR]
        exact fun h => (not_le_of_gt hd) h.1
      have hi : IntegrableOn (fun s : ℝ => s ^ (-2 : ℤ)) (Ioc d R) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hdR).mp
          (intervalIntegral.intervalIntegrable_zpow (Or.inr hnot))
      simpa only [positiveDistanceLayer, ite_eq_left hd] using hi.integrable_indicator measurableSet_Ioc
    · simp [hd, Ioc_eq_empty_of_le (le_of_not_ge hdR)]
  · simp [hd]

/-- Scalar layer cake with a far contribution 1/R. Valid also at totalized d=0. -/
theorem inverse_le_far_add_layer {d R : ℝ} (hd : 0 ≤ d) (hR : 0 < R) :
    d⁻¹ ≤ R⁻¹ + ∫ t, positiveDistanceLayer d R t := by
  unfold positiveDistanceLayer
  by_cases hdpos : 0 < d
  · by_cases hdR : d ≤ R
    · have hnot : (0 : ℝ) ∉ [[d, R]] := by
        rw [uIcc_of_le hdR]
        exact fun h => (not_le_of_gt hdpos) h.1
      simp only [ite_eq_left hdpos]
      rw [integral_indicator measurableSet_Ioc,
        ← intervalIntegral.integral_of_le hdR,
        integral_zpow (Or.inr ⟨by norm_num, hnot⟩)]
      norm_num
      linarith
    · have hRd : R ≤ d := le_of_not_ge hdR
      simp only [ite_eq_left hdpos, Ioc_eq_empty_of_le hRd,
        indicator_empty, integral_zero, add_zero]
      exact inv_anti₀ hR hRd
  · have hd0 : d = 0 := le_antisymm (le_of_not_gt hdpos) hd
    simp [hd0, hR.le]

theorem positiveDistanceLayer_nonneg (d R t : ℝ) : 0 ≤ positiveDistanceLayer d R t := by
  unfold positiveDistanceLayer
  split_ifs
  · exact indicator_nonneg (fun s _ => by positivity) _
  · exact le_rfl

/-- The finite scalar Riesz split follows from actual ball growth at every radius. -/
theorem finite_inverse_sum_le_of_ball_growth {m : ℕ} (a d : Fin m → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hd : ∀ j, 0 ≤ d j) {b R : ℝ}
    (_hb : 0 ≤ b) (hR : 0 < R)
    (hgrowth : ∀ t : ℝ, 0 < t → (∑ j, if d j < t then a j else 0) ≤ b * t ^ 2) :
    (∑ j, a j * (d j)⁻¹) ≤ (∑ j, a j) / R + b * R := by
  classical
  let F : ℝ → ℝ := fun t => ∑ j, a j * positiveDistanceLayer (d j) R t
  have hFi : Integrable F := integrable_finsetSum _
    (fun j _ => (positiveDistanceLayer_integrable (d j) R).const_mul (a j))
  have hBi : Integrable ((Ioc (0 : ℝ) R).indicator (fun _ => b)) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Ioc
  have hpoint : ∀ t, F t ≤ (Ioc (0 : ℝ) R).indicator (fun _ => b) t := by
    intro t
    by_cases ht : t ∈ Ioc (0 : ℝ) R
    · rw [indicator_of_mem ht]
      have hterm : ∀ j, a j * positiveDistanceLayer (d j) R t ≤
          (if d j < t then a j else 0) * t ^ (-2 : ℤ) := by
        intro j
        by_cases hdj : 0 < d j <;> by_cases hdt : d j < t
        · simp [positiveDistanceLayer, hdj, indicator_of_mem (show t ∈ Ioc (d j) R from ⟨hdt, ht.2⟩), hdt]
        · simp [positiveDistanceLayer, hdj, hdt]
        · simp only [positiveDistanceLayer, ite_eq_right hdj, mul_zero, ite_eq_left hdt]
          exact mul_nonneg (ha j) (by positivity)
        · simp [positiveDistanceLayer, hdj, hdt]
      calc
        F t ≤ ∑ j, (if d j < t then a j else 0) * t ^ (-2 : ℤ) :=
          Finset.sum_le_sum (fun j _ => hterm j)
        _ = (∑ j, if d j < t then a j else 0) * t ^ (-2 : ℤ) :=
          (Finset.sum_mul _ _ _).symm
        _ ≤ (b * t ^ 2) * t ^ (-2 : ℤ) :=
          mul_le_mul_of_nonneg_right (hgrowth t ht.1) (by positivity)
        _ = b := by rw [zpow_neg, zpow_ofNat]; field_simp [ht.1.ne']
    · have hzero : F t = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        by_cases hdj : 0 < d j
        · have hnot : t ∉ Ioc (d j) R := fun h => ht ⟨hdj.trans h.1, h.2⟩
          simp [positiveDistanceLayer, hdj, indicator_of_notMem hnot]
        · simp [positiveDistanceLayer, hdj]
      rw [hzero, indicator_of_notMem ht]
  have hint : (∫ t, F t) ≤ b * R := by
    have hh := integral_mono hFi hBi hpoint
    simpa [integral_indicator measurableSet_Ioc, setIntegral_const, Real.volume_Ioc,
      measureReal_def, ENNReal.toReal_ofReal hR.le, mul_comm] using hh
  calc
    (∑ j, a j * (d j)⁻¹) ≤ ∑ j, a j * (R⁻¹ + ∫ t, positiveDistanceLayer (d j) R t) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (inverse_le_far_add_layer (hd j) hR) (ha j))
    _ = (∑ j, a j) / R + ∫ t, F t := by
      rw [show (∫ t, F t) = ∑ j, ∫ t, a j * positiveDistanceLayer (d j) R t from
        integral_finsetSum _ (fun j _ => (positiveDistanceLayer_integrable (d j) R).const_mul (a j))]
      simp only [integral_const_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul, div_eq_mul_inv]
    _ ≤ _ := add_le_add le_rfl hint

end RepulsiveCoulomb.PaperRoute
