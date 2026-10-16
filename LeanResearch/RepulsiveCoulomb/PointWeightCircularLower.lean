module

public import LeanResearch.RepulsiveCoulomb.PointWeightCircle

@[expose] public section

/-! Jensen lower bounds on circles avoiding the finitely many puncture radii.
The exceptional radii are subsequently removed by radial almost-everywhere
integration, not by imposing any separation condition on the point family.
-/
noncomputable section
open MeasureTheory Real Filter
open scoped BigOperators ENNReal Topology
namespace RepulsiveCoulomb

def pointLogWeight {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ) (z : ℂ) : ℝ :=
  -γ * ‖z‖ ^ 2 / 2 + ∑ j, a j * Real.log ‖z - y j‖

theorem exp_pointLogWeight {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ)
    {z : ℂ} (hz : ∀ j, z ≠ y j) :
    Real.exp (pointLogWeight γ a y z) = pointWeight γ a y z := by
  unfold pointLogWeight pointWeight
  rw [Real.exp_add, Real.exp_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hz j)))]
  congr 1
  ring

theorem pointLocationFactor_eq_exp_sum {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) :
    pointLocationFactor a y = Real.exp (∑ j, a j * Real.log (1 + ‖y j‖)) := by
  unfold pointLocationFactor
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro j _
  rw [Real.rpow_def_of_pos (by positivity : 0 < 1 + ‖y j‖)]
  congr 1
  ring

theorem pointLogWeight_circleIntegrable {m : ℕ} (γ : ℝ) (a : Fin m → ℝ)
    (y : Fin m → ℂ) {R : ℝ} (hR : 0 ≤ R) :
    CircleIntegrable (pointLogWeight γ a y) 0 R := by
  have hgauss : CircleIntegrable (fun z : ℂ ↦ -γ * ‖z‖ ^ 2 / 2) 0 R :=
    ContinuousOn.circleIntegrable hR (by fun_prop)
  apply hgauss.add
  change IntervalIntegrable _ volume 0 (2 * Real.pi)
  convert (IntervalIntegrable.sum Finset.univ fun j _ ↦
    (circleIntegrable_log_norm_sub_const (a := y j) (c := 0) R).const_mul (a j)) using 1
  ext θ
  simp

theorem pointLogWeight_circleAverage {m : ℕ} (γ : ℝ) (a : Fin m → ℝ)
    (y : Fin m → ℂ) {R : ℝ} (hR : 0 ≤ R) :
    Real.circleAverage (pointLogWeight γ a y) 0 R = -γ * R ^ 2 / 2 +
      ∑ j, a j * Real.circleAverage (fun z : ℂ ↦ Real.log ‖z - y j‖) 0 R := by
  have hgauss : CircleIntegrable (fun z : ℂ ↦ -γ * ‖z‖ ^ 2 / 2) 0 R :=
    ContinuousOn.circleIntegrable hR (by fun_prop)
  have hlogs (j : Fin m) : CircleIntegrable (fun z : ℂ ↦ a j * Real.log ‖z - y j‖) 0 R :=
    (circleIntegrable_log_norm_sub_const (a := y j) (c := 0) R).const_mul (a j)
  have hsum : CircleIntegrable (fun z : ℂ ↦ ∑ j, a j * Real.log ‖z - y j‖) 0 R :=
    by
      change IntervalIntegrable _ volume 0 (2 * Real.pi)
      convert (IntervalIntegrable.sum Finset.univ fun j _ ↦ hlogs j) using 1
      ext θ
      simp
  unfold pointLogWeight
  rw [Real.circleAverage_fun_add hgauss hsum, Real.circleAverage_fun_sum (fun j _ ↦ hlogs j)]
  have hc : Real.circleAverage (fun z : ℂ ↦ -γ * ‖z‖ ^ 2 / 2) 0 R = -γ * R ^ 2 / 2 := by
    rw [← Real.circleAverage_const (-γ * R ^ 2 / 2) 0 R]
    apply Real.circleAverage_congr_sphere
    intro z hz
    have hn : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_zero_right, abs_of_nonneg hR] using hz
    simp only [hn]
  rw [hc]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simpa only [smul_eq_mul] using
    (Real.circleAverage_fun_smul (a := a j) (f := fun z : ℂ ↦ Real.log ‖z - y j‖) (c := 0) (R := R))

theorem pointLogWeight_circleAverage_lower {m : ℕ} {γ Q : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q)
    (y : Fin m → ℂ) {R : ℝ} (hR1 : 1 ≤ R) (hR2 : R ≤ 2) :
    -2 * γ - Q * Real.log 2 + ∑ j, a j * Real.log (1 + ‖y j‖) ≤
      Real.circleAverage (pointLogWeight γ a y) 0 R := by
  rw [pointLogWeight_circleAverage γ a y (by linarith)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦
    mul_le_mul_of_nonneg_left (circleAverage_log_distance_lower hR1 (y j)) (ha j))
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at hs
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hq := mul_le_mul_of_nonneg_right hQ hlog2
  have hsq : R ^ 2 ≤ 4 := by nlinarith
  have hg := mul_le_mul_of_nonneg_left hsq hγ.le
  linarith

theorem circleMap_avoids_points {m : ℕ} (y : Fin m → ℂ) {R : ℝ}
    (hR : 0 ≤ R) (havoid : ∀ j, R ≠ ‖y j‖) (θ : ℝ) :
    ∀ j, circleMap 0 R θ ≠ y j := by
  intro j heq
  have hn : ‖circleMap 0 R θ‖ = R := by
    simpa [Metric.mem_sphere, dist_zero_right, abs_of_nonneg hR] using
      (circleMap_mem_sphere' (0 : ℂ) R θ)
  exact havoid j (heq ▸ hn.symm)

theorem pointWeight_circleAverage_lower {m : ℕ} {γ Q : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q)
    (y : Fin m → ℂ) {R : ℝ} (hR1 : 1 ≤ R) (hR2 : R ≤ 2)
    (havoid : ∀ j, R ≠ ‖y j‖) :
    Real.exp (-2 * γ - Q * Real.log 2) * pointLocationFactor a y ≤
      Real.circleAverage (pointWeight γ a y) 0 R := by
  have hR : 0 ≤ R := by linarith
  have heq : (fun θ ↦ (Real.exp ∘ pointLogWeight γ a y) (circleMap 0 R θ)) =
      (fun θ ↦ pointWeight γ a y (circleMap 0 R θ)) := by
    funext θ
    exact exp_pointLogWeight γ a y (circleMap_avoids_points y hR havoid θ)
  have he : CircleIntegrable (Real.exp ∘ pointLogWeight γ a y) 0 R := by
    change IntervalIntegrable (fun θ ↦ (Real.exp ∘ pointLogWeight γ a y) (circleMap 0 R θ)) volume 0 (2 * Real.pi)
    rw [heq]
    exact ContinuousOn.circleIntegrable hR (pointWeight_continuous γ ha y).continuousOn
  have havg : Real.circleAverage (Real.exp ∘ pointLogWeight γ a y) 0 R =
      Real.circleAverage (pointWeight γ a y) 0 R := by
    unfold Real.circleAverage
    rw [heq]
  calc
    _ = Real.exp (-2 * γ - Q * Real.log 2 + ∑ j, a j * Real.log (1 + ‖y j‖)) := by
      rw [pointLocationFactor_eq_exp_sum, Real.exp_add]
    _ ≤ Real.exp (Real.circleAverage (pointLogWeight γ a y) 0 R) :=
      Real.exp_le_exp.mpr (pointLogWeight_circleAverage_lower hγ ha hQ y hR1 hR2)
    _ ≤ Real.circleAverage (Real.exp ∘ pointLogWeight γ a y) 0 R :=
      circleAverage_exp_ge _ _ _ (pointLogWeight_circleIntegrable γ a y hR) he
    _ = _ := havg

end RepulsiveCoulomb
