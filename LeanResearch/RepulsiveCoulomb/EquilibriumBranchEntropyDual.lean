import LeanResearch.PeriodicAttractiveLogGas.Rothaus
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Bounded scalar KL dual approximations for the thermal direct method.
This proves the actual scalar monotone approximation; it does not assume or
claim a measure-level variational equality, weak entropy lsc, or a minimizer. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology Classical
namespace RepulsiveCoulomb

def equilibriumEntropyDual (q h : ℝ) : ℝ := q * h - Real.exp h + 1

def equilibriumClippedLog (n : ℕ) (q : ℝ) : ℝ :=
  if q = 0 then -(n : ℝ) else max (-(n : ℝ)) (min (n : ℝ) (Real.log q))

theorem equilibriumEntropyDual_le {q : ℝ} (hq : 0 ≤ q) (h : ℝ) :
    equilibriumEntropyDual q h ≤ InformationTheory.klFun q := by
  have hv := PeriodicAttractiveLogGas.Rothaus.log_variational_pointwise
    (A := 1) (S := 1) hq (Real.exp_pos h) zero_lt_one zero_lt_one
  simp only [Real.log_exp, Real.log_one, mul_zero, sub_zero, one_div, inv_one, one_mul] at hv
  unfold equilibriumEntropyDual InformationTheory.klFun
  linarith

theorem equilibriumClippedLog_measurable (n : ℕ) : Measurable (equilibriumClippedLog n) :=
  measurable_const.ite (measurableSet_singleton (0 : ℝ))
    (measurable_const.max (measurable_const.min Real.measurable_log))

theorem equilibriumClippedLog_mem (n : ℕ) (q : ℝ) :
    equilibriumClippedLog n q ∈ Icc (-(n : ℝ)) (n : ℝ) := by
  have hn := Nat.cast_nonneg (α := ℝ) n
  by_cases hq : q = 0
  · simp only [equilibriumClippedLog, if_pos hq, mem_Icc]
    constructor <;> linarith
  · simp only [equilibriumClippedLog, if_neg hq, mem_Icc]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

private theorem equilibrium_exp_tangent (a h : ℝ) :
    Real.exp a + Real.exp a * (h - a) ≤ Real.exp h := by
  have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (h - a)) (Real.exp_pos a).le
  rw [← Real.exp_add, show a + (h - a) = h by ring] at hh
  nlinarith

private theorem equilibriumEntropyDual_le_of_product {q a h : ℝ}
    (hp : (q - Real.exp a) * (h - a) ≤ 0) :
    equilibriumEntropyDual q h ≤ equilibriumEntropyDual q a := by
  have ht := equilibrium_exp_tangent a h
  unfold equilibriumEntropyDual
  nlinarith

/-- Clipped logarithms are actual maximizers of the scalar dual on [-n,n]. -/
theorem equilibriumClippedLog_maximizes {q : ℝ} (hq : 0 ≤ q) (n : ℕ)
    {h : ℝ} (hh : h ∈ Icc (-(n : ℝ)) (n : ℝ)) :
    equilibriumEntropyDual q h ≤ equilibriumEntropyDual q (equilibriumClippedLog n q) := by
  have hn := Nat.cast_nonneg (α := ℝ) n
  apply equilibriumEntropyDual_le_of_product
  by_cases hq0 : q = 0
  · subst q
    simp only [equilibriumClippedLog, if_pos rfl, zero_sub]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le)
      (sub_nonneg.mpr hh.1)
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  by_cases hlo : Real.log q ≤ -(n : ℝ)
  · have hc : equilibriumClippedLog n q = -(n : ℝ) := by
      rw [equilibriumClippedLog, if_neg hq0, min_eq_right (by linarith), max_eq_left hlo]
    have hqe : q ≤ Real.exp (-(n : ℝ)) := by
      simpa only [Real.exp_log hqp] using Real.exp_le_exp.mpr hlo
    rw [hc]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hqe) (sub_nonneg.mpr hh.1)
  by_cases hhi : (n : ℝ) ≤ Real.log q
  · have hc : equilibriumClippedLog n q = (n : ℝ) := by
      rw [equilibriumClippedLog, if_neg hq0, min_eq_left hhi, max_eq_right (by linarith)]
    have heq : Real.exp (n : ℝ) ≤ q := by
      simpa only [Real.exp_log hqp] using Real.exp_le_exp.mpr hhi
    rw [hc]
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr heq) (sub_nonpos.mpr hh.2)
  · have hc : equilibriumClippedLog n q = Real.log q := by
      rw [equilibriumClippedLog, if_neg hq0, min_eq_right (le_of_not_ge hhi),
        max_eq_right (le_of_not_ge hlo)]
    simp only [hc, Real.exp_log hqp, sub_self, zero_mul, le_refl]

theorem equilibriumEntropyDual_clipped_nonneg {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    0 ≤ equilibriumEntropyDual q (equilibriumClippedLog n q) := by
  have hn := Nat.cast_nonneg (α := ℝ) n
  have h := equilibriumClippedLog_maximizes hq n (h := 0) ⟨by linarith, hn⟩
  simpa only [equilibriumEntropyDual, mul_zero, Real.exp_zero, zero_sub, neg_add_cancel] using h

theorem equilibriumEntropyDual_clipped_monotone {q : ℝ} (hq : 0 ≤ q) :
    Monotone (fun n : ℕ => equilibriumEntropyDual q (equilibriumClippedLog n q)) := by
  intro n m hnm
  have hn := equilibriumClippedLog_mem n q
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  exact equilibriumClippedLog_maximizes hq m ⟨by linarith [hn.1], by linarith [hn.2]⟩

/-- The bounded nonnegative dual values increase to the full scalar KL density,
including q=0. No integrability or finite-entropy hypothesis is inserted. -/
theorem equilibriumEntropyDual_clipped_tendsto {q : ℝ} (hq : 0 ≤ q) :
    Tendsto (fun n : ℕ => equilibriumEntropyDual q (equilibriumClippedLog n q)) atTop
      (𝓝 (InformationTheory.klFun q)) := by
  by_cases hq0 : q = 0
  · subst q
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    have hseq : (fun n : ℕ => equilibriumEntropyDual 0 (equilibriumClippedLog n 0)) =
        (fun n : ℕ => 1 - Real.exp (-(n : ℝ))) := by
      funext n
      simp [equilibriumEntropyDual, equilibriumClippedLog, sub_eq_add_neg, add_comm]
    rw [hseq, InformationTheory.klFun_zero]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub he
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  have heq : (fun n : ℕ => equilibriumEntropyDual q (equilibriumClippedLog n q))
      =ᶠ[atTop] (fun _ => InformationTheory.klFun q) := by
    obtain ⟨N, hN⟩ := exists_nat_ge |Real.log q|
    filter_upwards [eventually_ge_atTop N] with n hn
    have habs : |Real.log q| ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
    have hb := abs_le.mp habs
    rw [equilibriumClippedLog, if_neg hq0, min_eq_right hb.2, max_eq_right hb.1]
    simp only [equilibriumEntropyDual, Real.exp_log hqp, InformationTheory.klFun]
    ring
  exact (tendsto_congr' heq).mpr tendsto_const_nhds

end RepulsiveCoulomb
