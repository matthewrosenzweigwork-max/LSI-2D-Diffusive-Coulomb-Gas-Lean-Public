import LeanResearch.RepulsiveCoulomb.EquilibriumBranchLogKernel
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Actual Gaussian-mixture representation of -log |z| off the diagonal.
All scalar improper integrals are proved integrable. The absolute integral
identity is retained for the subsequent signed-energy Fubini theorem. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology
namespace RepulsiveCoulomb

def equilibriumFrullaniIntegrand (a b t : ℝ) : ℝ :=
  t⁻¹ * (Real.exp (-a * t) - Real.exp (-b * t))

private theorem equilibriumFrullani_nonneg {a b t : ℝ} (hab : a ≤ b) (ht : 0 < t) :
    0 ≤ equilibriumFrullaniIntegrand a b t := by
  apply mul_nonneg (inv_nonneg.mpr ht.le)
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  nlinarith

private theorem equilibriumFrullani_bound {a b t : ℝ} (hab : a ≤ b) (ht : 0 < t) :
    |equilibriumFrullaniIntegrand a b t| ≤ (b - a) * Real.exp (-a * t) := by
  rw [abs_of_nonneg (equilibriumFrullani_nonneg hab ht)]
  have he : Real.exp (-b * t) = Real.exp (-a * t) * Real.exp (-(b - a) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h := Real.add_one_le_exp (-(b - a) * t)
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (-a * t)).le
  have hd : Real.exp (-a * t) - Real.exp (-b * t) ≤
      (b - a) * t * Real.exp (-a * t) := by
    rw [he]
    nlinarith
  calc
    equilibriumFrullaniIntegrand a b t ≤
        t⁻¹ * ((b - a) * t * Real.exp (-a * t)) :=
      mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr ht.le)
    _ = (b - a) * Real.exp (-a * t) := by field_simp [ht.ne']

private theorem equilibriumFrullani_integrable_ordered {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) : IntegrableOn (equilibriumFrullaniIntegrand a b) (Ioi 0) := by
  have hi := (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).const_mul (b - a)
  apply hi.mono' (by unfold equilibriumFrullaniIntegrand; fun_prop)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  simpa only [Real.norm_eq_abs] using equilibriumFrullani_bound hab ht

private theorem equilibriumFrullani_swap (a b t : ℝ) :
    equilibriumFrullaniIntegrand a b t = -equilibriumFrullaniIntegrand b a t := by
  unfold equilibriumFrullaniIntegrand
  ring

theorem equilibriumFrullani_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (equilibriumFrullaniIntegrand a b) (Ioi 0) := by
  rcases le_total a b with hab | hba
  · exact equilibriumFrullani_integrable_ordered ha hab
  · have h := (equilibriumFrullani_integrable_ordered hb hba).neg
    have he : -equilibriumFrullaniIntegrand b a = equilibriumFrullaniIntegrand a b := by
      funext t
      exact (equilibriumFrullani_swap a b t).symm
    rw [he] at h
    exact h

theorem integral_equilibriumFrullani {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Ioi (0 : ℝ), equilibriumFrullaniIntegrand a b t) = Real.log (b / a) := by
  have hc : Continuous (fun t : ℝ => Real.exp (-t)) := by fun_prop
  have h0 : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝 1) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds (by
      simpa using (hc.continuousAt (x := 0)).tendsto)
  have h := Frullani.integral_Ioi_eq
    (hc.continuousOn.locallyIntegrableOn measurableSet_Ioi) ha hb h0
    Real.tendsto_exp_neg_atTop_nhds_zero
    (by
      apply (equilibriumFrullani_integrable ha hb).congr
      exact Eventually.of_forall (fun x => by
        simp only [equilibriumFrullaniIntegrand, smul_eq_mul, neg_mul]))
  simpa only [smul_eq_mul, sub_zero, mul_one, neg_mul, equilibriumFrullaniIntegrand] using h

/-- Absolute integrability is quantified exactly, for later Fubini. -/
theorem integral_abs_equilibriumFrullani {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Ioi (0 : ℝ), |equilibriumFrullaniIntegrand a b t|) = |Real.log (b / a)| := by
  rcases le_total a b with hab | hba
  · have hn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ equilibriumFrullaniIntegrand a b t := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact equilibriumFrullani_nonneg hab ht
    have he : (∫ t in Ioi (0 : ℝ), |equilibriumFrullaniIntegrand a b t|) =
        ∫ t in Ioi (0 : ℝ), equilibriumFrullaniIntegrand a b t := by
      apply integral_congr_ae
      exact hn.mono (fun _ h => abs_of_nonneg h)
    have hl : 0 ≤ Real.log (b / a) := by
      rw [← integral_equilibriumFrullani ha hb]
      exact integral_nonneg_of_ae hn
    rw [he, integral_equilibriumFrullani ha hb, abs_of_nonneg hl]
  · have hn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), equilibriumFrullaniIntegrand a b t ≤ 0 := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      rw [equilibriumFrullani_swap]
      exact neg_nonpos.mpr (equilibriumFrullani_nonneg hba ht)
    have he : (∫ t in Ioi (0 : ℝ), |equilibriumFrullaniIntegrand a b t|) =
        -(∫ t in Ioi (0 : ℝ), equilibriumFrullaniIntegrand a b t) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact hn.mono (fun _ h => abs_of_nonpos h)
    have hl : Real.log (b / a) ≤ 0 := by
      rw [← integral_equilibriumFrullani ha hb]
      exact integral_nonpos_of_ae hn
    rw [he, integral_equilibriumFrullani ha hb, abs_of_nonpos hl]

/-- Literal logarithmic kernel as a Gaussian mixture, away from the diagonal. -/
theorem equilibriumLogKernel_eq_frullani {z : ℂ} (hz : z ≠ 0) :
    equilibriumLogKernel z =
      (∫ t in Ioi (0 : ℝ), equilibriumFrullaniIntegrand (‖z‖ ^ 2) 1 t) / 2 := by
  rw [integral_equilibriumFrullani (sq_pos_of_pos (norm_pos_iff.mpr hz)) zero_lt_one,
    one_div, Real.log_inv, Real.log_pow]
  unfold equilibriumLogKernel
  ring

end RepulsiveCoulomb
