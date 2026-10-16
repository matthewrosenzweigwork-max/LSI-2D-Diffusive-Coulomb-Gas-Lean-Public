import LeanResearch.RepulsiveCoulomb.DbarBranchCutoffAdjointError
import LeanResearch.RepulsiveCoulomb.DbarBranchTwoFormFiber

/-! The literal exterior cutoff error in the fixed Hilbert fiber of i<j
coefficients. Its squared norm equals half the full Frobenius square, and the
actual L2 error tends to zero with the same proper cutoff scales. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

def dbarWedgeTwoForm {N : ℕ} (a b : CoulombConfig N) : CoulombAuxiliaryTwoForm N :=
  WithLp.toLp 2 (fun p : coulombPairs N => dbarVectorWedge a b p.1.1 p.1.2)

theorem dbarWedgeTwoForm_norm_sq {N : ℕ} (a b : CoulombConfig N) :
    ‖dbarWedgeTwoForm a b‖ ^ 2 = dbarAlternatingMatrixSq (dbarVectorWedge a b) := by
  have hasym (i j : Fin N) : dbarVectorWedge a b j i = -dbarVectorWedge a b i j := by
    unfold dbarVectorWedge
    ring
  rw [dbarAlternatingMatrixSq_pairs _ hasym, EuclideanSpace.norm_sq_eq]
  simp only [dbarWedgeTwoForm, WithLp.ofLp_toLp]
  exact Finset.sum_coe_sort (coulombPairs N)
    (fun p : Fin N × Fin N => ‖dbarVectorWedge a b p.1 p.2‖ ^ 2)

theorem dbarWedgeTwoForm_norm_le {N : ℕ} (a b : CoulombConfig N) :
    ‖dbarWedgeTwoForm a b‖ ≤ ‖a‖ * ‖b‖ := by
  have h := (dbarWedgeTwoForm_norm_sq a b).trans_le (dbarVectorWedge_bound a b)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow] using h

theorem coulombCutoffExteriorError_memLp {N : ℕ} (β : ℝ) {R : ℝ} (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    MemLp (fun z => dbarWedgeTwoForm (dbarCoreVector (coulombMetricCutoffSymbolCore hR) z) (u z))
      2 (coulombMeasure N β) := by
  apply memLp_piLp_iff.mpr
  intro p
  change MemLp (fun z => coulombMetricCutoffSymbolCore hR p.1.1 z * u z p.1.2 -
    u z p.1.1 * coulombMetricCutoffSymbolCore hR p.1.2 z) 2 (coulombMeasure N β)
  exact ((coulombMetricCutoffSymbolCore hR p.1.1).memLp_top.fun_mul
    ((Lp.memLp u).eval_piLp p.1.2)).sub
      (((Lp.memLp u).eval_piLp p.1.1).fun_mul (coulombMetricCutoffSymbolCore hR p.1.2).memLp_top)

def coulombCutoffExteriorError {N : ℕ} (β : ℝ) {R : ℝ} (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    Lp (CoulombAuxiliaryTwoForm N) 2 (coulombMeasure N β) :=
  (coulombCutoffExteriorError_memLp β hR u).toLp
    (fun z => dbarWedgeTwoForm (dbarCoreVector (coulombMetricCutoffSymbolCore hR) z) (u z))

theorem coulombCutoffExteriorError_coe {N : ℕ} (β : ℝ) {R : ℝ} (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    coulombCutoffExteriorError β hR u =ᵐ[coulombMeasure N β]
      fun z => dbarWedgeTwoForm (dbarCoreVector (coulombMetricCutoffSymbolCore hR) z) (u z) :=
  MemLp.coeFn_toLp _

theorem coulombCutoffExteriorError_raw_pointwise {N : ℕ} {R : ℝ} (hR : 0 < R)
    (z u : CoulombConfig N) (p : coulombPairs N) :
    dbarWedgeTwoForm (dbarCoreVector (coulombMetricCutoffSymbolCore hR) z) u p =
      (coulombInverseRootMatrix z *
        dbarVectorWedge (coulombDbar (fun x => (coulombMetricCutoff R x : ℂ)) z)
          (dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) u) *
        (coulombInverseRootMatrix z).transpose) p.1.1 p.1.2 := by
  rw [dbarMetric_cutoff_wedge, coulombMetricCutoffSymbolCore_vector]
  rfl

theorem coulombCutoffExteriorError_norm_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ} {β : ℝ}, 0 < β → ∀ {R : ℝ} (hR : 0 < R)
      (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)),
      ‖coulombCutoffExteriorError β hR u‖ ≤ (C / (2 * R)) * ‖u‖ := by
  obtain ⟨C, hC, hsymbol⟩ := coulombMetricCutoff_transformed_dbar_bound
  refine ⟨C, hC, ?_⟩
  intro N β hβ R hR u
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coulombCutoffExteriorError_coe β hR u,
    (coulombMeasure_ae_iff hβ).mpr (coulombDomain_ae N)] with z hz hΩ
  rw [hz]
  apply (dbarWedgeTwoForm_norm_le _ _).trans
  rw [coulombMetricCutoffSymbolCore_vector]
  exact mul_le_mul_of_nonneg_right (hsymbol hR z hΩ) (norm_nonneg _)

theorem coulombCutoffExteriorError_tendsto_zero {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    Tendsto (fun n : ℕ => coulombCutoffExteriorError β (by positivity : 0 < (n : ℝ) + 1) u)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := coulombCutoffExteriorError_norm_bound
  have hlim : Tendsto (fun n : ℕ => (C / (2 * ((n : ℝ) + 1))) * ‖u‖) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (C / 2 * ‖u‖)
    have he : (fun n : ℕ => (C / (2 * ((n : ℝ) + 1))) * ‖u‖) =
        (fun n : ℕ => (C / 2 * ‖u‖) * (1 / ((n : ℝ) + 1))) := by
      funext n
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hn] <;> ring
    rw [he]
    simpa only [mul_zero] using h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => hb hβ (by positivity) u) hlim

end RepulsiveCoulomb
