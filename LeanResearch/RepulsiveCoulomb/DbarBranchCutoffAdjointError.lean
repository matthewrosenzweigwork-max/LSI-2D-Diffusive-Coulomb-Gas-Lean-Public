import LeanResearch.RepulsiveCoulomb.DbarBranchWeightedCoreMultiplierL2
import LeanResearch.RepulsiveCoulomb.DbarBranchMetricCutoffSymbols
import LeanResearch.RepulsiveCoulomb.DbarBranchMetricCutoffL2
import Mathlib.Analysis.SpecificLimits.Basic

/-! The actual scalar cutoff commutator is a bounded complex-linear map on
auxiliary vector L2. Its representative is <R dbar(theta),u>, and its norm
tends to zero at the explicit proper cutoff scales. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology BigOperators ComplexConjugate
namespace RepulsiveCoulomb

def coulombMetricCutoffSymbolCore {N : ℕ} {R : ℝ} (hR : 0 < R) :
    Fin N → TestFunction (coulombDomain N) ℂ ⊤ :=
  coulombInverseRootCore (fun i => coulombDbarCoreCoordinateL N i
    (TestFunction.postcompCLM Complex.ofRealCLM (coulombMetricCutoffTest (N := N) hR)))

theorem coulombMetricCutoffSymbolCore_vector {N : ℕ} {R : ℝ} (hR : 0 < R)
    (z : CoulombConfig N) :
    dbarCoreVector (coulombMetricCutoffSymbolCore (N := N) hR) z =
      dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z))
        (coulombDbar (fun x => (coulombMetricCutoff (N := N) R x : ℂ)) z) := by
  rw [coulombMetricCutoffSymbolCore, coulombInverseRootCore_vector]
  congr 1
  ext i
  exact coulombDbarCoreCoordinateL_apply N i _ z

def coulombCutoffAdjointErrorL {N : ℕ} (β : ℝ) {R : ℝ} (hR : 0 < R) :
    Lp (CoulombConfig N) 2 (coulombMeasure N β) →L[ℂ] Lp ℂ 2 (coulombMeasure N β) :=
  ∑ i, (coulombCoreMultiplierL2L β
      (TestFunction.postcompCLM Complex.conjCLE.toContinuousLinearMap (coulombMetricCutoffSymbolCore hR i))).comp
    ((EuclideanSpace.proj (𝕜 := ℂ) i).compLpL 2 (coulombMeasure N β))

theorem coulombCutoffAdjointErrorL_coe {N : ℕ} (β : ℝ) {R : ℝ} (hR : 0 < R)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    coulombCutoffAdjointErrorL β hR u =ᵐ[coulombMeasure N β]
      fun z => inner ℂ (dbarCoreVector (coulombMetricCutoffSymbolCore hR) z) (u z) := by
  let F := fun i => coulombCoreMultiplierL2L β
      (TestFunction.postcompCLM Complex.conjCLE.toContinuousLinearMap (coulombMetricCutoffSymbolCore hR i))
      ((EuclideanSpace.proj (𝕜 := ℂ) i).compLpL 2 (coulombMeasure N β) u)
  have hF (i : Fin N) : F i =ᵐ[coulombMeasure N β]
      fun z => conj (coulombMetricCutoffSymbolCore hR i z) * u z i := by
    filter_upwards [coulombCoreMultiplierL2L_coe β
        (TestFunction.postcompCLM Complex.conjCLE.toContinuousLinearMap (coulombMetricCutoffSymbolCore hR i))
        ((EuclideanSpace.proj (𝕜 := ℂ) i).compLpL 2 (coulombMeasure N β) u),
      (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL (p := 2) (μ := coulombMeasure N β) u]
      with z hM hu
    change (F i) z = _
    rw [hM, hu]
    rfl
  have hsum : coulombCutoffAdjointErrorL β hR u = ∑ i, F i := by
    simp only [coulombCutoffAdjointErrorL, _root_.sum_apply, ContinuousLinearMap.comp_apply, F]
  rw [hsum]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ F, ae_all_iff.mpr hF] with z hs hFz
  rw [hs, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dbarCoreVector, WithLp.ofLp_toLp, dotProduct, Pi.star_apply, Complex.star_def]
  exact Finset.sum_congr rfl (fun i _ => (hFz i).trans (mul_comm _ _))

theorem coulombCutoffAdjointErrorL_norm_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ} {β : ℝ}, 0 < β → ∀ {R : ℝ} (hR : 0 < R)
      (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)),
      ‖coulombCutoffAdjointErrorL β hR u‖ ≤ (C / (2 * R)) * ‖u‖ := by
  obtain ⟨C, hC, hsymbol⟩ := coulombMetricCutoff_transformed_dbar_bound
  refine ⟨C, hC, ?_⟩
  intro N β hβ R hR u
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coulombCutoffAdjointErrorL_coe β hR u,
    (coulombMeasure_ae_iff hβ).mpr (coulombDomain_ae N)] with z hz hΩ
  rw [hz, coulombMetricCutoffSymbolCore_vector]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hsymbol hR z hΩ) (norm_nonneg _))

theorem coulombCutoffAdjointErrorL_tendsto_zero {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    Tendsto (fun n : ℕ => coulombCutoffAdjointErrorL β (by positivity : 0 < (n : ℝ) + 1) u)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := coulombCutoffAdjointErrorL_norm_bound
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
