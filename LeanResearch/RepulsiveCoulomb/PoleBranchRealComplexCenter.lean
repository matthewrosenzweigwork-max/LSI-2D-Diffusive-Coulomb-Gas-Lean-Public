import LeanResearch.RepulsiveCoulomb.PoleBranchWeakProjectionSymmetry
import LeanResearch.RepulsiveCoulomb.PoleBranchRealLpMean

/-! Real L2 centering inside the literal complex Gibbs L2 space. These lemmas
use the existing scalar postcomposition operation, not a second form-domain
embedding or a form-domain dilation/regularity assumption. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace ProbabilityTheory
namespace RepulsiveCoulomb

theorem poleBranch_ofRealLp_norm {N : ℕ} {β : ℝ}
    (v : Lp ℝ 2 (coulombMeasure N β)) :
    ‖Complex.ofRealCLM.compLpL 2 (coulombMeasure N β) v‖ = ‖v‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable v)
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL v] with z hz
  rw [hz]
  exact Complex.ofRealLI.norm_map (v z)

theorem poleBranch_ofRealLp_conjugate {N : ℕ} {β : ℝ}
    (v : Lp ℝ 2 (coulombMeasure N β)) :
    poleBranchComplexConj N β (Complex.ofRealCLM.compLpL 2 (coulombMeasure N β) v) =
      Complex.ofRealCLM.compLpL 2 (coulombMeasure N β) v := by
  apply Lp.ext
  filter_upwards [poleBranchComplexConj_coe (Complex.ofRealCLM.compLpL 2 (coulombMeasure N β) v),
    Complex.ofRealCLM.coeFn_compLpL v] with z hc hv
  simp only [hc, hv, Complex.ofRealCLM_apply, Complex.star_def, Complex.conj_ofReal]

theorem poleBranch_ofRealLp_permute {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (σ : Equiv.Perm (Fin N)) (v : Lp ℝ 2 (coulombMeasure N β)) :
    poleBranchComplexPermute N hβ σ (Complex.ofRealCLM.compLpL 2 (coulombMeasure N β) v) =
      Complex.ofRealCLM.compLpL 2 (coulombMeasure N β) (coulombValuePermuteL N hβ σ v) := by
  have ht := (coulombPermute_gibbs_preserving hβ.le σ).quasiMeasurePreserving.ae
    (Complex.ofRealCLM.coeFn_compLpL (p := 2) (μ := coulombMeasure N β) v)
  apply Lp.ext
  filter_upwards [poleBranchComplexPermute_coe hβ σ (Complex.ofRealCLM.compLpL 2 (coulombMeasure N β) v),
    ht, Complex.ofRealCLM.coeFn_compLpL (coulombValuePermuteL N hβ σ v),
    coulombValuePermuteL_coe N hβ σ v] with z hp ht he hv
  rw [hp, ht, he, hv]

theorem poleBranch_ofRealLp_mean {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure N β)) :
    poleBranchComplexMean N hβ (Complex.ofRealCLM.compLpL 2 (coulombMeasure N β) v) =
      (poleBranchRealMean N hβ v : ℂ) := by
  rw [poleBranchComplexMean_eq_integral, poleBranchRealMean_eq_integral]
  calc
    _ = ∫ z, (v z : ℂ) ∂coulombMeasure N β :=
      integral_congr_ae (Complex.ofRealCLM.coeFn_compLpL v)
    _ = _ := integral_complex_ofReal

theorem poleBranch_ofRealLp_center {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure N β)) :
    Complex.ofRealCLM.compLpL 2 (coulombMeasure N β) (poleBranchRealCenter N hβ v) =
      Complex.ofRealCLM.compLpL 2 (coulombMeasure N β) v -
        (poleBranchRealMean N hβ v : ℂ) • poleBranchComplexOne N hβ := by
  apply Lp.ext
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (poleBranchRealCenter N hβ v),
    poleBranchRealCenter_coe hβ v, Complex.ofRealCLM.coeFn_compLpL v,
    Lp.coeFn_sub (Complex.ofRealCLM.compLpL 2 (coulombMeasure N β) v)
      ((poleBranchRealMean N hβ v : ℂ) • poleBranchComplexOne N hβ),
    Lp.coeFn_smul (poleBranchRealMean N hβ v : ℂ) (poleBranchComplexOne N hβ),
    poleBranchComplexOne_coe N hβ] with z he hc hv hs hm h1
  simp only [he, Complex.ofRealCLM_apply, hc, Complex.ofReal_sub, hs, Pi.sub_apply,
    hv, hm, Pi.smul_apply, h1, smul_eq_mul, mul_one]

theorem poleBranch_ofRealLp_center_mean {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure N β)) :
    poleBranchComplexMean N hβ
      (Complex.ofRealCLM.compLpL 2 (coulombMeasure N β) (poleBranchRealCenter N hβ v)) = 0 := by
  rw [poleBranch_ofRealLp_mean, poleBranchRealCenter_mean, Complex.ofReal_zero]

theorem poleBranch_ofRealLp_center_norm_sq {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure N β)) :
    ‖Complex.ofRealCLM.compLpL 2 (coulombMeasure N β) (poleBranchRealCenter N hβ v)‖ ^ 2 =
      variance (v : CoulombConfig N → ℝ) (coulombMeasure N β) := by
  rw [poleBranch_ofRealLp_norm, poleBranchRealCenter_norm_sq]

end RepulsiveCoulomb
