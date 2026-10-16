import LeanResearch.RepulsiveCoulomb.CoulombFormSymmetrizer

/-! Literal real Gibbs L2 constants, continuous mean and variance, and centering.
All particle numbers are retained; these statements do not use a dbar estimate
or holomorphic-kernel regularity. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace ProbabilityTheory
open scoped Topology
namespace RepulsiveCoulomb

def poleBranchRealOne (N : ℕ) {β : ℝ} (hβ : 0 < β) : Lp ℝ 2 (coulombMeasure N β) := by
  letI := coulombMeasure_isProbability (N := N) hβ
  exact (memLp_const (1 : ℝ)).toLp (fun _ => 1)

theorem poleBranchRealOne_coe (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    poleBranchRealOne N hβ =ᵐ[coulombMeasure N β] fun _ => (1 : ℝ) := by
  letI := coulombMeasure_isProbability (N := N) hβ
  exact MemLp.coeFn_toLp (memLp_const (1 : ℝ))

def poleBranchRealMean (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Lp ℝ 2 (coulombMeasure N β) →L[ℝ] ℝ := innerSL ℝ (poleBranchRealOne N hβ)

theorem poleBranchRealMean_eq_integral {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure N β)) :
    poleBranchRealMean N hβ v = ∫ z, v z ∂coulombMeasure N β := by
  change inner ℝ (poleBranchRealOne N hβ) v = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [poleBranchRealOne_coe N hβ] with z hz
  simp [hz]

theorem poleBranchRealMean_one (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    poleBranchRealMean N hβ (poleBranchRealOne N hβ) = 1 := by
  letI := coulombMeasure_isProbability (N := N) hβ
  rw [poleBranchRealMean_eq_integral]
  calc
    _ = ∫ _z : CoulombConfig N, (1 : ℝ) ∂coulombMeasure N β :=
      integral_congr_ae (poleBranchRealOne_coe N hβ)
    _ = _ := by simp

theorem poleBranchRealOne_permute {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (σ : Equiv.Perm (Fin N)) :
    coulombValuePermuteL N hβ σ (poleBranchRealOne N hβ) = poleBranchRealOne N hβ := by
  have ht := (coulombPermute_gibbs_preserving hβ.le σ).quasiMeasurePreserving.ae
    (poleBranchRealOne_coe N hβ)
  apply Lp.ext
  filter_upwards [coulombValuePermuteL_coe N hβ σ (poleBranchRealOne N hβ),
    ht, poleBranchRealOne_coe N hβ] with z hp ht h1
  rw [hp, ht, h1]

theorem poleBranchRealLp_norm_sq_eq_integral {N : ℕ} {β : ℝ}
    (v : Lp ℝ 2 (coulombMeasure N β)) :
    ‖v‖ ^ 2 = ∫ z, (v z) ^ 2 ∂coulombMeasure N β := by
  rw [← real_inner_self_eq_norm_sq v, L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by simp [pow_two]

theorem poleBranchRealLp_variance_eq_norm_mean {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure N β)) :
    variance (v : CoulombConfig N → ℝ) (coulombMeasure N β) =
      ‖v‖ ^ 2 - (poleBranchRealMean N hβ v) ^ 2 := by
  letI := coulombMeasure_isProbability (N := N) hβ
  rw [variance_eq_sub (Lp.memLp v)]
  change (∫ z, (v z) ^ 2 ∂coulombMeasure N β) -
    (∫ z, v z ∂coulombMeasure N β) ^ 2 = _
  rw [← poleBranchRealLp_norm_sq_eq_integral, ← poleBranchRealMean_eq_integral]

theorem poleBranchRealLp_variance_continuous {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    Continuous (fun v : Lp ℝ 2 (coulombMeasure N β) =>
      variance (v : CoulombConfig N → ℝ) (coulombMeasure N β)) := by
  simp_rw [poleBranchRealLp_variance_eq_norm_mean hβ]
  exact (continuous_norm.pow 2).sub ((poleBranchRealMean N hβ).continuous.pow 2)

def poleBranchRealCenter (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure N β)) : Lp ℝ 2 (coulombMeasure N β) :=
  v - poleBranchRealMean N hβ v • poleBranchRealOne N hβ

theorem poleBranchRealCenter_coe {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure N β)) :
    poleBranchRealCenter N hβ v =ᵐ[coulombMeasure N β]
      fun z => v z - poleBranchRealMean N hβ v := by
  filter_upwards [Lp.coeFn_sub v (poleBranchRealMean N hβ v • poleBranchRealOne N hβ),
    Lp.coeFn_smul (poleBranchRealMean N hβ v) (poleBranchRealOne N hβ),
    poleBranchRealOne_coe N hβ] with z hsub hsm h1
  change (v - poleBranchRealMean N hβ v • poleBranchRealOne N hβ) z = _
  simp only [hsub, Pi.sub_apply, hsm, Pi.smul_apply, h1, smul_eq_mul, mul_one]

theorem poleBranchRealCenter_mean {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure N β)) :
    poleBranchRealMean N hβ (poleBranchRealCenter N hβ v) = 0 := by
  simp only [poleBranchRealCenter, map_sub, map_smul, poleBranchRealMean_one,
    smul_eq_mul, mul_one, sub_self]

theorem poleBranchRealCenter_norm_sq {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure N β)) :
    ‖poleBranchRealCenter N hβ v‖ ^ 2 =
      variance (v : CoulombConfig N → ℝ) (coulombMeasure N β) := by
  letI := coulombMeasure_isProbability (N := N) hβ
  rw [poleBranchRealLp_norm_sq_eq_integral,
    variance_eq_integral (Lp.aestronglyMeasurable v).aemeasurable]
  apply integral_congr_ae
  filter_upwards [poleBranchRealCenter_coe hβ v] with z hz
  rw [hz, poleBranchRealMean_eq_integral]

theorem poleBranchRealCenter_permute {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Lp ℝ 2 (coulombMeasure N β))
    (hsym : ∀ σ : Equiv.Perm (Fin N), coulombValuePermuteL N hβ σ v = v) :
    ∀ σ : Equiv.Perm (Fin N),
      coulombValuePermuteL N hβ σ (poleBranchRealCenter N hβ v) = poleBranchRealCenter N hβ v := by
  intro σ
  rw [poleBranchRealCenter, map_sub, map_smul, hsym σ, poleBranchRealOne_permute]

end RepulsiveCoulomb
