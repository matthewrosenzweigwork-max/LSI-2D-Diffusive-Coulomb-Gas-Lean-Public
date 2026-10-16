module

public import LeanResearch.RepulsiveCoulomb.CoulombJetPermutation

@[expose] public section

/-! Label permutations act on the full original closed form, preserving physical energy. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

def coulombFormPermuteL (N : ℕ) {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N)) :
    CoulombFormDomain N hβ →L[ℝ] CoulombFormDomain N hβ :=
  ((coulombJetPermuteL N hβ σ).comp (coulombFormSubmodule N hβ).toSubmodule.subtypeL).codRestrict
    (coulombFormSubmodule N hβ).toSubmodule (fun u => by
      change coulombJetPermuteL N hβ σ (u : CoulombJetL2 N β) ∈ (coulombFormSubmodule N hβ : Set _)
      rw [coe_coulombFormSubmodule]
      apply coulombJetPermuteL_preserves_graph N hβ σ
      rw [← coe_coulombFormSubmodule]
      exact u.property)

theorem coulombFormPermuteL_coe (N : ℕ) {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N))
    (u : CoulombFormDomain N hβ) :
    (coulombFormPermuteL N hβ σ u : CoulombJetL2 N β) =
      coulombJetPermuteL N hβ σ (u : CoulombJetL2 N β) := rfl

theorem coulombFormPermuteL_core {N : ℕ} {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N))
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombFormPermuteL N hβ σ (coulombFormCore hβ φ) = coulombFormCore hβ (coulombPermuteCore σ φ) := by
  apply Subtype.ext
  exact coulombJetPermuteL_core hβ σ φ

theorem coulombFormPermuteL_value (N : ℕ) {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N))
    (u : CoulombFormDomain N hβ) :
    coulombFormValueL N hβ (coulombFormPermuteL N hβ σ u) =
      coulombValuePermuteL N hβ σ (coulombFormValueL N hβ u) := by
  have hp := (coulombPermute_gibbs_preserving hβ.le σ).quasiMeasurePreserving.ae
    (coulombJetValueL_coe N β (u : CoulombJetL2 N β))
  apply Lp.ext
  filter_upwards [coulombJetValueL_coe N β (coulombJetPermuteL N hβ σ (u : CoulombJetL2 N β)),
    coulombJetPermuteL_coe N hβ σ (u : CoulombJetL2 N β),
    coulombValuePermuteL_coe N hβ σ (coulombFormValueL N hβ u), hp] with z hv ht hu hp
  change coulombJetValueL N β (coulombJetPermuteL N hβ σ (u : CoulombJetL2 N β)) z = _
  rw [hv, ht, coulombJetFiberPermute_apply, WithLp.toLp_fst, hu]
  exact hp.symm

theorem coulombFormPermuteL_gradient (N : ℕ) {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N))
    (u : CoulombFormDomain N hβ) :
    coulombFormGradientL N hβ (coulombFormPermuteL N hβ σ u) =ᵐ[coulombMeasure N β] fun z =>
      (coulombPermute σ).symm (coulombFormGradientL N hβ u (coulombPermute σ z)) := by
  have hp := (coulombPermute_gibbs_preserving hβ.le σ).quasiMeasurePreserving.ae
    (coulombJetGradientL_coe N β (u : CoulombJetL2 N β))
  filter_upwards [coulombJetGradientL_coe N β (coulombJetPermuteL N hβ σ (u : CoulombJetL2 N β)),
    coulombJetPermuteL_coe N hβ σ (u : CoulombJetL2 N β), hp] with z hg ht hp
  change coulombJetGradientL N β (coulombJetPermuteL N hβ σ (u : CoulombJetL2 N β)) z = _
  rw [hg, ht, coulombJetFiberPermute_apply, WithLp.toLp_snd]
  exact congrArg (coulombPermute σ).symm hp.symm

theorem coulombFormPermuteL_norm (N : ℕ) {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N))
    (u : CoulombFormDomain N hβ) :
    ‖coulombFormPermuteL N hβ σ u‖ = ‖u‖ :=
  coulombJetPermuteL_norm N hβ σ (u : CoulombJetL2 N β)

theorem coulombFormPermuteL_energy (N : ℕ) {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N))
    (u : CoulombFormDomain N hβ) :
    coulombFormEnergy N hβ (coulombFormPermuteL N hβ σ u) = coulombFormEnergy N hβ u := by
  have hv : ‖coulombFormValueL N hβ (coulombFormPermuteL N hβ σ u)‖ =
      ‖coulombFormValueL N hβ u‖ := by
    rw [coulombFormPermuteL_value]
    exact Lp.norm_compMeasurePreserving (coulombFormValueL N hβ u)
      (coulombPermute_gibbs_preserving hβ.le σ)
  have ht := coulombForm_norm_sq N hβ (coulombFormPermuteL N hβ σ u)
  have hu := coulombForm_norm_sq N hβ u
  rw [coulombFormPermuteL_norm, hv] at ht
  linarith

theorem coulombFormPermuteL_gradient_norm (N : ℕ) {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N))
    (u : CoulombFormDomain N hβ) :
    ‖coulombFormGradientL N hβ (coulombFormPermuteL N hβ σ u)‖ = ‖coulombFormGradientL N hβ u‖ := by
  have h := coulombFormPermuteL_energy N hβ σ u
  unfold coulombFormEnergy at h
  nlinarith [norm_nonneg (coulombFormGradientL N hβ (coulombFormPermuteL N hβ σ u)),
    norm_nonneg (coulombFormGradientL N hβ u)]

end RepulsiveCoulomb

