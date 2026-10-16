module

public import LeanResearch.RepulsiveCoulomb.CoulombValueRepresentation

@[expose] public section

/-! Actual value/physical-gradient jet transport by label permutations. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

def coulombJetFiberPermute {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    TauCeti.Sobolev1Jet (CoulombConfig N) ≃ₗᵢ[ℝ] TauCeti.Sobolev1Jet (CoulombConfig N) :=
  LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ ℝ) (coulombPermute σ).symm

theorem coulombJetFiberPermute_apply {N : ℕ} (σ : Equiv.Perm (Fin N))
    (q : TauCeti.Sobolev1Jet (CoulombConfig N)) :
    coulombJetFiberPermute σ q = WithLp.toLp 2 (WithLp.fst q, (coulombPermute σ).symm (WithLp.snd q)) := rfl

def coulombJetPermuteL (N : ℕ) {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N)) :
    CoulombJetL2 N β →L[ℝ] CoulombJetL2 N β :=
  ((coulombJetFiberPermute σ).toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 (coulombMeasure N β)).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (coulombPermute σ)
      (coulombPermute_gibbs_preserving hβ.le σ)).toContinuousLinearMap

theorem coulombJetPermuteL_coe (N : ℕ) {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N))
    (J : CoulombJetL2 N β) :
    coulombJetPermuteL N hβ σ J =ᵐ[coulombMeasure N β] fun z =>
      coulombJetFiberPermute σ (J (coulombPermute σ z)) := by
  let T : CoulombJetL2 N β →ₗᵢ[ℝ] CoulombJetL2 N β := Lp.compMeasurePreservingₗᵢ ℝ (coulombPermute σ) (coulombPermute_gibbs_preserving hβ.le σ)
  filter_upwards [(coulombJetFiberPermute σ).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL (T J),
    Lp.coeFn_compMeasurePreserving J (coulombPermute_gibbs_preserving hβ.le σ)] with z hm ht
  change ((coulombJetFiberPermute σ).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
    2 (coulombMeasure N β) (T J)) z = _
  rw [hm]
  change coulombJetFiberPermute σ (T J z) = _
  change T J z = J (coulombPermute σ z) at ht
  rw [ht]

theorem coulombJetPermuteL_core {N : ℕ} {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N))
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombJetPermuteL N hβ σ (coulombCoreJet hβ φ) = coulombCoreJet hβ (coulombPermuteCore σ φ) := by
  have hp := (coulombPermute_gibbs_preserving hβ.le σ).quasiMeasurePreserving.ae (coulombCoreJet_coe hβ φ)
  apply Lp.ext
  filter_upwards [coulombJetPermuteL_coe N hβ σ (coulombCoreJet hβ φ),
    hp, coulombCoreJet_coe hβ (coulombPermuteCore σ φ)] with z ht hc hpφ
  rw [ht, hc, hpφ, coulombJetFiberPermute_apply]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, coulombPermuteCore_apply, coulombPermuteCore_gradient]

theorem coulombJetPermuteL_preserves_graph (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (σ : Equiv.Perm (Fin N)) {J : CoulombJetL2 N β} (hJ : J ∈ coulombCoreGraph N hβ) :
    coulombJetPermuteL N hβ σ J ∈ coulombCoreGraph N hβ := by
  have hc : IsClosed ((coulombJetPermuteL N hβ σ) ⁻¹' coulombCoreGraph N hβ) :=
    isClosed_closure.preimage (coulombJetPermuteL N hβ σ).continuous
  apply closure_minimal ?_ hc hJ
  rintro K ⟨φ, rfl⟩
  change coulombJetPermuteL N hβ σ (coulombCoreJet hβ φ) ∈ coulombCoreGraph N hβ
  rw [coulombJetPermuteL_core]
  exact subset_closure (mem_range_self _)

theorem coulombJetPermuteL_norm (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (σ : Equiv.Perm (Fin N)) (J : CoulombJetL2 N β) :
    ‖coulombJetPermuteL N hβ σ J‖ = ‖J‖ := by
  have he : ‖coulombJetPermuteL N hβ σ J‖ ^ 2 = ‖J‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (coulombJetPermuteL N hβ σ J), L2.inner_def,
      ← real_inner_self_eq_norm_sq J, L2.inner_def]
    calc
      _ = ∫ z, inner ℝ (J (coulombPermute σ z)) (J (coulombPermute σ z)) ∂coulombMeasure N β := by
        apply integral_congr_ae
        filter_upwards [coulombJetPermuteL_coe N hβ σ J] with z hz
        rw [hz, (coulombJetFiberPermute σ).inner_map_map]
      _ = _ := (coulombPermute_gibbs_preserving hβ.le σ).integral_comp
        (coulombPermute σ).toMeasurableEquiv.measurableEmbedding (fun z => inner ℝ (J z) (J z))
  nlinarith [norm_nonneg (coulombJetPermuteL N hβ σ J), norm_nonneg J]

end RepulsiveCoulomb

