import LeanResearch.RepulsiveCoulomb.CoulombFormCore

/-! Local Haar weak-derivative identification after the proved weighted L2
restriction. The weighted law is not used as a Haar measure. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology ENNReal
namespace RepulsiveCoulomb

def coulombCoreGraph (N : ℕ) {β : ℝ} (hβ : 0 < β) : Set (CoulombJetL2 N β) :=
  closure (Set.range (coulombCoreJet (N := N) hβ))

theorem coulombCoreJet_local_mem_w1p {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (havoid : K ⊆ coulombDomain N)
    (U : Opens (CoulombConfig N)) (hUK : (U : Set (CoulombConfig N)) ⊆ K)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombL2RestrictToVolume hβ hK havoid hUK (TauCeti.Sobolev1Jet (CoulombConfig N))
      (coulombCoreJet hβ φ) ∈ TauCeti.w1pSubmodule volume U 2 := by
  let T : CoulombJetL2 N β →L[ℝ] TauCeti.Sobolev1JetLp volume U 2 :=
    coulombL2RestrictToVolume hβ hK havoid hUK (TauCeti.Sobolev1Jet (CoulombConfig N))
  have hT := coulombL2RestrictToVolume_coe hβ hK havoid hUK (coulombCoreJet hβ φ)
  have hφ := ae_restrict_of_ae (s := (U : Set (CoulombConfig N))) ((coulombMeasure_ae_iff hβ).mp (coulombCoreJet_coe hβ φ))
  have hv : TauCeti.Sobolev1JetLp.value (T (coulombCoreJet hβ φ)) =ᵐ[volume.restrict U] φ := by
    filter_upwards [TauCeti.Sobolev1JetLp.value_apply_ae (T (coulombCoreJet hβ φ)), hT, hφ] with z hv hz hφz
    simpa only [T, hz, hφz, WithLp.toLp_fst] using hv
  have hg : TauCeti.Sobolev1JetLp.candidateWeakFDeriv (T (coulombCoreJet hβ φ))
      =ᵐ[volume.restrict U] fun z => innerSL ℝ (gradient (φ : CoulombConfig N → ℝ) z) := by
    filter_upwards [TauCeti.Sobolev1JetLp.gradient_apply_ae (T (coulombCoreJet hβ φ)), hT, hφ] with z hg hz hφz
    ext v
    rw [TauCeti.Sobolev1JetLp.candidateWeakFDeriv_apply, hg]
    simp only [T, hz, hφz, WithLp.toLp_snd, innerSL_apply_apply, real_inner_comm]
  apply (TauCeti.mem_w1pSubmodule_iff_hasWeakFDerivOn _).mpr
  have hw := (TauCeti.hasWeakFDerivOn_testFunction (μ := volume) φ).mono
    (show U ≤ coulombDomain N from hUK.trans havoid)
  exact (hw.congr_ae hv.symm).congr_ae_deriv hg.symm

set_option maxHeartbeats 800000 in
theorem coulombCoreGraph_local_mem_w1p {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (havoid : K ⊆ coulombDomain N)
    (U : Opens (CoulombConfig N)) (hUK : (U : Set (CoulombConfig N)) ⊆ K)
    {J : CoulombJetL2 N β} (hJ : J ∈ coulombCoreGraph N hβ) :
    coulombL2RestrictToVolume hβ hK havoid hUK (TauCeti.Sobolev1Jet (CoulombConfig N)) J
      ∈ TauCeti.w1pSubmodule volume U 2 := by
  let T : CoulombJetL2 N β →L[ℝ] TauCeti.Sobolev1JetLp volume U 2 :=
    coulombL2RestrictToVolume hβ hK havoid hUK (TauCeti.Sobolev1Jet (CoulombConfig N))
  have hclosed : IsClosed (T ⁻¹' (TauCeti.w1pSubmodule volume U 2 : Set _)) :=
    (TauCeti.w1pSubmodule volume U 2).isClosed.preimage T.continuous
  apply closure_minimal _ hclosed hJ
  rintro _ ⟨φ, rfl⟩
  exact coulombCoreJet_local_mem_w1p hβ hK havoid U hUK φ

theorem coulombCoreGraph_zero_gradient_local {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (havoid : K ⊆ coulombDomain N)
    (U : Opens (CoulombConfig N)) (hUK : (U : Set (CoulombConfig N)) ⊆ K)
    {J : CoulombJetL2 N β} (hJ : J ∈ coulombCoreGraph N hβ)
    (hv : ∀ᵐ z ∂coulombMeasure N β, WithLp.fst (J z) = 0) :
    ∀ᵐ z ∂volume.restrict U, WithLp.snd (J z) = 0 := by
  let T : CoulombJetL2 N β →L[ℝ] TauCeti.Sobolev1JetLp volume U 2 :=
    coulombL2RestrictToVolume hβ hK havoid hUK (TauCeti.Sobolev1Jet (CoulombConfig N))
  let u : TauCeti.W1p volume U 2 := ⟨T J, coulombCoreGraph_local_mem_w1p hβ hK havoid U hUK hJ⟩
  have hT := coulombL2RestrictToVolume_coe hβ hK havoid hUK J
  have hv' := ae_restrict_of_ae (s := (U : Set (CoulombConfig N))) ((coulombMeasure_ae_iff hβ).mp hv)
  have hu : ∀ᵐ z ∂volume.restrict U, TauCeti.W1p.value u z = 0 := by
    filter_upwards [TauCeti.W1p.value_apply_ae u, hT, hv'] with z hu hz hvz
    exact hu.trans (by simpa only [u, T, hz] using hvz)
  have hg := TauCeti.W1p.gradient_ae_eq_zero_of_value_ae_eq_zero (u := u) le_rfl hu
  filter_upwards [hg, TauCeti.W1p.gradient_apply_ae u, hT] with z hg hgrad hz
  exact (by simpa only [u, T, hz] using hgrad.symm.trans hg)

end RepulsiveCoulomb
