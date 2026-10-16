module

public import LeanResearch.RepulsiveCoulomb.PointWeightFormCore

@[expose] public section

/-! Local weak-derivative identification of the weighted smooth-core graph.
A continuous restriction into Lebesgue L2 is constructed before the closed
Haar Sobolev subspace is used. No weighted-to-Haar substitution is made.
This implements the local test-field step of manuscript Proposition 2.1.
-/
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology
namespace RepulsiveCoulomb

/-- Closure in the physical value-gradient L2 norm. Its injective realization
as a space of functions is a conclusion of closability, not part of this definition. -/
def pointCoreGraph {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) : Set (PointJetL2 γ a y) :=
  closure (Set.range (pointCoreJet hγ ha y))

theorem pointCoreJet_local_mem_w1p {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {K : Set ℂ} (hK : IsCompact K) (havoid : K ⊆ (pointPunctures a y)ᶜ)
    (U : Opens ℂ) (hUK : (U : Set ℂ) ⊆ K)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    pointL2RestrictToVolume hγ ha y hK havoid hUK (TauCeti.Sobolev1Jet ℂ)
      (pointCoreJet hγ ha y φ) ∈ TauCeti.w1pSubmodule volume U 2 := by
  let T : PointJetL2 γ a y →L[ℝ] TauCeti.Sobolev1JetLp volume U 2 :=
    pointL2RestrictToVolume hγ ha y hK havoid hUK (TauCeti.Sobolev1Jet ℂ)
  have hT := pointL2RestrictToVolume_coe hγ ha y hK havoid hUK (pointCoreJet hγ ha y φ)
  have hφ := ae_restrict_of_ae (s := (U : Set ℂ)) ((pointMeasure_ae_iff hγ ha y).mp (pointCoreJet_coe hγ ha y φ))
  have hv : TauCeti.Sobolev1JetLp.value (T (pointCoreJet hγ ha y φ)) =ᵐ[volume.restrict U] φ := by
    filter_upwards [TauCeti.Sobolev1JetLp.value_apply_ae (T (pointCoreJet hγ ha y φ)), hT, hφ]
      with z hv hz hφz
    simpa only [T, hz, hφz, WithLp.toLp_fst] using hv
  have hg : TauCeti.Sobolev1JetLp.candidateWeakFDeriv (T (pointCoreJet hγ ha y φ))
      =ᵐ[volume.restrict U] (fun z ↦ innerSL ℝ (gradient (φ : ℂ → ℝ) z)) := by
    filter_upwards [TauCeti.Sobolev1JetLp.gradient_apply_ae (T (pointCoreJet hγ ha y φ)), hT, hφ]
      with z hg hz hφz
    ext v
    rw [TauCeti.Sobolev1JetLp.candidateWeakFDeriv_apply, hg]
    simp only [T, hz, hφz, WithLp.toLp_snd, innerSL_apply_apply, real_inner_comm]
  apply (TauCeti.mem_w1pSubmodule_iff_hasWeakFDerivOn _).mpr
  have hw := (TauCeti.hasWeakFDerivOn_testFunction (μ := volume) φ).mono
    (show U ≤ pointDomain a y from hUK.trans havoid)
  exact (hw.congr_ae hv.symm).congr_ae_deriv hg.symm

/-- Closedness is used only after actual local conversion to Lebesgue measure. -/
theorem pointCoreGraph_local_mem_w1p {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {K : Set ℂ} (hK : IsCompact K) (havoid : K ⊆ (pointPunctures a y)ᶜ)
    (U : Opens ℂ) (hUK : (U : Set ℂ) ⊆ K)
    {J : PointJetL2 γ a y} (hJ : J ∈ pointCoreGraph hγ ha y) :
    pointL2RestrictToVolume hγ ha y hK havoid hUK (TauCeti.Sobolev1Jet ℂ) J
      ∈ TauCeti.w1pSubmodule volume U 2 := by
  let T : PointJetL2 γ a y →L[ℝ] TauCeti.Sobolev1JetLp volume U 2 :=
    pointL2RestrictToVolume hγ ha y hK havoid hUK (TauCeti.Sobolev1Jet ℂ)
  have hclosed : IsClosed (T ⁻¹' (TauCeti.w1pSubmodule volume U 2 : Set _)) :=
    (TauCeti.w1pSubmodule volume U 2).isClosed.preimage T.continuous
  apply closure_minimal _ hclosed hJ
  rintro _ ⟨φ, rfl⟩
  exact pointCoreJet_local_mem_w1p hγ ha y hK havoid U hUK φ

/-- A zero value in the weighted graph has zero physical gradient on each
relatively compact open subset of the punctured plane. -/
theorem pointCoreGraph_zero_gradient_local {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {K : Set ℂ} (hK : IsCompact K) (havoid : K ⊆ (pointPunctures a y)ᶜ)
    (U : Opens ℂ) (hUK : (U : Set ℂ) ⊆ K)
    {J : PointJetL2 γ a y} (hJ : J ∈ pointCoreGraph hγ ha y)
    (hv : ∀ᵐ z ∂pointMeasure γ a y, WithLp.fst (J z) = 0) :
    ∀ᵐ z ∂volume.restrict U, WithLp.snd (J z) = 0 := by
  let T : PointJetL2 γ a y →L[ℝ] TauCeti.Sobolev1JetLp volume U 2 :=
    pointL2RestrictToVolume hγ ha y hK havoid hUK (TauCeti.Sobolev1Jet ℂ)
  let u : TauCeti.W1p volume U 2 :=
    ⟨T J, pointCoreGraph_local_mem_w1p hγ ha y hK havoid U hUK hJ⟩
  have hT := pointL2RestrictToVolume_coe hγ ha y hK havoid hUK J
  have hv' := ae_restrict_of_ae (s := (U : Set ℂ)) ((pointMeasure_ae_iff hγ ha y).mp hv)
  have hu : ∀ᵐ z ∂volume.restrict U, TauCeti.W1p.value u z = 0 := by
    filter_upwards [TauCeti.W1p.value_apply_ae u, hT, hv'] with z hu hz hvz
    exact hu.trans (by simpa only [u, T, hz] using hvz)
  have hg := TauCeti.W1p.gradient_ae_eq_zero_of_value_ae_eq_zero (u := u) le_rfl hu
  filter_upwards [hg, TauCeti.W1p.gradient_apply_ae u, hT] with z hg hgrad hz
  exact (by simpa only [u, T, hz] using hgrad.symm.trans hg)

end RepulsiveCoulomb
