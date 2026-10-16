import LeanResearch.RepulsiveCoulomb.CoulombPermutation
import LeanResearch.RepulsiveCoulomb.CoulombCoreSlice

noncomputable section
open Set MeasureTheory InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

theorem gradient_comp_linearIsometryEquiv {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (e : E ≃ₗᵢ[ℝ] F) {f : F → ℝ} (x : E) (hf : DifferentiableAt ℝ f (e x)) :
    gradient (fun z => f (e z)) x = e.symm (gradient f (e x)) := by
  have h := hf.hasFDerivAt.comp x e.toContinuousLinearEquiv.hasFDerivAt
  apply (toDual ℝ E).injective
  simp only [toDual_gradient]
  change fderiv ℝ (f ∘ e) x = _
  rw [h.fderiv]
  ext v
  change fderiv ℝ f (e x) (e v) = inner ℝ (e.symm (gradient f (e x))) v
  rw [← inner_gradient_left]
  have hi := e.inner_map_map (e.symm (gradient f (e x))) v
  rw [e.apply_symm_apply] at hi
  exact hi

theorem coulombPermute_symm_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (z : CoulombConfig N) (i : Fin N) :
    (coulombPermute σ).symm z i = z (σ.symm i) := by
  rw [coulombPermute, LinearIsometryEquiv.piLpCongrLeft_symm]
  rfl

def coulombPermuteCore {N : ℕ} (σ : Equiv.Perm (Fin N))
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    TestFunction (coulombDomain N) ℝ ⊤ :=
  ⟨fun z => φ (coulombPermute σ z),
    φ.contDiff.comp (coulombPermute σ).toContinuousLinearEquiv.contDiff,
    φ.hasCompactSupport.comp_isClosedEmbedding (coulombPermute σ).isometry.isClosedEmbedding,
    fun z hz => (coulombPermute_mem_domain σ z).mp
      (φ.tsupport_subset (tsupport_comp_subset_preimage (φ : CoulombConfig N → ℝ)
        (coulombPermute σ).continuous hz))⟩

theorem coulombPermuteCore_apply {N : ℕ} (σ : Equiv.Perm (Fin N))
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (z : CoulombConfig N) :
    coulombPermuteCore σ φ z = φ (coulombPermute σ z) := rfl

theorem coulombPermuteCore_gradient {N : ℕ} (σ : Equiv.Perm (Fin N))
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (z : CoulombConfig N) :
    gradient (coulombPermuteCore σ φ : CoulombConfig N → ℝ) z =
      (coulombPermute σ).symm (gradient (φ : CoulombConfig N → ℝ) (coulombPermute σ z)) :=
  gradient_comp_linearIsometryEquiv (coulombPermute σ) z (φ.contDiff.differentiable (by simp) _)

theorem coulombPermuteCore_gradient_component {N : ℕ} (σ : Equiv.Perm (Fin N))
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (z : CoulombConfig N) (i : Fin N) :
    gradient (coulombPermuteCore σ φ : CoulombConfig N → ℝ) z i =
      gradient (φ : CoulombConfig N → ℝ) (coulombPermute σ z) (σ.symm i) := by
  rw [coulombPermuteCore_gradient, coulombPermute_symm_apply]

end RepulsiveCoulomb

