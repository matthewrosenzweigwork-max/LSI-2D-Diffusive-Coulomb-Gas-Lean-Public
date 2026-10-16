import LeanResearch.RepulsiveCoulomb.DbarBranchComplexGraph

/-! The actual weak kernel is a closed Hilbert subspace, and subtracting its
orthogonal projection gives the minimal-norm weak solution for data already
in the range. Identification with holomorphic representatives and the sharp
projection estimate are separate, unproved analytic obligations. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology Distributions
namespace RepulsiveCoulomb

def coulombDbarWeakKernel (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    ClosedSubmodule ℂ (Lp ℂ 2 (coulombMeasure N β)) where
  toSubmodule := (coulombMaxDbarComplexGraph hβ).comap
    (LinearMap.inl ℂ (Lp ℂ 2 (coulombMeasure N β)) (Lp (CoulombConfig N) 2 (coulombMeasure N β)))
  isClosed' := by
    change IsClosed ((fun f : Lp ℂ 2 (coulombMeasure N β) => (f, 0)) ⁻¹'
      (coulombMaxDbarComplexGraph (N := N) hβ : Set (CoulombDbarL2Pair N β)))
    exact (coulombMaxDbarComplexGraph_isClosed hβ).preimage (continuous_id.prodMk continuous_const)

theorem coulombDbarWeakKernel_mem_iff {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (f : Lp ℂ 2 (coulombMeasure N β)) :
    f ∈ coulombDbarWeakKernel N hβ ↔ (f, 0) ∈ coulombMaxDbarGraph hβ := Iff.rfl

def coulombDbarWeakProjection (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Lp ℂ 2 (coulombMeasure N β) →L[ℂ] Lp ℂ 2 (coulombMeasure N β) :=
  (coulombDbarWeakKernel N hβ).toSubmodule.starProjection

theorem coulombDbarWeakProjection_mem_kernel {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (f : Lp ℂ 2 (coulombMeasure N β)) :
    coulombDbarWeakProjection N hβ f ∈ coulombDbarWeakKernel N hβ :=
  Submodule.starProjection_apply_mem _ f

theorem coulombDbarWeakProjection_residual_graph {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {f : Lp ℂ 2 (coulombMeasure N β)} {g : Lp (CoulombConfig N) 2 (coulombMeasure N β)}
    (hfg : (f, g) ∈ coulombMaxDbarGraph hβ) :
    (f - coulombDbarWeakProjection N hβ f, g) ∈ coulombMaxDbarGraph hβ := by
  have hK := (coulombDbarWeakKernel_mem_iff hβ _).mp (coulombDbarWeakProjection_mem_kernel hβ f)
  simpa only [Prod.mk_sub_mk, sub_zero] using (coulombMaxDbarGraph hβ).sub_mem hfg hK

theorem coulombDbarWeakProjection_residual_orthogonal {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (f : Lp ℂ 2 (coulombMeasure N β)) :
    f - coulombDbarWeakProjection N hβ f ∈ (coulombDbarWeakKernel N hβ).toSubmodule.orthogonal :=
  Submodule.sub_starProjection_mem_orthogonal f

theorem coulombDbarWeakProjection_residual_minimal {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {f s : Lp ℂ 2 (coulombMeasure N β)} {g : Lp (CoulombConfig N) 2 (coulombMeasure N β)}
    (hfg : (f, g) ∈ coulombMaxDbarGraph hβ) (hsg : (s, g) ∈ coulombMaxDbarGraph hβ) :
    ‖f - coulombDbarWeakProjection N hβ f‖ ≤ ‖s‖ := by
  have hK : f - s ∈ coulombDbarWeakKernel N hβ := by
    apply (coulombDbarWeakKernel_mem_iff hβ _).mpr
    simpa only [Prod.mk_sub_mk, sub_self] using (coulombMaxDbarGraph hβ).sub_mem hfg hsg
  change ‖f - (coulombDbarWeakKernel N hβ).toSubmodule.starProjection f‖ ≤ _
  rw [Submodule.starProjection_minimal]
  have hb : BddBelow (Set.range (fun x : (coulombDbarWeakKernel N hβ).toSubmodule => ‖f - (x : Lp ℂ 2 (coulombMeasure N β))‖)) :=
    ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
  simpa only [sub_sub_cancel] using ciInf_le hb (⟨f - s, hK⟩ : (coulombDbarWeakKernel N hβ).toSubmodule)

end RepulsiveCoulomb
