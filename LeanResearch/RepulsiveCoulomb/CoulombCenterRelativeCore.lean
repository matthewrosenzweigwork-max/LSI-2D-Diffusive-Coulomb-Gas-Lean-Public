import LeanResearch.RepulsiveCoulomb.CoulombCenterGradient

/-! Literal relative collision-free smooth core in the (N-1)-particle Euclidean
coordinate space, and actual Gaussian and relative slices of the original
many-particle core. The frozen center does not alter the relative domain. -/
noncomputable section
open Set MeasureTheory InnerProductSpace TopologicalSpace
open scoped Topology
namespace RepulsiveCoulomb

variable {n : ℕ}

def coulombCenterRelativeDomain (e : CoulombCenterRotation n) : Opens (CoulombConfig n) :=
  ⟨{r | coulombCenterInsert e 0 r ∈ coulombDomain (n + 1)},
    (coulombDomain (n + 1)).isOpen.preimage
      (e.symm.continuous.comp (coulombCenterRelativeInjection n).continuous)⟩

theorem coulombCenterInsert_contDiff_center (e : CoulombCenterRotation n)
    (r : CoulombConfig n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun c : ℂ => coulombCenterInsert e c r) :=
  e.symm.toContinuousLinearEquiv.contDiff.comp (coulombInsertZero_contDiff r)

theorem coulombCenterInsert_contDiff_relative (e : CoulombCenterRotation n) (c : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun r : CoulombConfig n => coulombCenterInsert e c r) := by
  have hi : ContDiff ℝ (⊤ : ℕ∞) (fun r : CoulombConfig n => coulombInsertZero c r) := by
    have h : (fun r : CoulombConfig n => coulombInsertZero c r) =
        fun r => coulombInsertZero c (0 : CoulombConfig n) + coulombCenterRelativeInjection n r := by
      funext r
      exact coulombInsertZero_add_axes c r
    rw [h]
    exact contDiff_const.add (coulombCenterRelativeInjection n).toContinuousLinearMap.contDiff
  exact e.symm.toContinuousLinearEquiv.contDiff.comp hi

theorem coulombCenterInsert_isometry_center (e : CoulombCenterRotation n)
    (r : CoulombConfig n) : Isometry (fun c : ℂ => coulombCenterInsert e c r) :=
  e.symm.isometry.comp (coulombInsertZero_isometry r)

theorem coulombCenterInsert_isometry_relative (e : CoulombCenterRotation n) (c : ℂ) :
    Isometry (fun r : CoulombConfig n => coulombCenterInsert e c r) := by
  have hi : Isometry (fun r : CoulombConfig n => coulombInsertZero c r) := by
    apply Isometry.of_dist_eq
    intro r s
    rw [dist_eq_norm, dist_eq_norm]
    have hs : coulombInsertZero c r - coulombInsertZero c s =
        coulombCenterRelativeInjection n (r - s) := by
      rw [coulombInsertZero_add_axes c r, coulombInsertZero_add_axes c s]
      rw [map_sub]
      change _ = coulombInsertZero 0 r - coulombInsertZero 0 s
      abel
    rw [hs, (coulombCenterRelativeInjection n).norm_map]
  exact e.symm.isometry.comp hi

def coulombCenterGaussianCore (e : CoulombCenterRotation n)
    (φ : TestFunction (coulombDomain (n + 1)) ℝ ⊤) (r : CoulombConfig n) :
    TestFunction (⊤ : Opens ℂ) ℝ ⊤ :=
  ⟨fun c => φ (coulombCenterInsert e c r),
    φ.contDiff.comp (coulombCenterInsert_contDiff_center e r),
    φ.hasCompactSupport.comp_isClosedEmbedding
      (coulombCenterInsert_isometry_center e r).isClosedEmbedding,
    fun _ _ => Set.mem_univ _⟩

def coulombCenterRelativeCore (e : CoulombCenterRotation n) (he : CoulombCenterAxis e)
    (φ : TestFunction (coulombDomain (n + 1)) ℝ ⊤) (c : ℂ) :
    TestFunction (coulombCenterRelativeDomain e) ℝ ⊤ :=
  ⟨fun r => φ (coulombCenterInsert e c r),
    φ.contDiff.comp (coulombCenterInsert_contDiff_relative e c),
    φ.hasCompactSupport.comp_isClosedEmbedding
      (coulombCenterInsert_isometry_relative e c).isClosedEmbedding,
    fun r hr => (coulombCenterInsert_mem_domain_iff e he c r).mp
      (φ.tsupport_subset (tsupport_comp_subset_preimage
        (φ : CoulombConfig (n + 1) → ℝ)
        (coulombCenterInsert_contDiff_relative e c).continuous hr))⟩

theorem coulombCenterGaussianCore_apply (e : CoulombCenterRotation n)
    (φ : TestFunction (coulombDomain (n + 1)) ℝ ⊤) (r : CoulombConfig n) (c : ℂ) :
    coulombCenterGaussianCore e φ r c = φ (coulombCenterInsert e c r) := rfl

theorem coulombCenterRelativeCore_apply (e : CoulombCenterRotation n) (he : CoulombCenterAxis e)
    (φ : TestFunction (coulombDomain (n + 1)) ℝ ⊤) (c : ℂ) (r : CoulombConfig n) :
    coulombCenterRelativeCore e he φ c r = φ (coulombCenterInsert e c r) := rfl

theorem coulombCenterGaussianCore_gradient (e : CoulombCenterRotation n)
    (φ : TestFunction (coulombDomain (n + 1)) ℝ ⊤) (r : CoulombConfig n) (c : ℂ) :
    gradient (coulombCenterGaussianCore e φ r : ℂ → ℝ) c =
      e (gradient (φ : CoulombConfig (n + 1) → ℝ) (coulombCenterInsert e c r)) 0 :=
  coulombCenter_center_gradient e c r (φ.contDiff.differentiable (by simp) _)

theorem coulombCenterRelativeCore_gradient (e : CoulombCenterRotation n) (he : CoulombCenterAxis e)
    (φ : TestFunction (coulombDomain (n + 1)) ℝ ⊤) (c : ℂ) (r : CoulombConfig n) :
    gradient (coulombCenterRelativeCore e he φ c : CoulombConfig n → ℝ) r =
      coulombTail (e (gradient (φ : CoulombConfig (n + 1) → ℝ) (coulombCenterInsert e c r))) :=
  coulombCenter_relative_gradient e c r (φ.contDiff.differentiable (by simp) _)

end RepulsiveCoulomb
