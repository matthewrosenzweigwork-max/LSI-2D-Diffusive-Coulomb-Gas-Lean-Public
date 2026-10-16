module

public import LeanResearch.RepulsiveCoulomb.CoulombCenterRelativeSliceApproximation

@[expose] public section

/-! Exact equality of the relative ambient smooth closure and collision-free
smooth closure. It is obtained from the ORIGINAL common core via genuine
bounded-cylinder lifting and contractive good-center slice approximation. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombCenterRelativeAmbientJet_mem_closedCore (m : ℕ)
    (e : CoulombCenterRotation (m + 1)) (he : CoulombCenterAxis e)
    {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (⊤ : Opens (CoulombConfig (m + 1))) ℝ ⊤) :
    coulombCenterRelativeAmbientJet e he hβ ψ ∈
      (coulombCenterRelativeFormSubmodule e he hβ : Set _) := by
  let J := coulombCenterRelativeAmbientJet e he hβ ψ
  have hL := coulombCenterRelativeAmbientJet_lift_mem m e he hβ ψ
  change coulombCenterRelativeJetLiftL e he hβ J ∈
    closure (range (coulombCoreJet (N := m + 2) hβ)) at hL
  obtain ⟨K, hK, hlim⟩ := mem_closure_iff_seq_limit.mp hL
  choose φ hφ using hK
  have hφlim : Tendsto (fun k => coulombCoreJet hβ (φ k)) atTop
      (𝓝 (coulombCenterRelativeJetLiftL e he hβ J)) := by
    simpa only [hφ] using hlim
  choose c hc using (fun k => coulombCenterRelative_exists_good_slice e he hβ (φ k) ψ)
  have hrel : Tendsto (fun k => coulombCenterRelativeCoreJet e he hβ
      (coulombCenterRelativeCore e he (φ k) (c k))) atTop (𝓝 J) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun k => norm_nonneg _) hc
    exact tendsto_iff_norm_sub_tendsto_zero.mp hφlim
  rw [coulombCenterRelativeFormSubmodule, Submodule.coe_closure, LinearMap.coe_range]
  change J ∈ closure (range (coulombCenterRelativeCoreJet e he hβ))
  exact isClosed_closure.mem_of_tendsto hrel
    (Eventually.of_forall (fun k => subset_closure (mem_range_self _)))

/-- Relative common-core identification for the actual marginal law. This is
the domain correspondence needed to interpret its optimal constant as the
natural full physical weighted form optimum, not merely the punctured core. -/
theorem coulombCenter_relative_common_core (m : ℕ)
    (e : CoulombCenterRotation (m + 1)) (he : CoulombCenterAxis e)
    {β : ℝ} (hβ : 0 < β) :
    closure (range (coulombCenterRelativeAmbientJet e he hβ)) =
      (coulombCenterRelativeFormSubmodule e he hβ : Set (CoulombCenterRelativeJetL2 e β)) := by
  apply Subset.antisymm
  · apply closure_minimal
    · rintro J ⟨ψ, rfl⟩
      exact coulombCenterRelativeAmbientJet_mem_closedCore m e he hβ ψ
    · exact (coulombCenterRelativeFormSubmodule e he hβ).isClosed
  · rw [coulombCenterRelativeFormSubmodule, Submodule.coe_closure, LinearMap.coe_range]
    change closure (range (coulombCenterRelativeCoreJet e he hβ)) ⊆ _
    apply closure_mono
    rintro J ⟨ψ, rfl⟩
    let φ : TestFunction (⊤ : Opens (CoulombConfig (m + 1))) ℝ ⊤ :=
      ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, by simp⟩
    refine ⟨φ, ?_⟩
    apply Lp.ext
    filter_upwards [coulombCenterRelativeAmbientJet_coe e he hβ φ,
      coulombCenterRelativeCoreJet_coe e he hβ ψ] with r ha hc
    rw [ha, hc]
    rfl

end RepulsiveCoulomb
