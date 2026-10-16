import LeanResearch.RepulsiveCoulomb.CoulombFormApproximation
import LeanResearch.RepulsiveCoulomb.DbarBranchDenseDomain

/-! Density of the actual real closed-form value range in Gibbs L2.
The proof uses weighted-measure test annihilation, not a Haar theorem on Gibbs. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology Distributions
namespace RepulsiveCoulomb

theorem coulombFormValueL_annihilator {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (f : Lp ℝ 2 (coulombMeasure N β))
    (hf : ∀ u : CoulombFormDomain N hβ, inner ℝ (coulombFormValueL N hβ u) f = 0) : f = 0 := by
  letI := coulombMeasure_isProbability (N := N) hβ
  have hloc : LocallyIntegrableOn (f : CoulombConfig N → ℝ)
      (coulombDomain N) (coulombMeasure N β) :=
    (MemLp.integrable (by norm_num) (Lp.memLp f)).locallyIntegrable.locallyIntegrableOn _
  have hzero := (coulombDomain N).isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun g hg hgc hgΩ => by
      let φ : TestFunction (coulombDomain N) ℝ ⊤ := ⟨g, hg, hgc, hgΩ⟩
      have he : (∫ z, g z • f z ∂coulombMeasure N β) =
          inner ℝ (coulombFormValueL N hβ (coulombFormCore hβ φ)) f := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [coulombFormCore_value hβ φ] with z hz
        rw [hz]
        simp only [φ, RCLike.inner_apply', starRingEnd_apply, star_trivial, smul_eq_mul]
        rfl
      exact he.trans (hf (coulombFormCore hβ φ)))
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hzero, (coulombMeasure_ae_iff hβ).mpr (coulombDomain_ae N)] with z hz hΩ
  exact hz hΩ

theorem coulombFormValueL_denseRange (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    DenseRange (coulombFormValueL N hβ) := by
  change Dense (LinearMap.range (coulombFormValueL N hβ).toLinearMap : Set (Lp ℝ 2 (coulombMeasure N β)))
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro f hf
  apply coulombFormValueL_annihilator hβ f
  intro u
  exact hf (coulombFormValueL N hβ u) ⟨u, rfl⟩

end RepulsiveCoulomb
