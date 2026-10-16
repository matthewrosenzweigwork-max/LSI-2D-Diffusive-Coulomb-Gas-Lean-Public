module

public import LeanResearch.RepulsiveCoulomb.CoulombCenterRelativeAmbientJet

@[expose] public section

/-! Every ambient compact smooth relative jet lifts to the actual original
closed form, independently of relative collision-free support. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombCenterRelativeAmbientJet_lift_mem (m : ℕ)
    (e : CoulombCenterRotation (m + 1)) (he : CoulombCenterAxis e)
    {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (⊤ : Opens (CoulombConfig (m + 1))) ℝ ⊤) :
    coulombCenterRelativeJetLiftL e he hβ (coulombCenterRelativeAmbientJet e he hβ ψ) ∈
      coulombCoreGraph (m + 2) hβ := by
  let f : CoulombConfig (m + 2) → ℝ := fun z => ψ (coulombCenterRelativeProjection e z)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := ψ.contDiff.comp (coulombCenterRelativeProjection e).contDiff
  obtain ⟨B, hBpos, hB⟩ := coulombCenter_test_c1_bound (⊤ : Opens (CoulombConfig (m + 1))) ψ
  have hb : ∀ z, |f z| ≤ B := fun z => (hB (coulombCenterRelativeProjection e z)).1
  have hgb : ∀ z, ‖gradient f z‖ ≤ B := by
    intro z
    rw [coulombCenter_relative_cylinder_gradient_norm e z (ψ.contDiff.differentiable (by simp) _)]
    exact (hB (coulombCenterRelativeProjection e z)).2
  let u := coulombBoundedSmoothForm m hβ f hf B hb hgb
  have huc : (u : CoulombJetL2 (m + 2) β) =ᵐ[coulombMeasure (m + 2) β]
      fun z => WithLp.toLp 2 (f z, gradient f z) :=
    coulombBoundedSmoothJet_coe m hβ f hf B hb hgb
  have hp := (coulombCenterRelativeProjection_measurePreserving e he hβ).quasiMeasurePreserving.ae
    (coulombCenterRelativeAmbientJet_coe e he hβ ψ)
  have hj : coulombCenterRelativeJetLiftL e he hβ (coulombCenterRelativeAmbientJet e he hβ ψ) =
      (u : CoulombJetL2 (m + 2) β) := by
    apply Lp.ext
    filter_upwards [coulombCenterRelativeJetLiftL_coe e he hβ
      (coulombCenterRelativeAmbientJet e he hβ ψ), hp, huc] with z hl hψ hu
    rw [hl, hψ, hu, coulombCenterRelativeJetFiber_apply]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd]
    congr 1
    apply Prod.ext
    · rfl
    · exact (coulombCenter_relative_cylinder_gradient e z
        (ψ.contDiff.differentiable (by simp) _)).symm
  rw [hj, ← coe_coulombFormSubmodule]
  exact u.property

end RepulsiveCoulomb
