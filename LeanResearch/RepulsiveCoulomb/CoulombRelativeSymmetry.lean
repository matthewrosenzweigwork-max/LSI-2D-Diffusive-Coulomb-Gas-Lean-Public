import LeanResearch.RepulsiveCoulomb.CoulombRelativeKernel

/-! Sign symmetry of the literal relative conditional. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem coulombRelative_pointWeight_even {N : ℕ} (γ α : ℝ) (c u : ℂ) (y : CoulombConfig N) :
    pointWeight γ (fun _ : Fin (N + N + 1) => α) (coulombRelativeRoots c y) (-u) =
      pointWeight γ (fun _ : Fin (N + N + 1) => α) (coulombRelativeRoots c y) u := by
  rw [coulombRelative_pointWeight, coulombRelative_pointWeight]
  simp only [norm_neg]
  have hl (v : ℂ) : ‖-u - v‖ = ‖u + v‖ := by
    have he : -u - v = -(u + v) := by abel
    rw [he, norm_neg]
  have hr (v : ℂ) : ‖-u + v‖ = ‖u - v‖ := by rw [neg_add_eq_sub, norm_sub_rev]
  simp_rw [hl, hr]
  ring

theorem coulombRelativeKernel_neg_measurePreserving {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (p : ℂ × CoulombConfig N) :
    MeasurePreserving (fun u : ℂ => -u) (coulombRelativeKernel N β hβ p)
      (coulombRelativeKernel N β hβ p) := by
  refine ⟨measurable_neg, ?_⟩
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF measurable_neg, coulombRelativeKernel_apply]
  rw [pointMeasure_lintegral _ _ _ (F := fun u => F (-u)) (hF.comp measurable_neg),
    pointMeasure_lintegral _ _ _ hF]
  congr 1
  have hw := (pointWeight_measurable β (coulombRelativeExponents N β) (coulombRelativeRoots p.1 p.2)).ennreal_ofReal.mul hF
  have hm : MeasurePreserving (fun u : ℂ => -u) volume volume :=
    (LinearIsometryEquiv.neg ℝ : ℂ ≃ₗᵢ[ℝ] ℂ).measurePreserving
  have he := hm.lintegral_comp hw
  dsimp only [Pi.mul_apply] at he
  have hev (u : ℂ) : pointWeight β (coulombRelativeExponents N β) (coulombRelativeRoots p.1 p.2) (-u) =
      pointWeight β (coulombRelativeExponents N β) (coulombRelativeRoots p.1 p.2) u :=
    coulombRelative_pointWeight_even β (β / ((N + 2 : ℕ) : ℝ)) p.1 u p.2
  simp_rw [hev] at he
  exact he

end RepulsiveCoulomb

