module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-! A bounded functional on the algebraic range of a linear map extends
to its ambient normed space with the same bound. The application will supply
the bound from the actual curvature estimate; no closed-range premise is
required and the source module need not have a Hilbert graph norm. -/
noncomputable section
namespace RepulsiveCoulomb

theorem dbarLinearMap_exists_bounded_factor
    {D E : Type*} [AddCommGroup D] [Module ℂ D]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : D →ₗ[ℂ] E) (P : D →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖P x‖ ≤ C * ‖Q x‖) :
    ∃ ℓ : E →L[ℂ] ℂ, (∀ x, ℓ (Q x) = P x) ∧ ‖ℓ‖ ≤ C := by
  classical
  let pick : Q.range → D := fun y =>
    Classical.choose (show ∃ x, Q x = (y : E) from y.property)
  have hpick (y : Q.range) : Q (pick y) = (y : E) :=
    Classical.choose_spec (show ∃ x, Q x = (y : E) from y.property)
  have hsame (x y : D) (hxy : Q x = Q y) : P x = P y := by
    have h := hbound (x - y)
    simp only [map_sub, hxy, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  let F : Q.range →ₗ[ℂ] ℂ :=
    { toFun := fun y => P (pick y)
      map_add' := by
        intro y z
        have he : Q (pick (y + z)) = Q (pick y + pick z) := by
          rw [hpick, map_add, hpick, hpick]
          rfl
        exact (hsame _ _ he).trans (map_add P (pick y) (pick z))
      map_smul' := by
        intro c y
        have he : Q (pick (c • y)) = Q (c • pick y) := by
          rw [hpick, map_smul, hpick]
          rfl
        exact (hsame _ _ he).trans (map_smul P c (pick y)) }
  have hF (y : Q.range) : ‖F y‖ ≤ C * ‖y‖ := by
    change ‖P (pick y)‖ ≤ C * ‖(y : E)‖
    simpa only [hpick] using hbound (pick y)
  obtain ⟨ℓ, hext, hnorm⟩ := exists_extension_norm_eq Q.range (F.mkContinuous C hF)
  refine ⟨ℓ, ?_, ?_⟩
  · intro x
    let y : Q.range := ⟨Q x, ⟨x, rfl⟩⟩
    have he := hext y
    change ℓ (Q x) = P (pick y) at he
    exact he.trans (hsame (pick y) x (hpick y))
  · exact hnorm.trans_le (F.mkContinuous_norm_le hC hF)

end RepulsiveCoulomb
