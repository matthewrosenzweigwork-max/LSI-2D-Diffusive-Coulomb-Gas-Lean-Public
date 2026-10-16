module

public import LeanResearch.RepulsiveCoulomb.CoulombFormIntegrals
public import LeanResearch.RepulsiveCoulomb.CoulombLocalL2

@[expose] public section

/-! Actual unweighted local physical H1 control on the full closed form.
The compact set must avoid collisions; compactness itself is not asserted. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem coulombForm_local_h1_bound {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (havoid : K ⊆ coulombDomain N) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : CoulombFormDomain N hβ,
      (∫ z in K, coulombFormValueL N hβ u z ^ 2) +
        (∫ z in K, ‖coulombFormGradientL N hβ u z‖ ^ 2) ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨D, hD, hmeasure⟩ := coulombMeasure_volume_restrict_le hβ hK havoid (Subset.rfl : K ⊆ K)
  refine ⟨D.toReal + 1, by positivity, ?_⟩
  intro u
  have hv := coulombFormValue_square_integrable N hβ u
  have hg := coulombFormGradient_square_integrable N hβ u
  have hvK := (hv.smul_measure hD).mono_measure hmeasure
  have hgK := (hg.smul_measure hD).mono_measure hmeasure
  have hm := integral_mono_measure hmeasure
    (Eventually.of_forall (fun z => show 0 ≤ coulombFormValueL N hβ u z ^ 2 +
      ‖coulombFormGradientL N hβ u z‖ ^ 2 by positivity)) ((hv.add hg).smul_measure hD)
  rw [integral_smul_measure] at hm
  rw [integral_add hvK hgK, integral_add hv hg] at hm
  simp only [smul_eq_mul] at hm
  rw [← coulombFormValue_norm_sq_eq_integral N hβ u,
    ← coulombFormEnergy_eq_integral N hβ u, ← coulombForm_norm_sq N hβ u] at hm
  exact hm.trans (by nlinarith [sq_nonneg ‖u‖])

end RepulsiveCoulomb
