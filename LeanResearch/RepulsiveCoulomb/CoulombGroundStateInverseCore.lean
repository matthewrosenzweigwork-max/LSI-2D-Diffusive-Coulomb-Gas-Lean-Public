import LeanResearch.RepulsiveCoulomb.CoulombGroundStateCore

/-! The inverse normalized ground-state transform preserves the original core.
There is no common-support assumption and no restriction on particle collisions
beyond the original compact support inside the collision complement. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombInverseGroundState_contDiff {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombDomain N) ℝ ⊤) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => ψ z / Real.sqrt (coulombDensity N β z)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ coulombDomain N
  · have hd : ContDiffAt ℝ (⊤ : ℕ∞) (coulombDensity N β) z :=
      (coulombDensity_contDiffAt β hz).of_le (by simp)
    have hp := coulombDensity_pos_off_collisions hβ hz
    exact ψ.contDiff.contDiffAt.div (hd.sqrt hp.ne') (Real.sqrt_pos.mpr hp).ne'
  · have hn : z ∉ tsupport (ψ : CoulombConfig N → ℝ) := fun ht => hz (ψ.tsupport_subset ht)
    have he := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun _ : CoulombConfig N => (0 : ℝ)) z).congr_of_eventuallyEq
    filter_upwards [he] with x hx
    simp [hx]

def coulombInverseGroundStateCore {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombDomain N) ℝ ⊤) : TestFunction (coulombDomain N) ℝ ⊤ :=
  ⟨fun z => ψ z / Real.sqrt (coulombDensity N β z),
    coulombInverseGroundState_contDiff hβ ψ,
    by simpa only [div_eq_mul_inv, Pi.mul_apply] using!
      (ψ.hasCompactSupport.mul_right (f' := fun z => (Real.sqrt (coulombDensity N β z))⁻¹)),
    by simpa only [div_eq_mul_inv] using
      (tsupport_mul_subset_left (f := (ψ : CoulombConfig N → ℝ))
        (g := fun z => (Real.sqrt (coulombDensity N β z))⁻¹)).trans ψ.tsupport_subset⟩

theorem coulombInverseGroundStateCore_apply {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombDomain N) ℝ ⊤) (z : CoulombConfig N) :
    coulombInverseGroundStateCore hβ ψ z = ψ z / Real.sqrt (coulombDensity N β z) := rfl

theorem coulombGroundState_inverse_core {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombGroundStateCore hβ (coulombInverseGroundStateCore hβ ψ) = ψ := by
  ext z
  rw [coulombGroundStateCore_apply, coulombInverseGroundStateCore_apply]
  by_cases hz : z ∈ coulombDomain N
  · exact div_mul_cancel₀ _ (Real.sqrt_pos.mpr (coulombDensity_pos_off_collisions hβ hz)).ne'
  · have hzero : ψ z = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hz (ψ.tsupport_subset ht))
    simp [hzero]

theorem coulombInverseGroundState_core {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombInverseGroundStateCore hβ (coulombGroundStateCore hβ φ) = φ := by
  ext z
  rw [coulombInverseGroundStateCore_apply, coulombGroundStateCore_apply]
  by_cases hz : z ∈ coulombDomain N
  · exact mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr (coulombDensity_pos_off_collisions hβ hz)).ne'
  · have hzero : φ z = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hz (φ.tsupport_subset ht))
    simp [hzero]

end RepulsiveCoulomb
