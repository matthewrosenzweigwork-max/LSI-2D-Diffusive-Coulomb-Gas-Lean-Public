import LeanResearch.RepulsiveCoulomb.EntropySquareScaling
import LeanResearch.RepulsiveCoulomb.CoulombFormIntegrals
import LeanResearch.RepulsiveCoulomb.CoulombCutoffEnergy
import LeanResearch.PeriodicAttractiveLogGas.EntropyL2

/-!
Zero-safe particle-core normalization and extension to the full original
closed physical form. No entropy integrability of a limit is assumed: the
checked extended entropy lower-semicontinuity theorem supplies that passage.
Records-only draft, not staged or checked.
-/
noncomputable section
open MeasureTheory Filter
open PeriodicAttractiveLogGas
open scoped Topology
namespace RepulsiveCoulomb

theorem conditionalEntropyBranch_core_smul_mass {N : ℕ} {β : ℝ}
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (c : ℝ) :
    (∫ z, (c • φ : TestFunction (coulombDomain N) ℝ ⊤) z ^ 2 ∂coulombMeasure N β) =
      c ^ 2 * (∫ z, φ z ^ 2 ∂coulombMeasure N β) := by
  change (∫ z, (c * φ z) ^ 2 ∂coulombMeasure N β) = _
  simp only [mul_pow, integral_const_mul]

theorem conditionalEntropyBranch_core_smul_energy {N : ℕ} {β : ℝ}
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (c : ℝ) :
    (∫ z, ‖gradient (c • φ : TestFunction (coulombDomain N) ℝ ⊤) z‖ ^ 2 ∂coulombMeasure N β) =
      c ^ 2 * (∫ z, ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2 ∂coulombMeasure N β) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  have h := TauCeti.gradient_const_smul (𝕜 := ℝ) (f := (φ : CoulombConfig N → ℝ)) (x := z) c
  have hn := congrArg (fun v : CoulombConfig N => ‖v‖ ^ 2) h
  simpa [norm_smul, mul_pow] using hn

theorem conditionalEntropyBranch_core_denormalize {N : ℕ} {β C D : ℝ}
    (hβ : 0 < β) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hNorm : ∀ φ : TestFunction (coulombDomain N) ℝ ⊤,
      (∫ z, φ z ^ 2 ∂coulombMeasure N β) = 1 →
      entropy (coulombMeasure N β) (fun z => φ z ^ 2) ≤
        ((C * (∫ z, ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2 ∂coulombMeasure N β) + D : ℝ) : EReal))
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    entropy (coulombMeasure N β) (fun z => φ z ^ 2) ≤
      ((C * (∫ z, ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2 ∂coulombMeasure N β) +
        D * (∫ z, φ z ^ 2 ∂coulombMeasure N β) : ℝ) : EReal) := by
  letI := coulombMeasure_isProbability (N := N) hβ
  obtain ⟨B, hBpos, hB⟩ := coulomb_testFunction_c1_bound φ
  have hFi : Integrable (fun z => φ z ^ 2) (coulombMeasure N β) :=
    Rothaus.integrable_continuous_comp_bounded φ.continuous.measurable
      (fun z => (hB z).1) (continuous_id.pow 2)
  let m : ℝ := ∫ z, φ z ^ 2 ∂coulombMeasure N β
  have hm : 0 ≤ m := integral_nonneg (fun z => sq_nonneg _)
  by_cases hz : m = 0
  · have hfzero : (fun z => φ z ^ 2) =ᵐ[coulombMeasure N β] (fun _ => (0 : ℝ)) :=
      (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall (fun _ => sq_nonneg _)) hFi).mp hz
    rw [entropy_congr_ae hfzero, entropy_zero]
    apply EReal.coe_le_coe_iff.mpr
    exact add_nonneg (mul_nonneg hC (integral_nonneg (fun _ => sq_nonneg _))) (mul_nonneg hD hm)
  · have hmp : 0 < m := lt_of_le_of_ne hm (Ne.symm hz)
    let c : ℝ := (Real.sqrt m)⁻¹
    let ψ : TestFunction (coulombDomain N) ℝ ⊤ := c • φ
    have hmc : m * c ^ 2 = 1 := by
      dsimp only [c]
      rw [inv_pow, Real.sq_sqrt hm]
      exact mul_inv_cancel₀ hz
    have hmassψ : (∫ z, ψ z ^ 2 ∂coulombMeasure N β) = 1 := by
      rw [conditionalEntropyBranch_core_smul_mass]
      exact (mul_comm (c ^ 2) m).trans hmc
    have hψ := hNorm ψ hmassψ
    obtain ⟨Bψ, hBψpos, hBψ⟩ := coulomb_testFunction_c1_bound ψ
    rw [Rothaus.entropy_sq_eq ψ.continuous.measurable (fun z => (hBψ z).1)] at hψ
    have hψreal := EReal.coe_le_coe_iff.mp hψ
    have hs : Rothaus.squareEntropy (coulombMeasure N β) ψ =
        c ^ 2 * Rothaus.squareEntropy (coulombMeasure N β) φ :=
      bounded_squareEntropy_smul (coulombMeasure N β) φ.continuous.measurable
        (fun z => (hB z).1) c
    have hEntropy : Rothaus.squareEntropy (coulombMeasure N β) φ =
        m * Rothaus.squareEntropy (coulombMeasure N β) ψ := by
      rw [hs, ← mul_assoc, hmc, one_mul]
    have hEnergy : m * (∫ z, ‖gradient (ψ : CoulombConfig N → ℝ) z‖ ^ 2 ∂coulombMeasure N β) =
        ∫ z, ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2 ∂coulombMeasure N β := by
      rw [conditionalEntropyBranch_core_smul_energy, ← mul_assoc, hmc, one_mul]
    rw [Rothaus.entropy_sq_eq φ.continuous.measurable (fun z => (hB z).1)]
    apply EReal.coe_le_coe_iff.mpr
    calc
      Rothaus.squareEntropy (coulombMeasure N β) φ = m * Rothaus.squareEntropy (coulombMeasure N β) ψ := hEntropy
      _ ≤ m * (C * (∫ z, ‖gradient (ψ : CoulombConfig N → ℝ) z‖ ^ 2 ∂coulombMeasure N β) + D) :=
        mul_le_mul_of_nonneg_left hψreal hm
      _ = C * (∫ z, ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2 ∂coulombMeasure N β) + D * m := by
        rw [← hEnergy]
        ring

/-- Exact full original-form extension, before centering and with the same
core coefficients. Infinite entropy of an approximating limit is handled by
the checked extended entropy L2 lower-semicontinuity theorem. -/
theorem conditionalEntropyBranch_form_of_core {N : ℕ} {β C D : ℝ} (hβ : 0 < β)
    (hcore : ∀ φ : TestFunction (coulombDomain N) ℝ ⊤,
      entropy (coulombMeasure N β) (fun z => φ z ^ 2) ≤
        ((C * (∫ z, ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2 ∂coulombMeasure N β) +
          D * (∫ z, φ z ^ 2 ∂coulombMeasure N β) : ℝ) : EReal))
    (u : CoulombFormDomain N hβ) :
    entropy (coulombMeasure N β) (fun z => (coulombFormValueL N hβ u z) ^ 2) ≤
      ((C * coulombFormEnergy N hβ u +
        D * (∫ z, (coulombFormValueL N hβ u z) ^ 2 ∂coulombMeasure N β) : ℝ) : EReal) := by
  obtain ⟨φ, hφ⟩ := coulombFormCore_approximation N hβ u
  have hv := ((coulombFormValueL N hβ).continuous.tendsto u).comp hφ
  have hg := ((coulombFormGradientL N hβ).continuous.tendsto u).comp hφ
  simp only [Function.comp_def] at hv hg
  have he : Tendsto (fun n => coulombFormEnergy N hβ (coulombFormCore hβ (φ n))) atTop
      (𝓝 (coulombFormEnergy N hβ u)) := hg.norm.pow 2
  have hm : Tendsto (fun n => ∫ z, (coulombFormValueL N hβ (coulombFormCore hβ (φ n)) z) ^ 2
      ∂coulombMeasure N β) atTop (𝓝 (∫ z, (coulombFormValueL N hβ u z) ^ 2 ∂coulombMeasure N β)) := by
    simpa only [← coulombFormValue_norm_sq_eq_integral] using hv.norm.pow 2
  apply entropy_sq_le_of_tendsto hv ((tendsto_const_nhds.mul he).add (tendsto_const_nhds.mul hm))
  intro n
  have hval := (coulombFormCore_value hβ (φ n)).mono (fun _ hx => congrArg (fun t : ℝ => t ^ 2) hx)
  rw [entropy_congr_ae hval, coulombFormCore_energy_eq_integral, coulombFormCore_mass_eq_integral]
  exact hcore (φ n)

end RepulsiveCoulomb
