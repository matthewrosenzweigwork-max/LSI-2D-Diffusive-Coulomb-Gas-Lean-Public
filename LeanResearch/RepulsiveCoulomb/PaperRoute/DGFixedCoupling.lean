module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchActualNelsonTail
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchExponentialTailBound

@[expose] public section

/-! Correctly normalized fixed-coupling upper-bound instance of the
Delgadino–Gvalani type, for the actual supplied thermal-reference class.
This directly applies the proved finite-product correlation/Nelson argument.
The canonical one-body correction is retained; no old all-coupling partition
endpoint or selected thermal reference is used. The signed spatial-diagonal
representation bridge is a separate obligation. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb.PaperRoute

/-- The numerical bound is selected before beta, the supplied reference and N.
It depends only on the fixed coupling T; the reference cap is exactly 1/pi. -/
theorem paper_dg_fixed_coupling {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ β (_hβ : 0 < β) (R : EquilibriumConstructedReference β),
      ∀ N : ℕ, 2 ≤ N → equilibriumReferencePartition N T R ≤ C := by
  obtain ⟨k, m, hk, hm, hkT, hmT, hpEven, hp, hq, hqp⟩ := equilibriumPartition_parameters_exist T
  let q : ℝ := (k : ℝ) / T
  let D : ℝ := equilibriumPartitionTailConstant T k m
  have hq1 : 1 < q := by
    apply (lt_div_iff₀ hT).mpr
    linarith
  have hD : 0 < D := equilibriumPartitionTailConstant_pos hT k m
  let C : ℝ := Real.exp 1 + D * Real.exp (T / 2) + D / (q - 1)
  have hC : 0 < C := by
    dsimp only [C]
    have hq0 : 0 < q - 1 := by linarith
    positivity
  refine ⟨C, hC, ?_⟩
  intro β hβ R N hN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have har : T / 4 ≤ ((2 * m : ℕ) : ℝ) := by
    push_cast
    linarith
  have hXm : Measurable (fun z : Fin N → ℂ => -T * equilibriumModulatedEnergy R.density z) :=
    measurable_const.mul (equilibriumModulatedEnergy_measurable R.smooth.continuous.measurable)
  have hcut : ∀ᵐ z : Fin N → ℂ ∂Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ)),
      -T * equilibriumModulatedEnergy R.density z ≤ (T / 4) * Real.log (N : ℝ) + T / 2 := by
    filter_upwards [equilibriumReference_nelson_tail_cutoff hβ R (by omega : 0 < N) hT.le le_rfl] with z hz
    nlinarith
  have htail : ∀ u : ℝ, 1 ≤ u →
      (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ)))
        {z : Fin N → ℂ | u < -T * equilibriumModulatedEnergy R.density z} ≤
      ENNReal.ofReal (D * ((N : ℝ) ^ (-((2 * m : ℕ) : ℝ)) + Real.exp (-q * u))) :=
    fun u hu => equilibriumReference_actual_nelson_tail hβ R hN hk hm hT hT.le le_rfl hu
  have h := equilibrium_exponential_log_cutoff_bound hXm hn har hq1 hD.le hcut htail
  rw [← ofReal_integral_eq_lintegral_ofReal
    (equilibriumReference_modulated_exp_integrable hβ R (by omega : 0 < N) hT.le)
    (Eventually.of_forall (fun z => (Real.exp_pos _).le))] at h
  exact (ENNReal.ofReal_le_ofReal_iff hC.le).mp h

end RepulsiveCoulomb.PaperRoute
