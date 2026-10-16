module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchActualNelsonTail
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchExponentialTailBound

@[expose] public section

/-! Actual uniform repulsive partition bound for the constructed thermal
reference. The proof instantiates the proved finite-list correlation estimate,
keeps the canonical one-body correction, uses double-smoothed positivity, and
integrates the true probability tail. No equilibrium or partition hypothesis
is added to the manuscript-facing selected-reference theorem. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

/-- A bound depending only on T works for every actually constructed reference,
every positive beta, every N>=2 and every 0<=t<=T. -/
theorem equilibriumReferencePartition_uniform {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ β (hβ : 0 < β) (R : EquilibriumConstructedReference β),
      ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t → t ≤ T → equilibriumReferencePartition N t R ≤ C := by
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
  intro β hβ R N hN t ht htT
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have har : T / 4 ≤ ((2 * m : ℕ) : ℝ) := by
    push_cast
    linarith
  have hXm : Measurable (fun z : Fin N → ℂ => -t * equilibriumModulatedEnergy R.density z) :=
    measurable_const.mul (equilibriumModulatedEnergy_measurable R.smooth.continuous.measurable)
  have hcut : ∀ᵐ z : Fin N → ℂ ∂Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ)),
      -t * equilibriumModulatedEnergy R.density z ≤ (T / 4) * Real.log (N : ℝ) + T / 2 := by
    filter_upwards [equilibriumReference_nelson_tail_cutoff hβ R (by omega : 0 < N) ht htT] with z hz
    nlinarith
  have htail : ∀ u : ℝ, 1 ≤ u →
      (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ)))
        {z : Fin N → ℂ | u < -t * equilibriumModulatedEnergy R.density z} ≤
      ENNReal.ofReal (D * ((N : ℝ) ^ (-((2 * m : ℕ) : ℝ)) + Real.exp (-q * u))) :=
    fun u hu => equilibriumReference_actual_nelson_tail hβ R hN hk hm hT ht htT hu
  have h := equilibrium_exponential_log_cutoff_bound hXm hn har hq1 hD.le hcut htail
  rw [← ofReal_integral_eq_lintegral_ofReal
    (equilibriumReference_modulated_exp_integrable hβ R (by omega : 0 < N) ht)
    (Eventually.of_forall (fun z => (Real.exp_pos _).le))] at h
  exact (ENNReal.ofReal_le_ofReal_iff hC.le).mp h

/-- The exact manuscript compact-temperature specialization, with the reference
selected by the actual existence/uniqueness/regularity construction. -/
theorem equilibriumConstructedReference_partition_uniform {βlo βhi T : ℝ}
    (hlo : 0 < βlo) (hord : βlo ≤ βhi) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ β (hβlo : βlo ≤ β) (hβhi : β ≤ βhi),
      ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 < t → t ≤ T →
      equilibriumReferencePartition N t (equilibriumConstructedReference β (hlo.trans_le hβlo)) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := equilibriumReferencePartition_uniform hT
  refine ⟨C, hC, ?_⟩
  intro β hβlo hβhi N hN t ht htT
  exact hbound β (hlo.trans_le hβlo) (equilibriumConstructedReference β (hlo.trans_le hβlo))
    N hN t ht.le htT

end RepulsiveCoulomb
