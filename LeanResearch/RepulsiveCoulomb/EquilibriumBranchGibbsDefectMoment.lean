module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCanonicalSplitting
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchProductExponential
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchPartitionBasic
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchReferenceCompactBounds

@[expose] public section

/-! The actual exponential moment in the manuscript's additive entropy defect.
The one-body term has its exact factor 1/N. Product Jensen and Cauchy--Schwarz
supply genuine integrability and the precise partition/one-body bound.
Records-only uncompiled source. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

def equilibriumDefectEnergy {N : ℕ} (ρ : ℂ → ℝ) (z : Fin N → ℂ) : ℝ :=
  equilibriumModulatedEnergy ρ z + (∑ i, equilibriumDensityPotential ρ (z i)) / (N : ℝ)

theorem equilibriumDefectEnergy_measurable {N : ℕ} {ρ : ℂ → ℝ} (hρ : Measurable ρ) :
    Measurable (equilibriumDefectEnergy (N := N) ρ) :=
  (equilibriumModulatedEnergy_measurable hρ).add
    ((Finset.measurable_sum Finset.univ (fun i _ =>
      (equilibriumDensityPotential_measurable hρ).comp (measurable_pi_apply i))).div_const _)

/-- The exact Gibbs exponential-moment estimate in particle coordinates. The
reference moment and both partition integrals are genuine finite integrals. -/
theorem equilibriumReference_gibbs_defect_moment {β ℓ : ℝ} (hβ : 0 < β) (hℓ : 0 < ℓ)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) :
    Integrable (fun z : Fin N → ℂ => Real.exp (-ℓ * β * equilibriumDefectEnergy R.density z))
      (Measure.map (@WithLp.ofLp 2 (Fin N → ℂ)) (coulombMeasure N β)) ∧
    (∫ z : Fin N → ℂ, Real.exp (-ℓ * β * equilibriumDefectEnergy R.density z)
      ∂Measure.map (@WithLp.ofLp 2 (Fin N → ℂ)) (coulombMeasure N β)) ≤
      (equilibriumReferencePartition N β R)⁻¹ *
        (equilibriumReferencePartition N (2 * (1 + ℓ) * β) R) ^ (1 / 2 : ℝ) *
          (∫ x : ℂ, Real.exp (-(2 * ℓ) * β * equilibriumDensityPotential R.density x)
            ∂R.measure) ^ (1 / 2 : ℝ) := by
  let P := Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))
  let A : (Fin N → ℂ) → ℝ := equilibriumModulatedEnergy R.density
  let U : ℂ → ℝ := equilibriumDensityPotential R.density
  let F : (Fin N → ℂ) → ℝ := fun z => Real.exp (-(1 + ℓ) * β * A z)
  let G : (Fin N → ℂ) → ℝ := fun z => Real.exp (-ℓ * β * ((∑ i, U (z i)) / (N : ℝ)))
  let E : (Fin N → ℂ) → ℝ := fun z => Real.exp (-ℓ * β * equilibriumDefectEnergy R.density z)
  let K := equilibriumReferencePartition N β R
  have hK : 0 < K := equilibriumReferencePartition_canonical_pos hβ R N
  have hAm : Measurable A := equilibriumModulatedEnergy_measurable R.smooth.continuous.measurable
  have hUm : Measurable U := equilibriumDensityPotential_measurable R.smooth.continuous.measurable
  have hFm : Measurable F := (measurable_const.mul hAm).exp
  have hGm : Measurable G := (measurable_const.mul
    ((Finset.measurable_sum Finset.univ (fun i _ => hUm.comp (measurable_pi_apply i))).div_const _)).exp
  have hF2 : (fun z => F z ^ 2) =
      (fun z : Fin N → ℂ => Real.exp (-(2 * (1 + ℓ) * β) * A z)) := by
    funext z
    dsimp only [F]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hFi : Integrable (fun z => F z ^ 2) P := by
    rw [hF2]
    exact equilibriumReference_modulated_exp_integrable hβ R hN (by positivity)
  have hFint : (∫ z, F z ^ 2 ∂P) = equilibriumReferencePartition N (2 * (1 + ℓ) * β) R := by
    rw [hF2]
    rfl
  have hUi : Integrable (fun x : ℂ => Real.exp (-(2 * ℓ) * β * U x))
      (R.measure : Measure ℂ) :=
    (equilibriumReference_potential_exponential_bound (θ := 2 * ℓ) hβ le_rfl le_rfl
      (mul_pos (by norm_num : (0 : ℝ) < 2) hℓ) R).1
  have hJ := equilibriumProduct_exp_average (f := fun x : ℂ => -(2 * ℓ) * β * U x)
    (measurable_const.mul hUm) hUi hN
  have hG2 : (fun z => G z ^ 2) = (fun z : Fin N → ℂ =>
      Real.exp ((∑ i, -(2 * ℓ) * β * U (z i)) / (N : ℝ))) := by
    funext z
    dsimp only [G]
    rw [pow_two, ← Real.exp_add, ← Finset.mul_sum]
    congr 1
    ring
  have hGi : Integrable (fun z => G z ^ 2) P := by rw [hG2]; exact hJ.1
  have hGint : (∫ z, G z ^ 2 ∂P) ≤
      ∫ x : ℂ, Real.exp (-(2 * ℓ) * β * U x) ∂R.measure := by rw [hG2]; exact hJ.2
  obtain ⟨hFGi, hCS⟩ := equilibrium_integral_mul_le_half_powers hFm hGm
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le) hFi hGi
  have hproduct (z : Fin N → ℂ) : E z * Real.exp (-β * A z) = F z * G z := by
    dsimp only [E, F, G, equilibriumDefectEnergy, A, U]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hwm : Measurable (fun z : Fin N → ℂ => ENNReal.ofReal (Real.exp (-β * A z) / K)) :=
    ((measurable_const.mul hAm).exp.div_const K).ennreal_ofReal
  have hwi : Integrable E (P.tilted (fun z => -β * A z)) := by
    change Integrable E (P.withDensity (fun z => ENNReal.ofReal (Real.exp (-β * A z) / K)))
    apply (integrable_withDensity_iff hwm (Eventually.of_forall
      (fun _ => ENNReal.ofReal_lt_top))).mpr
    simp only [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hK.le)]
    apply (hFGi.div_const K).congr
    exact Eventually.of_forall (fun z => by
      dsimp only
      rw [← hproduct z]
      ring)
  have hval : (∫ z, E z ∂P.tilted (fun z => -β * A z)) = K⁻¹ * ∫ z, F z * G z ∂P := by
    change (∫ z, E z ∂P.withDensity (fun z => ENNReal.ofReal (Real.exp (-β * A z) / K))) = _
    rw [integral_withDensity_eq_integral_toReal_smul hwm
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hK.le), smul_eq_mul]
    calc
      _ = ∫ z, (F z * G z) / K ∂P := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => by
          change Real.exp (-β * A z) / K * E z = (F z * G z) / K
          rw [← hproduct z]
          ring)
      _ = _ := by rw [integral_div, div_eq_inv_mul]
  rw [equilibriumReference_coulombMeasure_eq_tilted hβ R N]
  refine ⟨hwi, ?_⟩
  change (∫ z, E z ∂P.tilted (fun z => -β * A z)) ≤ _
  rw [hval]
  have hroot := Real.rpow_le_rpow (integral_nonneg (fun z => sq_nonneg (G z))) hGint
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hCS' := hCS.trans (mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg
    (integral_nonneg (fun z => sq_nonneg (F z))) _))
  have h := mul_le_mul_of_nonneg_left hCS' (inv_nonneg.mpr hK.le)
  rw [hFint] at h
  simpa only [mul_assoc] using h

/-- Physical l2 configuration formulation, suitable for the canonical
conditional-entropy theorem without changing coordinate or gradient norms. -/
theorem equilibriumReference_physical_gibbs_defect_moment {β ℓ : ℝ}
    (hβ : 0 < β) (hℓ : 0 < ℓ) (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) :
    Integrable (fun z : CoulombConfig N => Real.exp (-ℓ * β *
      (equilibriumModulatedEnergy R.density (@WithLp.ofLp 2 (Fin N → ℂ) z) +
        (∑ i : Fin N, equilibriumDensityPotential R.density (z i)) / (N : ℝ)))) (coulombMeasure N β) ∧
    (∫ z : CoulombConfig N, Real.exp (-ℓ * β *
      (equilibriumModulatedEnergy R.density (@WithLp.ofLp 2 (Fin N → ℂ) z) +
        (∑ i : Fin N, equilibriumDensityPotential R.density (z i)) / (N : ℝ))) ∂coulombMeasure N β) ≤
      (equilibriumReferencePartition N β R)⁻¹ *
        (equilibriumReferencePartition N (2 * (1 + ℓ) * β) R) ^ (1 / 2 : ℝ) *
          (∫ x : ℂ, Real.exp (-(2 * ℓ) * β * equilibriumDensityPotential R.density x)
            ∂R.measure) ^ (1 / 2 : ℝ) := by
  obtain ⟨hi, hb⟩ := equilibriumReference_gibbs_defect_moment hβ hℓ R hN
  have hp : MeasurePreserving (@WithLp.ofLp 2 (Fin N → ℂ)) (coulombMeasure N β)
      (Measure.map (@WithLp.ofLp 2 (Fin N → ℂ)) (coulombMeasure N β)) :=
    ⟨WithLp.measurable_ofLp 2 _, rfl⟩
  have hiPhysical := hp.integrable_comp_of_integrable hi
  have hIntegral := hp.integral_comp (MeasurableEquiv.toLp 2 (Fin N → ℂ)).symm.measurableEmbedding
    (fun z : Fin N → ℂ => Real.exp (-ℓ * β * equilibriumDefectEnergy R.density z))
  have hbPhysical := hIntegral.trans_le hb
  simpa only [Function.comp_def, equilibriumDefectEnergy] using And.intro hiPhysical hbPhysical

end RepulsiveCoulomb
