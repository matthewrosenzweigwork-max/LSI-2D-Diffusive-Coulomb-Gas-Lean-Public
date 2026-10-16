module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchOnsager
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchProductCollisions

@[expose] public section

/-! Exact product-reference integrability and mean of the canonical A_N.
All off-diagonal pair laws and their logarithmic integrability are actual;
the surviving one-body correction yields E[A_N]=-c_beta/2. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators
namespace RepulsiveCoulomb

theorem equilibriumProduct_pair_measurePreserving (N : ℕ) (μ : Measure ℂ)
    [IsProbabilityMeasure μ] {i j : Fin N} (hij : i ≠ j) :
    MeasurePreserving (fun z : Fin N → ℂ => (z i, z j))
      (Measure.pi (fun _ : Fin N => μ)) (μ.prod μ) := by
  have hind := (iIndepFun_pi (μ := fun _ : Fin N => μ)
    (X := fun _ : Fin N => (id : ℂ → ℂ)) (fun _ => aemeasurable_id)).indepFun hij
  have hm := hind.map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  change Measure.map (fun z : Fin N → ℂ => (z i, z j)) (Measure.pi (fun _ : Fin N => μ)) =
    (Measure.map (Function.eval i) (Measure.pi (fun _ : Fin N => μ))).prod
      (Measure.map (Function.eval j) (Measure.pi (fun _ : Fin N => μ))) at hm
  rw [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq,
    (measurePreserving_eval (fun _ : Fin N => μ) j).map_eq] at hm
  exact ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), hm⟩

private theorem equilibrium_integral_comp_probability {α δ : Type*}
    [MeasurableSpace α] [MeasurableSpace δ] {μ : Measure α} {ν : Measure δ}
    {f : α → δ} (hf : MeasurePreserving f μ ν) {g : δ → ℝ} (hg : Measurable g) :
    (∫ x, g (f x) ∂μ) = ∫ y, g y ∂ν := by
  rw [← hf.map_eq, integral_map hf.measurable.aemeasurable hg.aestronglyMeasurable]

/-- Actual potential integrability under the constructed reference law. -/
theorem equilibriumReference_potential_measure_integrable {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) : Integrable (equilibriumDensityPotential R.density) R.measure := by
  have he : equilibriumDensityPotential R.density =
      (fun x => ∫ y : ℂ, equilibriumLogKernel (x - y) ∂R.measure) := by
    funext x
    rw [← R.density_measure]
    exact equilibriumDensityPotential_eq_measureIntegral R.smooth.continuous.measurable
      (fun y => (R.positive y).le) x
  rw [he]
  exact equilibriumObjective_finite_potential_integrable hβ R.objective_finite

theorem integral_equilibriumReference_potential {β : ℝ} (R : EquilibriumConstructedReference β) :
    (∫ x : ℂ, equilibriumDensityPotential R.density x ∂R.measure) = equilibriumDensityInteraction R.density := by
  rw [← R.density_measure, integral_equilibriumDensityMeasure R.smooth.continuous.measurable
    (fun y => (R.positive y).le)]
  unfold equilibriumDensityInteraction
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => mul_comm _ _)

/-- Both actual L1 integrability and the exact expected value hold for every
positive particle number; no exponential-integrability premise is assumed. -/
theorem equilibriumReference_modulated_integrable_mean {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) :
    Integrable (equilibriumModulatedEnergy R.density : (Fin N → ℂ) → ℝ)
      (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))) ∧
    (∫ z : Fin N → ℂ, equilibriumModulatedEnergy R.density z
      ∂Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))) = -equilibriumDensityInteraction R.density / 2 := by
  let P := Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))
  let H : Fin N → Fin N → (Fin N → ℂ) → ℝ :=
    fun i j z => if i = j then 0 else equilibriumLogKernel (z i - z j)
  have hp (i j : Fin N) : Integrable (H i j) P := by
    by_cases hij : i = j
    · simp only [H, hij, if_true]
      exact integrable_zero (Fin N → ℂ) ℝ P
    · have h := (equilibriumProduct_pair_measurePreserving N (R.measure : Measure ℂ) hij).integrable_comp_of_integrable (equilibriumObjective_finite_logEnergy_integrable hβ R.objective_finite)
      simpa only [H, hij, if_false, Function.comp_def] using h
  have hs : Integrable (fun z => ∑ i, ∑ j, H i j z) P :=
    integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hp i j))
  have hu (i : Fin N) : Integrable (fun z : Fin N → ℂ => equilibriumDensityPotential R.density (z i)) P :=
    (measurePreserving_eval (fun _ : Fin N => (R.measure : Measure ℂ)) i).integrable_comp_of_integrable (equilibriumReference_potential_measure_integrable hβ R)
  have hus := integrable_finsetSum Finset.univ (fun i _ => hu i)
  have hpi (i j : Fin N) : (∫ z, H i j z ∂P) =
      if i = j then 0 else equilibriumDensityInteraction R.density := by
    by_cases hij : i = j
    · simp only [H, hij, if_true, integral_zero]
    · simp only [H, hij, if_false]
      rw [equilibrium_integral_comp_probability
        (g := fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2))
        (equilibriumProduct_pair_measurePreserving N (R.measure : Measure ℂ) hij)
        (equilibriumLogKernel_measurable.comp (measurable_fst.sub measurable_snd)),
        equilibriumReference_measureInteraction hβ R]
  have hui (i : Fin N) : (∫ z : Fin N → ℂ, equilibriumDensityPotential R.density (z i) ∂P) =
      equilibriumDensityInteraction R.density := by
    rw [equilibrium_integral_comp_probability
      (measurePreserving_eval (fun _ : Fin N => (R.measure : Measure ℂ)) i)
      (equilibriumDensityPotential_measurable R.smooth.continuous.measurable),
      integral_equilibriumReference_potential R]
  have hsi : (∫ z, (∑ i, ∑ j, H i j z) ∂P) =
      (N : ℝ) * ((N : ℝ) - 1) * equilibriumDensityInteraction R.density := by
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hp i j))]
    simp_rw [integral_finsetSum Finset.univ (fun j _ => hp _ j), hpi]
    exact equilibriumOffDiagonal_const N _
  have husi : (∫ z : Fin N → ℂ, (∑ i, equilibriumDensityPotential R.density (z i)) ∂P) =
      (N : ℝ) * equilibriumDensityInteraction R.density := by
    rw [integral_finsetSum Finset.univ (fun i _ => hu i)]
    simp only [hui, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hA := ((hs.div_const (2 * (N : ℝ))).sub hus).add
    (integrable_const ((N : ℝ) * equilibriumDensityInteraction R.density / 2))
  refine ⟨hA, ?_⟩
  change (∫ z, ((∑ i, ∑ j, H i j z) / (2 * (N : ℝ)) -
    (∑ i, equilibriumDensityPotential R.density (z i)) +
    (N : ℝ) * equilibriumDensityInteraction R.density / 2) ∂P) = _
  have hadd := integral_add ((hs.div_const (2 * (N : ℝ))).sub hus)
    (integrable_const (μ := P) ((N : ℝ) * equilibriumDensityInteraction R.density / 2))
  have hsub := integral_sub (hs.div_const (2 * (N : ℝ))) hus
  dsimp only [Pi.add_apply, Pi.sub_apply] at hadd hsub
  rw [hadd, hsub, integral_div, hsi, husi]
  simp only [integral_const, probReal_univ, one_smul]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hn] <;> ring

end RepulsiveCoulomb
