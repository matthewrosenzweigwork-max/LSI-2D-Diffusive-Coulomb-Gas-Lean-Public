import LeanResearch.RepulsiveCoulomb.EquilibriumBranchNelsonTailAlgebra
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! The actual Markov transfer from a proved canonical error moment to the
Boltzmann tail event. It uses genuine ENNReal probability measures and the
radius exp(-s/T); no exponential-tail or partition estimate is assumed. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

/-- This adapter is to be supplied with the moment obtained from the generic
centered correlation theorem and ErrorMomentTransfer. The exact (2T/s)^p
factor is retained. -/
theorem equilibriumReference_nelson_markov {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N)
    {T t s : ℝ} (hT : 0 < T) (ht : 0 ≤ t) (htT : t ≤ T) (hs : 0 < s)
    (p : ℕ) {M : ℝ}
    (herror : Integrable (fun z : Fin N → ℂ =>
      |equilibriumModulatedEnergy R.density z -
        equilibriumRegularizedModulatedEnergy (equilibriumNelsonRadius T s) R z| ^ p)
      (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))))
    (hM : (∫ z : Fin N → ℂ,
      |equilibriumModulatedEnergy R.density z -
        equilibriumRegularizedModulatedEnergy (equilibriumNelsonRadius T s) R z| ^ p
      ∂Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))) ≤ M) :
    (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ)))
      {z : Fin N → ℂ | s < -t * equilibriumModulatedEnergy R.density z} ≤
      ENNReal.ofReal (((2 * T) / s) ^ p * M) := by
  let P := Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))
  let D : (Fin N → ℂ) → ℝ := fun z =>
    |equilibriumModulatedEnergy R.density z -
      equilibriumRegularizedModulatedEnergy (equilibriumNelsonRadius T s) R z| ^ p
  let a : ℝ := (s / (2 * T)) ^ p
  have ha : 0 < a := pow_pos (div_pos hs (by positivity)) _
  have hD0 (z : Fin N → ℂ) : 0 ≤ D z := pow_nonneg (abs_nonneg _) _
  have hsubset : {z : Fin N → ℂ | s < -t * equilibriumModulatedEnergy R.density z} ⊆
      {z : Fin N → ℂ | ENNReal.ofReal a ≤ ENNReal.ofReal (D z)} := by
    intro z hz
    have h := equilibriumReference_nelson_event_inclusion hβ R hN hT ht htT hs.le hz
    change ENNReal.ofReal a ≤ ENNReal.ofReal (D z)
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_left₀ (div_pos hs (by positivity : 0 < 2 * T)).le h.le p
  have hmarkov := meas_ge_le_lintegral_div herror.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top
  have hline : (∫⁻ z, ENNReal.ofReal (D z) ∂P) = ENNReal.ofReal (∫ z, D z ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal herror (Eventually.of_forall hD0)).symm
  have hratio : M / (s / (2 * T)) ^ p = ((2 * T) / s) ^ p * M := by
    rw [div_pow, div_pow]
    field_simp [hs.ne', hT.ne']
  calc
    P {z : Fin N → ℂ | s < -t * equilibriumModulatedEnergy R.density z} ≤
        P {z : Fin N → ℂ | ENNReal.ofReal a ≤ ENNReal.ofReal (D z)} := measure_mono hsubset
    _ ≤ (∫⁻ z, ENNReal.ofReal (D z) ∂P) / ENNReal.ofReal a := hmarkov
    _ = ENNReal.ofReal (∫ z, D z ∂P) / ENNReal.ofReal a := by rw [hline]
    _ ≤ ENNReal.ofReal M / ENNReal.ofReal a :=
      ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hM) _
    _ = ENNReal.ofReal (M / a) := (ENNReal.ofReal_div_of_pos ha).symm
    _ = _ := by
      change ENNReal.ofReal (M / (s / (2 * T)) ^ p) = _
      rw [hratio]

end RepulsiveCoulomb
