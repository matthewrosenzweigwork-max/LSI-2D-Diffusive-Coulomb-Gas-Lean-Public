import LeanResearch.RepulsiveCoulomb.CoulombTemperatureNormalization

/-! An actual integrable local-in-temperature bound for normalized densities. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

def coulombDensityTemperatureBound (N : ℕ) (β : ℝ) (z : CoulombConfig N) : ℝ :=
  (2 / (∫ x : CoulombConfig N, coulombWeight β x)) *
    coulombTemperatureMajorant N (β / 2) (2 * β) z

theorem coulombDensityTemperatureBound_integrable (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Integrable (coulombDensityTemperatureBound N β) :=
  (coulombTemperatureMajorant_integrable N (by positivity) (2 * β)).const_mul _

theorem coulombDensity_le_temperatureBound {N : ℕ} {β γ : ℝ} (hβ : 0 < β)
    (hγ : γ ∈ Icc (β / 2) (2 * β))
    (hZ : (∫ x : CoulombConfig N, coulombWeight β x) / 2 ≤
      ∫ x : CoulombConfig N, coulombWeight γ x) (z : CoulombConfig N) :
    coulombDensity N γ z ≤ coulombDensityTemperatureBound N β z := by
  have hp := coulombWeight_integral_pos (N := N) hβ
  have hγp : 0 < γ := by linarith [hγ.1]
  have hq := coulombWeight_integral_pos (N := N) hγp
  have hi : (∫ x : CoulombConfig N, coulombWeight γ x)⁻¹ ≤
      2 / (∫ x : CoulombConfig N, coulombWeight β x) := by
    simpa only [inv_div] using (inv_le_inv₀ hq (show 0 < (∫ x : CoulombConfig N, coulombWeight β x) / 2 by positivity)).mpr hZ
  exact mul_le_mul hi
    (coulombWeight_le_temperatureMajorant (by positivity) hγ.1 hγ.2 z)
    (coulombWeight_nonneg γ z) (by positivity)

theorem coulombDensity_eventually_temperatureBound {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ γ in 𝓝 β, 0 < γ ∧ ∀ z : CoulombConfig N,
      coulombDensity N γ z ≤ coulombDensityTemperatureBound N β z := by
  have hp := coulombWeight_integral_pos (N := N) hβ
  have hn : ∀ᶠ γ in 𝓝 β, γ ∈ Icc (β / 2) (2 * β) :=
    Icc_mem_nhds (by linarith) (by linarith)
  have hZ : ∀ᶠ γ in 𝓝 β, (∫ x : CoulombConfig N, coulombWeight β x) / 2 <
      ∫ x : CoulombConfig N, coulombWeight γ x :=
    (coulombWeightIntegral_temperature_continuousAt hβ).eventually (lt_mem_nhds (by linarith))
  filter_upwards [hn, hZ] with γ hγ hz
  exact ⟨by linarith [hγ.1], fun z => coulombDensity_le_temperatureBound hβ hγ hz.le z⟩

theorem coulombDensity_self_temperatureBound {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (z : CoulombConfig N) : coulombDensity N β z ≤ coulombDensityTemperatureBound N β z := by
  have hp := coulombWeight_integral_pos (N := N) hβ
  exact coulombDensity_le_temperatureBound hβ ⟨by linarith, by linarith⟩ (by linarith) z

end RepulsiveCoulomb
