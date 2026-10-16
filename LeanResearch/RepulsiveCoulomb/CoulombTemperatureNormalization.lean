import LeanResearch.RepulsiveCoulomb.CoulombTemperatureDomination
import LeanResearch.RepulsiveCoulomb.CoulombDensityLocal

/-! Actual finite partition and density continuity in positive temperature.
The domination is the proved common Gaussian majorant, not properness alone. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombWeight_temperature_continuous {N : ℕ} {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) : Continuous (fun β : ℝ => coulombWeight β z) := by
  have he : (fun β : ℝ => coulombWeight β z) =
      fun β : ℝ => Real.exp (-coulombPotential β z) := by
    funext β
    exact coulombWeight_eq_exp_neg_potential β hz
  rw [he]
  unfold coulombPotential
  fun_prop

theorem coulombWeightIntegral_temperature_continuousAt {N : ℕ} {β : ℝ}
    (hβ : 0 < β) :
    ContinuousAt (fun γ : ℝ => ∫ z : CoulombConfig N, coulombWeight γ z) β := by
  have hn : ∀ᶠ γ in 𝓝 β, γ ∈ Icc (β / 2) (2 * β) :=
    Icc_mem_nhds (by linarith) (by linarith)
  apply continuousAt_of_dominated
    (bound := coulombTemperatureMajorant N (β / 2) (2 * β))
  · filter_upwards [hn] with γ hγ
    exact (coulombWeight_continuous (show 0 ≤ γ by linarith [hγ.1])).aestronglyMeasurable
  · filter_upwards [hn] with γ hγ
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (coulombWeight_nonneg γ z)]
      exact coulombWeight_le_temperatureMajorant (by positivity) hγ.1 hγ.2 z
  · exact coulombTemperatureMajorant_integrable N (by positivity) _
  · filter_upwards [coulombDomain_ae N] with z hz
    exact (coulombWeight_temperature_continuous hz).continuousAt

theorem coulombDensity_temperature_continuousAt {N : ℕ} {β : ℝ}
    (hβ : 0 < β) {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    ContinuousAt (fun γ : ℝ => coulombDensity N γ z) β := by
  exact ((coulombWeightIntegral_temperature_continuousAt hβ).inv₀
    (coulombWeight_integral_pos hβ).ne').mul (coulombWeight_temperature_continuous hz).continuousAt

end RepulsiveCoulomb
