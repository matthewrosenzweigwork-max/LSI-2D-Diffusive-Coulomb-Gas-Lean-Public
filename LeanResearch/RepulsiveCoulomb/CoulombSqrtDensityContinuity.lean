module

public import LeanResearch.RepulsiveCoulomb.CoulombDensityTemperatureBound

@[expose] public section

/-! Strong-L2 content of continuity for the actual normalized square-root
Gibbs densities at every positive temperature. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombDensity_integrable (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Integrable (coulombDensity N β) :=
  (coulombWeight_integrable (N := N) hβ).const_mul _

theorem coulombSqrtDensity_memLp (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    MemLp (fun z : CoulombConfig N => Real.sqrt (coulombDensity N β z)) 2 volume := by
  apply (memLp_two_iff_integrable_sq
    (coulombDensity_continuous hβ.le).sqrt.aestronglyMeasurable).mpr
  simpa only [Real.sq_sqrt (coulombDensity_nonneg β _)] using coulombDensity_integrable N hβ

theorem coulombSqrtDensity_squareDifference_tendsto {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun γ : ℝ => ∫ z : CoulombConfig N,
      (Real.sqrt (coulombDensity N γ z) - Real.sqrt (coulombDensity N β z)) ^ 2) (𝓝 β) (𝓝 0) := by
  have hn := coulombDensity_eventually_temperatureBound (N := N) hβ
  have hc : ContinuousAt (fun γ : ℝ => ∫ z : CoulombConfig N,
      (Real.sqrt (coulombDensity N γ z) - Real.sqrt (coulombDensity N β z)) ^ 2) β := by
    apply continuousAt_of_dominated
      (bound := fun z => 4 * coulombDensityTemperatureBound N β z)
    · filter_upwards [hn] with γ hγ
      exact (((coulombDensity_continuous hγ.1.le).sqrt.sub
        (coulombDensity_continuous hβ.le).sqrt).pow 2).aestronglyMeasurable
    · filter_upwards [hn] with γ hγ
      exact Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hg := hγ.2 z
        have hb := coulombDensity_self_temperatureBound hβ z
        have hsg := Real.sq_sqrt (coulombDensity_nonneg γ z)
        have hsb := Real.sq_sqrt (coulombDensity_nonneg β z)
        nlinarith [sq_nonneg (Real.sqrt (coulombDensity N γ z) + Real.sqrt (coulombDensity N β z))]
    · exact (coulombDensityTemperatureBound_integrable N hβ).const_mul 4
    · filter_upwards [coulombDomain_ae N] with z hz
      exact (((coulombDensity_temperature_continuousAt hβ hz).sqrt).sub continuousAt_const).pow 2
  simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), integral_zero] using hc.tendsto

end RepulsiveCoulomb
