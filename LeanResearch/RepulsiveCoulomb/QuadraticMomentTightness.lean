import LeanResearch.RepulsiveCoulomb.QuadraticMomentTail
import LeanResearch.RepulsiveCoulomb.Imported.TauCeti.MeasureTheory.Function.Lp.FrechetKolmogorov

/-! Actual L2 tightness from a uniformly bounded integrable quadratic moment. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem repulsive_eLpNorm_two_eq_sqrt {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ x, f x ^ 2 ∂μ)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by ring, ← Real.sqrt_eq_rpow]

theorem repulsive_unifTight_of_quadratic_moment {E ι : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    {μ : Measure E} [IsLocallyFiniteMeasure μ]
    (f : ι → E → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ i, MemLp (f i) 2 μ)
    (hm : ∀ i, Integrable (fun x => ‖x‖ ^ 2 * f i x ^ 2) μ)
    (hbound : ∀ i, (∫ x, ‖x‖ ^ 2 * f i x ^ 2 ∂μ) ≤ C) :
    UnifTight f 2 μ := by
  apply (unifTight_iff_real f 2 μ).mpr
  intro ε hε
  let R : ℝ := (Real.sqrt C + 1) / ε
  have hR : 0 < R := div_pos (by positivity) hε
  have hscale : C ≤ ε ^ 2 * R ^ 2 := by
    have hs := Real.sq_sqrt hC
    have hn := Real.sqrt_nonneg C
    have he : ε ^ 2 * R ^ 2 = (Real.sqrt C + 1) ^ 2 := by
      dsimp only [R]
      field_simp
    rw [he]
    nlinarith only [hs, hn]
  refine ⟨ball (0 : E) R, (measure_ball_lt_top (μ := μ) (x := (0 : E)) (r := R)).ne, fun i => ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.compl,
    repulsive_eLpNorm_two_eq_sqrt ((hf i).restrict ((ball (0 : E) R)ᶜ))]
  apply ENNReal.ofReal_le_ofReal
  apply (Real.sqrt_le_left hε.le).mpr
  have ht := repulsive_quadratic_moment_tail hR (f i) (hf i).integrable_sq (hm i)
  have hh := ht.trans (hbound i)
  have hpos : 0 < R ^ 2 := sq_pos_of_pos hR
  exact (mul_le_mul_iff_right₀ hpos).mp (hh.trans (by simpa only [mul_comm] using hscale))

end RepulsiveCoulomb
