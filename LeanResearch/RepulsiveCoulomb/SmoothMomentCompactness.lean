import LeanResearch.RepulsiveCoulomb.QuadraticMomentTightness
import LeanResearch.RepulsiveCoulomb.Imported.TauCeti.MeasureTheory.Function.Lp.Translation

/-! Global L2 compactness for an actual smooth family with uniform mass,
derivative and integrable quadratic-moment bounds. No Poincare input. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace RepulsiveCoulomb

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem repulsive_smooth_moment_compactness (f : ι → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (hLp : ∀ i, MemLp (f i) 2 μ)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hval : ∀ i, eLpNorm (f i) 2 μ ≤ ENNReal.ofReal B)
    (hder : ∀ i, eLpNorm (fderiv ℝ (f i)) 2 μ ≤ ENNReal.ofReal B)
    (hm : ∀ i, Integrable (fun x => ‖x‖ ^ 2 * f i x ^ 2) μ)
    (hbound : ∀ i, (∫ x, ‖x‖ ^ 2 * f i x ^ 2 ∂μ) ≤ C) :
    IsCompact (closure (range (fun i => (hLp i).toLp (f i)))) := by
  classical
  let V : ι → Lp ℝ 2 μ := fun i => (hLp i).toLp (f i)
  have hV (i : ι) : V i =ᵐ[μ] f i := (hLp i).coeFn_toLp
  have ht : UnifTight (fun i => (V i : E → ℝ)) 2 μ :=
    (repulsive_unifTight_of_quadratic_moment f hC hLp hm hbound).aeeq
      (fun i => (hV i).symm)
  apply TauCeti.isCompact_closure_of_comp_add_sub_of_unifTight (M := ENNReal.ofReal B)
    (by norm_num : (2 : ENNReal) ≠ ⊤) ENNReal.ofReal_ne_top
  · rintro u ⟨i, rfl⟩
    exact (eLpNorm_congr_ae (hV i)).le.trans (hval i)
  · intro ε hε
    by_cases htop : ε = ⊤
    · refine ⟨1, by norm_num, fun u hu h hh => ?_⟩
      rw [htop]
      exact le_top
    have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    refine ⟨ε.toReal / (B + 1), div_pos he (by linarith), ?_⟩
    rintro u ⟨i, rfl⟩ h hh
    have ha := (hV i).comp_tendsto
      (measurePreserving_add_right μ h).quasiMeasurePreserving.tendsto_ae
    have hrep : (fun x => V i (x + h) - V i x) =ᵐ[μ] fun x => f i (x + h) - f i x := by
      filter_upwards [hV i, ha] with x hx hxh
      simp only [Function.comp_apply] at hxh
      rw [hx, hxh]
    rw [eLpNorm_congr_ae hrep]
    have hraw := TauCeti.eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv (mu := μ)
      (hf i) (by norm_num : (1 : ENNReal) ≤ 2) (by norm_num : (2 : ENNReal) ≠ ⊤) h
    have hnum : ‖h‖ * B ≤ ε.toReal := by
      have hh' := (lt_div_iff₀ (show 0 < B + 1 by linarith)).mp hh
      nlinarith only [hh', norm_nonneg h]
    calc
      _ ≤ ‖h‖ₑ * eLpNorm (fderiv ℝ (f i)) 2 μ := hraw
      _ ≤ ‖h‖ₑ * ENNReal.ofReal B := mul_le_mul le_rfl (hder i) (by positivity) (by positivity)
      _ = ENNReal.ofReal (‖h‖ * B) := by rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg h)]
      _ ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal hnum
      _ = ε := ENNReal.ofReal_toReal htop
  · intro ε hε
    obtain ⟨s, hs, ht'⟩ := ht ε hε
    refine ⟨s, hs, fun u => ?_⟩
    obtain ⟨i, hi⟩ := u.property
    change V i = (u : Lp ℝ 2 μ) at hi
    change eLpNorm (sᶜ.indicator ((u : Lp ℝ 2 μ) : E → ℝ)) 2 μ ≤ ε
    rw [← hi]
    exact ht' i

end RepulsiveCoulomb
