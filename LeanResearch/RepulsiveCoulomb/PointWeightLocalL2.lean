import LeanResearch.RepulsiveCoulomb.PointWeightRegularity
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! Quantitative local L2 restriction for the actual point-weighted measure.
The compact-set lower density bound is used only locally. In particular this
map does not treat the weighted measure as an additive Haar measure.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem pointMeasure_volume_restrict_le {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {K s : Set ℂ} (hK : IsCompact K) (havoid : K ⊆ (pointPunctures a y)ᶜ)
    (hs : s ⊆ K) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ volume.restrict s ≤ C • pointMeasure γ a y := by
  obtain ⟨c, D, hc, hD, hlo, hhi⟩ := pointMeasure_restrict_comparison hγ ha y hK havoid
  have hc0 : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hc)
  refine ⟨(ENNReal.ofReal c)⁻¹, ENNReal.inv_ne_top.mpr hc0, ?_⟩
  have hreverse : volume.restrict K ≤ (ENNReal.ofReal c)⁻¹ •
      (pointMeasure γ a y).restrict K := by
    have h := smul_le_smul_left (ENNReal.ofReal c)⁻¹ hlo
    simpa only [smul_smul, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_smul] using h
  exact (Measure.restrict_mono_set _ hs).trans
    (hreverse.trans (smul_le_smul_left _ Measure.restrict_le_self))

/-- The same function, now as a local Lebesgue L2 class. -/
def pointL2RestrictToVolume {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {K s : Set ℂ} (hK : IsCompact K) (havoid : K ⊆ (pointPunctures a y)ᶜ)
    (hs : s ⊆ K) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Lp F 2 (pointMeasure γ a y) →L[ℝ] Lp F 2 (volume.restrict s) :=
  Lp.LpToLpOfMeasureLeSMul
    (pointMeasure_volume_restrict_le hγ ha y hK havoid hs).choose_spec.1
    (pointMeasure_volume_restrict_le hγ ha y hK havoid hs).choose_spec.2

theorem pointL2RestrictToVolume_coe {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {K s : Set ℂ} (hK : IsCompact K) (havoid : K ⊆ (pointPunctures a y)ᶜ)
    (hs : s ⊆ K) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Lp F 2 (pointMeasure γ a y)) :
    pointL2RestrictToVolume hγ ha y hK havoid hs F f =ᵐ[volume.restrict s] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f

/-- A finite quantitative bound, uniform over the two functions, for local
convergence. Its constant may depend on this configuration and compact set. -/
theorem pointL2RestrictToVolume_bound {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {K s : Set ℂ} (hK : IsCompact K) (havoid : K ⊆ (pointPunctures a y)ᶜ)
    (hs : s ⊆ K) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : Lp F 2 (pointMeasure γ a y),
      ‖pointL2RestrictToVolume hγ ha y hK havoid hs F f -
        pointL2RestrictToVolume hγ ha y hK havoid hs F g‖ ≤ C * ‖f - g‖ := by
  let T := pointL2RestrictToVolume hγ ha y hK havoid hs F
  refine ⟨‖T‖, norm_nonneg _, ?_⟩
  intro f g
  simpa only [map_sub] using T.le_opNorm (f - g)

theorem pointL2RestrictToVolume_tendsto {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {K s : Set ℂ} (hK : IsCompact K) (havoid : K ⊆ (pointPunctures a y)ᶜ)
    (hs : s ⊆ K) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℕ → Lp F 2 (pointMeasure γ a y)} {g : Lp F 2 (pointMeasure γ a y)}
    (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n ↦ pointL2RestrictToVolume hγ ha y hK havoid hs F (f n)) atTop
      (𝓝 (pointL2RestrictToVolume hγ ha y hK havoid hs F g)) :=
  ((pointL2RestrictToVolume hγ ha y hK havoid hs F).continuous.tendsto g).comp hf

end RepulsiveCoulomb
