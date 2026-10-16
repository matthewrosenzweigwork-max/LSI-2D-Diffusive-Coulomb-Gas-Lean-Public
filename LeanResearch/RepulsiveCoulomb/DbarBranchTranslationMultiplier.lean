module

public import LeanResearch.RepulsiveCoulomb.DbarBranchLpMollifier
public import Mathlib.MeasureTheory.Function.Holder

@[expose] public section

/-! Actual fixed multiplication operators and their commutators with strongly
continuous Lebesgue-L2 translations. These are ingredients for a simultaneous
first-order Friedrichs argument, not a graph-approximation assumption. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

def dbarVolumeMulL {N : ℕ} {A : CoulombConfig N → ℂ}
    (hA : MemLp A ⊤ (volume : Measure (CoulombConfig N))) :
    Lp ℂ 2 (volume : Measure (CoulombConfig N)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (CoulombConfig N)) :=
  (ContinuousLinearMap.mul ℝ ℂ).holderL volume ⊤ 2 2 (hA.toLp A)

theorem dbarVolumeMulL_coe {N : ℕ} {A : CoulombConfig N → ℂ}
    (hA : MemLp A ⊤ (volume : Measure (CoulombConfig N)))
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    dbarVolumeMulL hA f =ᵐ[volume] fun x => A x * f x := by
  filter_upwards [(ContinuousLinearMap.mul ℝ ℂ).coeFn_holder (r := 2) (hA.toLp A) f,
    hA.coeFn_toLp] with x hx hAx
  change ((ContinuousLinearMap.mul ℝ ℂ).holder 2 (hA.toLp A) f) x = _
  rw [hx, hAx]
  rfl

theorem dbarVolumeMulL_norm_le {N : ℕ} {A : CoulombConfig N → ℂ}
    (hA : MemLp A ⊤ (volume : Measure (CoulombConfig N))) {C : ℝ}
    (hC : ∀ᵐ x ∂volume, ‖A x‖ ≤ C)
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    ‖dbarVolumeMulL hA f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [dbarVolumeMulL_coe hA f, hC] with x hx hCx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hCx (norm_nonneg _)

def dbarVolumeTranslationComm {N : ℕ} {A : CoulombConfig N → ℂ}
    (hA : MemLp A ⊤ (volume : Measure (CoulombConfig N))) (t : CoulombConfig N) :
    Lp ℂ 2 (volume : Measure (CoulombConfig N)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (CoulombConfig N)) :=
  (dbarVolumeMulL hA).comp (Measure.translateLp (F := ℂ) volume 2 t).toLinearIsometry.toContinuousLinearMap -
    (Measure.translateLp (F := ℂ) volume 2 t).toLinearIsometry.toContinuousLinearMap.comp (dbarVolumeMulL hA)

theorem dbarVolumeTranslationComm_coe {N : ℕ} {A : CoulombConfig N → ℂ}
    (hA : MemLp A ⊤ (volume : Measure (CoulombConfig N))) (t : CoulombConfig N)
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    dbarVolumeTranslationComm hA t f =ᵐ[volume] fun x => (A x - A (x + t)) * f (x + t) := by
  filter_upwards [Lp.coeFn_sub (dbarVolumeMulL hA (Measure.translateLp volume 2 t f))
      (Measure.translateLp volume 2 t (dbarVolumeMulL hA f)),
    dbarVolumeMulL_coe hA (Measure.translateLp volume 2 t f),
    Measure.coeFn_translateLp (mu := volume) t f,
    Measure.coeFn_translateLp (mu := volume) t (dbarVolumeMulL hA f),
    (measurePreserving_add_right (volume : Measure (CoulombConfig N)) t).quasiMeasurePreserving.tendsto_ae.eventually
      (dbarVolumeMulL_coe hA f)] with x hs hM ht hMt hMx
  change (dbarVolumeMulL hA (Measure.translateLp volume 2 t f) -
    Measure.translateLp volume 2 t (dbarVolumeMulL hA f)) x = _
  simp only [hs, Pi.sub_apply, hM, ht, hMt, Function.comp_apply, hMx]
  ring

theorem dbarVolumeTranslationComm_continuous {N : ℕ} {A : CoulombConfig N → ℂ}
    (hA : MemLp A ⊤ (volume : Measure (CoulombConfig N)))
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    Continuous (fun t => dbarVolumeTranslationComm hA t f) := by
  have ht : Continuous (fun t : CoulombConfig N => Measure.translateLp volume 2 t f) :=
    Measure.continuous_translateLp (mu := volume) (p := 2) (by norm_num) f
  have hMt : Continuous (fun t : CoulombConfig N =>
      Measure.translateLp volume 2 t (dbarVolumeMulL hA f)) :=
    Measure.continuous_translateLp (mu := volume) (p := 2) (by norm_num) (dbarVolumeMulL hA f)
  change Continuous (fun t : CoulombConfig N =>
    dbarVolumeMulL hA (Measure.translateLp volume 2 t f) -
      Measure.translateLp volume 2 t (dbarVolumeMulL hA f))
  exact ((dbarVolumeMulL hA).continuous.comp ht).sub hMt

theorem dbarVolumeTranslationComm_norm_le {N : ℕ} {A : CoulombConfig N → ℂ}
    (hA : MemLp A ⊤ (volume : Measure (CoulombConfig N))) {C : NNReal}
    (hLip : LipschitzWith C A) (t : CoulombConfig N)
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    ‖dbarVolumeTranslationComm hA t f‖ ≤ (C : ℝ) * ‖t‖ * ‖f‖ := by
  have hbound : ‖dbarVolumeTranslationComm hA t f‖ ≤
      ((C : ℝ) * ‖t‖) * ‖Measure.translateLp volume 2 t f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [dbarVolumeTranslationComm_coe hA t f,
      Measure.coeFn_translateLp (mu := volume) t f] with x hx ht
    rw [hx, ht, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have h := hLip.norm_sub_le x (x + t)
    have he : x - (x + t) = -t := by abel
    simpa only [he, norm_neg] using h
  simpa using hbound

theorem dbarVolumeMollifier_mul_comm_tendsto {N : ℕ} {ι : Type*} {l : Filter ι}
    {A : CoulombConfig N → ℂ} (hA : MemLp A ⊤ (volume : Measure (CoulombConfig N)))
    (ψ : ι → ContDiffBump (0 : CoulombConfig N))
    (hψ : Tendsto (fun i => (ψ i).rOut) l (𝓝 0))
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    Tendsto (fun i => dbarVolumeMulL hA (coulombVolumeLpMollify (ψ i) f) -
      coulombVolumeLpMollify (ψ i) (dbarVolumeMulL hA f)) l (𝓝 0) := by
  have h := ((dbarVolumeMulL hA).continuous.tendsto (f : Lp ℂ 2 volume) |>.comp
    (coulombVolumeLpMollify_tendsto ψ hψ f)).sub
    (coulombVolumeLpMollify_tendsto ψ hψ (dbarVolumeMulL hA f))
  simpa only [Function.comp_def, Pi.sub_apply, sub_self] using h

end RepulsiveCoulomb
