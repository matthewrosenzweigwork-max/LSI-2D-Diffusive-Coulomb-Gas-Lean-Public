module

public import LeanResearch.RepulsiveCoulomb.WeightedAverageComparison

@[expose] public section

/-! Correct L1 centering for a finite positive restriction, in normalized form. -/
noncomputable section
open Set MeasureTheory Filter
namespace RepulsiveCoulomb

theorem setAverage_norm_centered_le_twice {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {S : Set X} (hS0 : μ S ≠ 0) (hSfin : μ S ≠ ⊤)
    {f : X → ℝ} (hf : IntegrableOn f S μ) (c : ℝ) :
    (⨍ x in S, ‖f x - (⨍ y in S, f y ∂μ)‖ ∂μ) ≤ 2 * ⨍ x in S, ‖f x - c‖ ∂μ := by
  let A := ⨍ y in S, f y ∂μ
  have hleft : IntegrableOn (fun x => ‖f x - A‖) S μ := (hf.sub (integrableOn_const hSfin)).norm
  have hright : IntegrableOn (fun x => ‖f x - c‖) S μ := (hf.sub (integrableOn_const hSfin)).norm
  have hconst : IntegrableOn (fun _ : X => ‖A - c‖) S μ := integrableOn_const hSfin
  have hpoint (x : X) : ‖f x - A‖ ≤ ‖f x - c‖ + ‖A - c‖ := by
    simpa only [sub_sub_sub_cancel_right] using norm_sub_le (f x - c) (A - c)
  have h := setAverage_mono_ae_real μ hleft (hright.add hconst) (Eventually.of_forall hpoint)
  simp only [Pi.add_apply] at h
  rw [setAverage_fun_add hright hconst, setAverage_const hS0 hSfin] at h
  have hmean := norm_setAverage_sub_const_le μ hS0 hSfin hf c
  change (⨍ x in S, ‖f x - A‖ ∂μ) ≤ _
  change ‖A - c‖ ≤ _ at hmean
  linarith

end RepulsiveCoulomb
