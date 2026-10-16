import LeanResearch.RepulsiveCoulomb.JordanSmoothTotalTurn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Topology.Instances.AddCircle.Defs

/-! Actual C¹ periodization of a closed finite-arc concatenation with matched
endpoint derivatives. Periodize its continuous derivative, then integrate it;
the period integral vanishes by the actual endpoint equality. This avoids a
smoothness certificate for a floor-function extension. Records-only candidate. -/
noncomputable section
open Set MeasureTheory
namespace RepulsiveCoulomb

def euclideanPeriodicTangent (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  AddCircle.liftIco (1 : ℝ) 0 (deriv f) (t : AddCircle (1 : ℝ))

theorem euclideanPeriodicTangent_periodic (f : ℝ → ℂ) :
    Function.Periodic (euclideanPeriodicTangent f) 1 := by
  intro t
  unfold euclideanPeriodicTangent
  rw [AddCircle.coe_add_period]

theorem euclideanPeriodicTangent_eq {f : ℝ → ℂ}
    (hjet : deriv f 0 = deriv f 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    euclideanPeriodicTangent f t = deriv f t := by
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  by_cases ht1 : t = 1
  · subst t
    have hp := euclideanPeriodicTangent_periodic f 0
    rw [zero_add] at hp
    rw [hp]
    unfold euclideanPeriodicTangent
    rw [AddCircle.liftIco_zero_coe_apply (by norm_num), hjet]
  · exact AddCircle.liftIco_zero_coe_apply ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩

theorem euclideanPeriodicTangent_continuous {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hjet : deriv f 0 = deriv f 1) : Continuous (euclideanPeriodicTangent f) := by
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  exact (AddCircle.liftIco_zero_continuous hjet hf.continuous_deriv_one.continuousOn).comp
    (AddCircle.continuous_mk' (1 : ℝ))

def euclideanC1Periodize (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  f 0 + ∫ s in (0 : ℝ)..t, euclideanPeriodicTangent f s

theorem euclideanC1Periodize_hasDerivAt {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hjet : deriv f 0 = deriv f 1) (t : ℝ) :
    HasDerivAt (euclideanC1Periodize f) (euclideanPeriodicTangent f t) t := by
  change HasDerivAt (fun u => f 0 + ∫ s in (0 : ℝ)..u, euclideanPeriodicTangent f s)
    (euclideanPeriodicTangent f t) t
  have h := (hasDerivAt_const t (f 0)).fun_add
    ((euclideanPeriodicTangent_continuous hf hjet).integral_hasStrictDerivAt 0 t).hasDerivAt
  simpa only [zero_add] using h

theorem euclideanC1Periodize_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hjet : deriv f 0 = deriv f 1) (t : ℝ) :
    deriv (euclideanC1Periodize f) t = euclideanPeriodicTangent f t :=
  (euclideanC1Periodize_hasDerivAt hf hjet t).deriv

theorem euclideanC1Periodize_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hjet : deriv f 0 = deriv f 1) : ContDiff ℝ 1 (euclideanC1Periodize f) := by
  apply contDiff_one_iff_deriv.mpr
  constructor
  · exact fun t => (euclideanC1Periodize_hasDerivAt hf hjet t).differentiableAt
  · have heq : deriv (euclideanC1Periodize f) = euclideanPeriodicTangent f :=
      funext (euclideanC1Periodize_deriv hf hjet)
    rw [heq]
    exact euclideanPeriodicTangent_continuous hf hjet

/-- Exact agreement, not merely equal image, on the original standard interval. -/
theorem euclideanC1Periodize_eq {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hjet : deriv f 0 = deriv f 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    euclideanC1Periodize f t = f t := by
  have heq : ∫ s in (0 : ℝ)..t, euclideanPeriodicTangent f s = ∫ s in (0 : ℝ)..t, deriv f s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact euclideanPeriodicTangent_eq hjet ⟨hs.1, hs.2.trans ht.2⟩
  rw [euclideanC1Periodize, heq,
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc hf.contDiffOn]
  abel

theorem euclideanC1Periodize_periodic {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hclose : f 0 = f 1) (hjet : deriv f 0 = deriv f 1) :
    Function.Periodic (euclideanC1Periodize f) 1 := by
  have hc := euclideanPeriodicTangent_continuous hf hjet
  have hzero : ∫ s in (0 : ℝ)..1, euclideanPeriodicTangent f s = 0 := by
    have h := euclideanC1Periodize_eq hf hjet (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
    unfold euclideanC1Periodize at h
    rw [← hclose] at h
    exact add_left_cancel (by simpa using h :
      f 0 + (∫ s in (0 : ℝ)..1, euclideanPeriodicTangent f s) = f 0 + 0)
  intro t
  unfold euclideanC1Periodize
  rw [(euclideanPeriodicTangent_periodic f).intervalIntegral_add_eq_add 0 t
    (fun a b => hc.intervalIntegrable a b)]
  simp only [zero_add, hzero, add_zero]

/-- The smooth total-turn theorem now applies directly to an actual closed
regular C¹ concatenation, without asking for a periodic parametrization. -/
theorem regular_closed_C1_arc_total_turn
    {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hclose : f 0 = f 1) (hjet : deriv f 0 = deriv f 1)
    (hinj : InjOn f (Ico (0 : ℝ) 1))
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, deriv f t ≠ 0)
    {θ : Icc (0 : ℝ) 1 → ℝ} (hθ : Continuous θ)
    (hlift : ∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
      deriv f t / (‖deriv f t‖ : ℂ)) :
    θ 1 - θ 0 = 2 * Real.pi ∨ θ 1 - θ 0 = -(2 * Real.pi) := by
  have hper := euclideanC1Periodize_periodic hf hclose hjet
  have hderiv (t : Icc (0 : ℝ) 1) : deriv (euclideanC1Periodize f) t = deriv f t := by
    rw [euclideanC1Periodize_deriv hf hjet, euclideanPeriodicTangent_eq hjet t.2]
  apply regular_simple_periodic_loop_total_turn
    (euclideanC1Periodize_contDiff hf hjet) hper
  · intro s hs t ht h
    apply hinj hs ht
    simpa only [euclideanC1Periodize_eq hf hjet (Ico_subset_Icc_self hs),
      euclideanC1Periodize_eq hf hjet (Ico_subset_Icc_self ht)] using h
  · intro t ht
    rw [euclideanC1Periodize_deriv hf hjet, euclideanPeriodicTangent_eq hjet ht]
    exact hreg t ht
  · exact hθ
  · intro t
    rw [hderiv]
    exact hlift t

end RepulsiveCoulomb
