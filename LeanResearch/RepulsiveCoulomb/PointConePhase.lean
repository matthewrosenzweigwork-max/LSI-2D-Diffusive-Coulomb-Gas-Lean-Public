module

public import LeanResearch.RepulsiveCoulomb.PointConeChordUpper

@[expose] public section

/-! Controlled rotations of developed cone sectors and Euclidean supporting
projections. Argument windows are explicit to avoid principal-branch errors. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def conePhase (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

theorem conePhase_norm (θ : ℝ) : ‖conePhase θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

theorem conePhase_arg {θ : ℝ} (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    Complex.arg (conePhase θ) = θ := by
  have h := Complex.log_exp (x := (θ : ℂ) * Complex.I)
    (by simpa using hθ.1) (by simpa using hθ.2)
  rw [← Complex.log_im, conePhase, h]
  simp

theorem conePhase_arg_mul {θ : ℝ} (hθ : θ ∈ Ioc (-Real.pi) Real.pi) {z : ℂ} (hz : z ≠ 0)
    (harg : θ + Complex.arg z ∈ Ioc (-Real.pi) Real.pi) :
    Complex.arg (conePhase θ * z) = θ + Complex.arg z := by
  have hc : conePhase θ ≠ 0 := Complex.exp_ne_zero _
  rw [Complex.arg_mul hc hz (by rwa [conePhase_arg hθ]), conePhase_arg hθ]

theorem pointConeSectorMap_phase {α θ : ℝ} (hθ : θ ∈ Ioc (-Real.pi) Real.pi)
    {z : ℂ} (hz : z ≠ 0) (harg : θ + Complex.arg z ∈ Ioc (-Real.pi) Real.pi) :
    pointConeSectorMap α (conePhase θ * z) = conePhase (θ * (α + 1)) * pointConeSectorMap α z := by
  have hc : conePhase θ ≠ 0 := Complex.exp_ne_zero _
  have hl := Complex.log_mul hc hz (by rwa [conePhase_arg hθ])
  have hlc : Complex.log (conePhase θ) = (θ : ℂ) * Complex.I :=
    Complex.log_exp (by simpa using hθ.1) (by simpa using hθ.2)
  unfold pointConeSectorMap
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hc hz), hl, hlc, add_mul, Complex.exp_add,
    ← Complex.cpow_def_of_ne_zero hz]
  have he : (θ : ℂ) * Complex.I * ((α + 1 : ℝ) : ℂ) = ((θ * (α + 1) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he]
  unfold conePhase
  ring

theorem conePhase_neg_arg_mul (w : ℂ) : conePhase (-Complex.arg w) * w = (‖w‖ : ℂ) := by
  calc
    _ = conePhase (-Complex.arg w) * ((‖w‖ : ℂ) * conePhase (Complex.arg w)) := by
      exact congrArg (fun v : ℂ ↦ conePhase (-Complex.arg w) * v) (Complex.norm_mul_exp_arg_mul_I w).symm
    _ = (‖w‖ : ℂ) := by
      unfold conePhase
      rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg]
      field_simp

theorem exists_cone_halfplane_projection (w : ℂ) :
    ∃ β : ℝ, |β| ≤ Real.pi / 2 ∧ |(conePhase (-β) * w).re| = ‖w‖ := by
  have hproj (v : ℂ) (hv : 0 ≤ v.re) :
      |Complex.arg v| ≤ Real.pi / 2 ∧ |(conePhase (-Complex.arg v) * v).re| = ‖v‖ := by
    refine ⟨Complex.abs_arg_le_pi_div_two_iff.mpr hv, ?_⟩
    rw [conePhase_neg_arg_mul, Complex.ofReal_re, abs_of_nonneg (norm_nonneg _)]
  by_cases hw : 0 ≤ w.re
  · exact ⟨Complex.arg w, hproj w hw⟩
  · refine ⟨Complex.arg (-w), ?_⟩
    simpa only [mul_neg, Complex.neg_re, abs_neg, norm_neg] using
      hproj (-w) (by simp only [Complex.neg_re]; linarith)

end RepulsiveCoulomb
