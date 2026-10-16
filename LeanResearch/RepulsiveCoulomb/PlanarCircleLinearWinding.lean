import LeanResearch.RepulsiveCoulomb.JordanArgumentHomotopy
import LeanResearch.RepulsiveCoulomb.ComplexLinearJacobianBounds

/-!
Actual circles and signed winding of invertible real-linear maps of the plane.
Winding is expressed by the increment of a continuous real argument lift.
The linear calculation contracts the smaller of the complex-linear and
antilinear summands; it does not assume a degree/determinant identification.
Records-only candidate: not compiled or accepted.
-/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- A genuine continuous argument of the actual normalized vector loop. -/
def PlanarArgumentLift (v : Icc (0 : ℝ) 1 → ℂ) (θ : Icc (0 : ℝ) 1 → ℝ) : Prop :=
  Continuous θ ∧ ∀ t, Complex.exp ((θ t : ℂ) * Complex.I) = v t / (‖v t‖ : ℂ)

/-- Radius `r`, with angular speed `σ * 2π`. The positive actual circle uses `σ=1`. -/
def planarSignedCircleVector (r σ : ℝ) (t : Icc (0 : ℝ) 1) : ℂ :=
  (r : ℂ) * (Circle.exp (σ * (2 * Real.pi * (t : ℝ))) : ℂ)

abbrev planarCircleVector (r : ℝ) := planarSignedCircleVector r 1

theorem planarSignedCircleVector_continuous (r σ : ℝ) :
    Continuous (planarSignedCircleVector r σ) := by
  unfold planarSignedCircleVector
  change Continuous (fun t : Icc (0 : ℝ) 1 =>
    (r : ℂ) * Complex.exp (((σ * (2 * Real.pi * (t : ℝ)) : ℝ) : ℂ) * Complex.I))
  fun_prop

theorem planarSignedCircleVector_norm {r : ℝ} (hr : 0 ≤ r) (σ : ℝ)
    (t : Icc (0 : ℝ) 1) : ‖planarSignedCircleVector r σ t‖ = r := by
  rw [planarSignedCircleVector, norm_mul, Circle.norm_coe, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

theorem planarCircleVector_closed (r : ℝ) :
    planarCircleVector r 0 = planarCircleVector r 1 := by
  simp [planarCircleVector, planarSignedCircleVector]

theorem planarCircleVector_conj (r : ℝ) (t : Icc (0 : ℝ) 1) :
    star (planarCircleVector r t) = planarSignedCircleVector r (-1) t := by
  simp only [planarCircleVector, planarSignedCircleVector, one_mul, neg_one_mul,
    Complex.star_def, map_mul, Complex.conj_ofReal, Circle.exp_neg,
    Circle.coe_inv_eq_conj]

/-- Pointwise nonvanishing for the explicit straight contraction of a dominated
perturbation. This is the entire avoidance estimate used below. -/
theorem planar_add_small_smul_ne_zero {x y : ℂ} (hsmall : ‖y‖ < ‖x‖)
    (s : Icc (0 : ℝ) 1) : x + (1 - (s : ℝ)) • y ≠ 0 := by
  intro hz
  have heq : x = -((1 - (s : ℝ)) • y) := eq_neg_of_add_eq_zero_left hz
  have hnonneg : 0 ≤ 1 - (s : ℝ) := sub_nonneg.mpr s.2.2
  have hle : 1 - (s : ℝ) ≤ 1 := by linarith [s.2.1]
  have hnorm : ‖x‖ ≤ ‖y‖ := by
    rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact (mul_le_mul_of_nonneg_right hle (norm_nonneg y)).trans_eq (one_mul _)
  exact (not_lt_of_ge hnorm) hsmall

/-- Actual argument increments are unchanged by deleting a pointwise dominated
continuous perturbation. The square homotopy is constructed, not supplied. -/
theorem planar_argument_increment_add_small
    (v w : Icc (0 : ℝ) 1 → ℂ) (hv : Continuous v) (hw : Continuous w)
    (hvc : v 0 = v 1) (hwc : w 0 = w 1) (hsmall : ∀ t, ‖w t‖ < ‖v t‖)
    {θ ψ : Icc (0 : ℝ) 1 → ℝ}
    (hθ : PlanarArgumentLift (fun t => v t + w t) θ)
    (hψ : PlanarArgumentLift v ψ) : θ 1 - θ 0 = ψ 1 - ψ 0 := by
  let H : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → ℂ :=
    fun q => v q.2 + (1 - (q.1 : ℝ)) • w q.2
  have hH : Continuous H :=
    (hv.comp continuous_snd).add
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (hw.comp continuous_snd))
  apply closed_vector_loop_argument_homotopy H hH
    (fun q => planar_add_small_smul_ne_zero (hsmall q.2) q.1)
    (fun s => by simp only [H, hvc, hwc]) θ ψ hθ.1 hψ.1
  · intro t
    simpa [H] using hθ.2 t
  · intro t
    simpa [H] using hψ.2 t

/-- Explicit argument lift of a nonzero complex multiple of an actual circle. -/
theorem planarSignedCircleVector_mul_lift {r : ℝ} (hr : 0 < r)
    {c : ℂ} (hc : c ≠ 0) (σ : ℝ) :
    PlanarArgumentLift (fun t => c * planarSignedCircleVector r σ t)
      (fun t => Complex.arg c + σ * (2 * Real.pi * (t : ℝ))) := by
  refine ⟨by fun_prop, fun t => ?_⟩
  have he : Complex.exp ((Complex.arg c : ℂ) * Complex.I) = c / (‖c‖ : ℂ) := by
    have h := Circle.exp_arg (euclideanDirection c hc)
    rw [euclideanDirection_arg] at h
    exact congrArg (fun z : Circle => (z : ℂ)) h
  have hn : ‖c * planarSignedCircleVector r σ t‖ = ‖c‖ * r := by
    rw [norm_mul, planarSignedCircleVector_norm hr.le]
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, he, hn]
  change c / (‖c‖ : ℂ) * (Circle.exp (σ * (2 * Real.pi * (t : ℝ))) : ℂ) = _
  simp only [planarSignedCircleVector, Complex.ofReal_mul]
  field_simp [Complex.ofReal_ne_zero.mpr hr.ne',
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hc)] <;> ring

/-- The actual complex-linear coefficient of a real-linear plane map. -/
def planarLinearPart (A : ℂ →ₗ[ℝ] ℂ) : ℂ := (A 1 - Complex.I * A Complex.I) / 2

/-- The actual conjugate-linear coefficient of a real-linear plane map. -/
def planarAntilinearPart (A : ℂ →ₗ[ℝ] ℂ) : ℂ := (A 1 + Complex.I * A Complex.I) / 2

theorem planar_realLinear_decomposition (A : ℂ →ₗ[ℝ] ℂ) (z : ℂ) :
    A z = planarLinearPart A * z + planarAntilinearPart A * star z := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
  rw [hz, map_add, map_smul, map_smul]
  simp only [planarLinearPart, planarAntilinearPart, Complex.real_smul]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.star_def] <;> ring

/-- A direct two-column computation identifies the genuine real determinant. -/
theorem planar_realLinear_det_parts (A : ℂ →ₗ[ℝ] ℂ) :
    A.det = ‖planarLinearPart A‖ ^ 2 - ‖planarAntilinearPart A‖ ^ 2 := by
  rw [complex_realLinear_det_formula, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  simp [planarLinearPart, planarAntilinearPart, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, Complex.star_def]
  <;> ring

/-- Positive determinant gives exactly one positive turn of the actual ellipse. -/
theorem planar_realLinear_circle_increment_pos (A : ℂ →L[ℝ] ℂ)
    (hdet : 0 < A.toLinearMap.det) {r : ℝ} (hr : 0 < r)
    {θ : Icc (0 : ℝ) 1 → ℝ}
    (hθ : PlanarArgumentLift (fun t => A (planarCircleVector r t)) θ) :
    θ 1 - θ 0 = 2 * Real.pi := by
  let a := planarLinearPart A.toLinearMap
  let b := planarAntilinearPart A.toLinearMap
  have hba : ‖b‖ < ‖a‖ := by
    have h := planar_realLinear_det_parts A.toLinearMap
    change A.toLinearMap.det = ‖a‖ ^ 2 - ‖b‖ ^ 2 at h
    nlinarith [norm_nonneg a, norm_nonneg b]
  have ha : a ≠ 0 := norm_pos_iff.mp ((norm_nonneg b).trans_lt hba)
  let v := fun t => a * planarCircleVector r t
  let w := fun t => b * star (planarCircleVector r t)
  have hv : Continuous v := continuous_const.mul (planarSignedCircleVector_continuous r 1)
  have hw : Continuous w := continuous_const.mul
    (planarSignedCircleVector_continuous r 1).star
  have hvw (t) : v t + w t = A (planarCircleVector r t) :=
    (planar_realLinear_decomposition A.toLinearMap _).symm
  have hθ' : PlanarArgumentLift (fun t => v t + w t) θ := by
    simpa only [hvw] using hθ
  have hψ := planarSignedCircleVector_mul_lift hr ha 1
  have hinc := planar_argument_increment_add_small v w hv hw
    (by simp only [v, planarCircleVector_closed])
    (by simp only [w, planarCircleVector_closed])
    (fun t => by
      dsimp [v, w]
      simp only [norm_mul, Complex.norm_conj, planarSignedCircleVector_norm hr.le]
      exact mul_lt_mul_of_pos_right hba hr) hθ' hψ
  simpa using hinc

/-- Negative determinant gives exactly one negative turn of the actual ellipse. -/
theorem planar_realLinear_circle_increment_neg (A : ℂ →L[ℝ] ℂ)
    (hdet : A.toLinearMap.det < 0) {r : ℝ} (hr : 0 < r)
    {θ : Icc (0 : ℝ) 1 → ℝ}
    (hθ : PlanarArgumentLift (fun t => A (planarCircleVector r t)) θ) :
    θ 1 - θ 0 = -(2 * Real.pi) := by
  let a := planarLinearPart A.toLinearMap
  let b := planarAntilinearPart A.toLinearMap
  have hab : ‖a‖ < ‖b‖ := by
    have h := planar_realLinear_det_parts A.toLinearMap
    change A.toLinearMap.det = ‖a‖ ^ 2 - ‖b‖ ^ 2 at h
    nlinarith [norm_nonneg a, norm_nonneg b]
  have hb : b ≠ 0 := norm_pos_iff.mp ((norm_nonneg a).trans_lt hab)
  let v := fun t => b * star (planarCircleVector r t)
  let w := fun t => a * planarCircleVector r t
  have hv : Continuous v := continuous_const.mul
    (planarSignedCircleVector_continuous r 1).star
  have hw : Continuous w := continuous_const.mul (planarSignedCircleVector_continuous r 1)
  have hvw (t) : v t + w t = A (planarCircleVector r t) := by
    calc
      v t + w t = w t + v t := add_comm _ _
      _ = A (planarCircleVector r t) :=
        (planar_realLinear_decomposition A.toLinearMap _).symm
  have hθ' : PlanarArgumentLift (fun t => v t + w t) θ := by
    simpa only [hvw] using hθ
  have hψ : PlanarArgumentLift v
      (fun t => Complex.arg b + (-1 : ℝ) * (2 * Real.pi * (t : ℝ))) := by
    simpa only [v, planarCircleVector_conj] using planarSignedCircleVector_mul_lift hr hb (-1)
  have hinc := planar_argument_increment_add_small v w hv hw
    (by simp only [v, planarCircleVector_closed])
    (by simp only [w, planarCircleVector_closed])
    (fun t => by
      dsimp [v, w]
      simp only [norm_mul, Complex.norm_conj, planarSignedCircleVector_norm hr.le]
      exact mul_lt_mul_of_pos_right hab hr) hθ' hψ
  simpa using hinc

/-- The winding of an invertible real-linear image of an actual positively
oriented circle is precisely the sign of its genuine determinant. -/
theorem planar_realLinear_circle_increment (A : ℂ →L[ℝ] ℂ)
    (hdet : A.toLinearMap.det ≠ 0) {r : ℝ} (hr : 0 < r)
    {θ : Icc (0 : ℝ) 1 → ℝ}
    (hθ : PlanarArgumentLift (fun t => A (planarCircleVector r t)) θ) :
    θ 1 - θ 0 = if 0 < A.toLinearMap.det then 2 * Real.pi else -(2 * Real.pi) := by
  rcases lt_or_gt_of_ne hdet with hn | hp
  · rw [if_neg (not_lt_of_ge hn.le)]
    exact planar_realLinear_circle_increment_neg A hn hr hθ
  · rw [if_pos hp]
    exact planar_realLinear_circle_increment_pos A hp hr hθ

end RepulsiveCoulomb
