import LeanResearch.RepulsiveCoulomb.ComplexTriangleRigidity

/-!
Source-only bounded successor to the frozen three-module rigidity packet.
An actual arclength isometry of a symmetric interval through the origin, whose
image lies in the closed upper halfplane, has real coordinate +t or -t.
No boundary-direction correspondence or affine-line formula is assumed.
-/

noncomputable section
open Set
namespace RepulsiveCoulomb

/-- The actual zero point of a positive-radius symmetric interval. -/
def complexSymmetricIntervalZero {R : ℝ} (hR : 0 < R) : Icc (-R) R :=
  ⟨0, by constructor <;> linarith⟩

/-- The actual right endpoint of a positive-radius symmetric interval. -/
def complexSymmetricIntervalRight {R : ℝ} (hR : 0 < R) : Icc (-R) R :=
  ⟨R, by constructor <;> linarith⟩

/-- The actual left endpoint of a positive-radius symmetric interval. -/
def complexSymmetricIntervalLeft {R : ℝ} (hR : 0 < R) : Icc (-R) R :=
  ⟨-R, by constructor <;> linarith⟩

/-- Two squared distances determine a point on the real line when one anchor is
nonzero. The zero imaginary part is derived, not a premise. -/
theorem complex_eq_real_of_two_squared_distances {z : ℂ} {t R : ℝ}
    (hR : R ≠ 0) (hzero : Complex.normSq z = t ^ 2)
    (hend : Complex.normSq (z - (R : ℂ)) = (t - R) ^ 2) : z = (t : ℂ) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero] at hzero hend
  have hprod : (z.re - t) * R = 0 := by nlinarith
  have hre : z.re = t := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hR)
  have himsq : z.im ^ 2 = 0 := by
    rw [hre] at hzero
    nlinarith
  apply Complex.ext
  · exact hre
  · exact sq_eq_zero_iff.mp himsq

/-- Squared distance preservation, expressed in the actual complex coordinates. -/
theorem complex_interval_isometry_normSq_sub {R : ℝ}
    (f : Icc (-R) R → ℂ) (hf : Isometry f) (s t : Icc (-R) R) :
    Complex.normSq (f s - f t) = (s.1 - t.1) ^ 2 := by
  have hd : dist (f s) (f t) = dist (s.1 : ℂ) (t.1 : ℂ) :=
    (hf.dist_eq s t).trans (Complex.isometry_ofReal.dist_eq s.1 t.1).symm
  have h := complex_normSq_sub_eq_of_dist_eq hd
  simpa only [← Complex.ofReal_sub, Complex.normSq_ofReal, pow_two] using h

/-- In a closed upper halfplane, the endpoints of an actual centered isometric
interval must be real. In particular, its right endpoint is +R or -R. -/
theorem complex_upper_interval_right_endpoint_eq_or_neg
    {R : ℝ} (hR : 0 < R) (f : Icc (-R) R → ℂ) (hf : Isometry f)
    (hzero : f (complexSymmetricIntervalZero hR) = 0)
    (hupper : ∀ t : Icc (-R) R, 0 ≤ (f t).im) :
    f (complexSymmetricIntervalRight hR) = (R : ℂ) ∨
      f (complexSymmetricIntervalRight hR) = (-R : ℂ) := by
  let p := complexSymmetricIntervalRight hR
  let m := complexSymmetricIntervalLeft hR
  have hp := complex_interval_isometry_normSq_sub f hf p (complexSymmetricIntervalZero hR)
  have hm := complex_interval_isometry_normSq_sub f hf m (complexSymmetricIntervalZero hR)
  have hpm := complex_interval_isometry_normSq_sub f hf p m
  change Complex.normSq (f p - f (complexSymmetricIntervalZero hR)) = (R - 0) ^ 2 at hp
  change Complex.normSq (f m - f (complexSymmetricIntervalZero hR)) = (-R - 0) ^ 2 at hm
  simp only [hzero, sub_zero] at hp hm
  change Complex.normSq (f p - f m) = (R - -R) ^ 2 at hpm
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hp hm hpm
  have hsum : ((f p).re + (f m).re) ^ 2 +
      ((f p).im + (f m).im) ^ 2 = 0 := by nlinarith
  have himsum : (f p).im + (f m).im = 0 := (sq_add_sq_eq_zero.mp hsum).2
  have hpim : (f p).im = 0 := by
    have hu₁ := hupper p
    have hu₂ := hupper m
    linarith
  have hpre : (f p).re ^ 2 = R ^ 2 := by rw [hpim] at hp; nlinarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hpre with hpos | hneg
  · left
    apply Complex.ext
    · simpa using hpos
    · simpa using hpim
  · right
    apply Complex.ext
    · simpa using hneg
    · simpa using hpim

/-- Requested arclength alignment: one globally fixed sign works at every
actual point of the interval. The sign is a conclusion of the metric and side
hypotheses, not a supplied boundary-direction certificate. -/
theorem complex_upper_interval_isometry_eq_signed_real
    {R : ℝ} (hR : 0 < R) (f : Icc (-R) R → ℂ) (hf : Isometry f)
    (hzero : f (complexSymmetricIntervalZero hR) = 0)
    (hupper : ∀ t : Icc (-R) R, 0 ≤ (f t).im) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ t : Icc (-R) R, f t = ((σ * t.1 : ℝ) : ℂ) := by
  have hnorm (t : Icc (-R) R) : Complex.normSq (f t) = t.1 ^ 2 := by
    have h := complex_interval_isometry_normSq_sub f hf t (complexSymmetricIntervalZero hR)
    rw [hzero, sub_zero] at h
    simpa only [complexSymmetricIntervalZero, sub_zero] using h
  have hend (t : Icc (-R) R) :
      Complex.normSq (f t - f (complexSymmetricIntervalRight hR)) = (t.1 - R) ^ 2 :=
    complex_interval_isometry_normSq_sub f hf t (complexSymmetricIntervalRight hR)
  rcases complex_upper_interval_right_endpoint_eq_or_neg hR f hf hzero hupper with hp | hm
  · refine ⟨1, Or.inl rfl, fun t => ?_⟩
    have hdist : Complex.normSq (f t - (R : ℂ)) = (t.1 - R) ^ 2 := by
      simpa only [hp] using hend t
    simpa only [one_mul] using complex_eq_real_of_two_squared_distances
      (ne_of_gt hR) (hnorm t) hdist
  · refine ⟨-1, Or.inr rfl, fun t => ?_⟩
    have hdist : Complex.normSq (f t - ((-R : ℝ) : ℂ)) = (-t.1 - -R) ^ 2 := by
      calc
        _ = (t.1 - R) ^ 2 := by simpa only [hm, Complex.ofReal_neg] using hend t
        _ = (-t.1 - -R) ^ 2 := by ring
    have hnorm' : Complex.normSq (f t) = (-t.1) ^ 2 := by
      simpa only [neg_sq] using hnorm t
    simpa only [neg_one_mul] using complex_eq_real_of_two_squared_distances
      (neg_ne_zero.mpr (ne_of_gt hR)) hnorm' hdist

end RepulsiveCoulomb
