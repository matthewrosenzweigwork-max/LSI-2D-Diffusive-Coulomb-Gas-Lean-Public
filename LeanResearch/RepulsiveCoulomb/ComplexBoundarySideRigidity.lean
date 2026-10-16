import LeanResearch.RepulsiveCoulomb.ComplexSubsetIsometryExtension

/-!
Source-only draft: the boundary reflection ambiguity is settled from the actual
side of one point. No orientation label or rigid-transition certificate is used.
For normalized local halfplane chart compositions, fixing an actual real interval
and retaining an actual upper-side point forces agreement throughout the domain.
-/

noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Two distances to distinct real points determine a point up to conjugation. -/
theorem complex_eq_or_conj_of_two_real_dist_eq {s t : ℝ} (hst : s ≠ t)
    {x y : ℂ} (hs : dist x (s : ℂ) = dist y (s : ℂ))
    (ht : dist x (t : ℂ) = dist y (t : ℂ)) :
    x = y ∨ x = star y := by
  have hs' := complex_normSq_sub_eq_of_dist_eq hs
  have ht' := complex_normSq_sub_eq_of_dist_eq ht
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero] at hs' ht'
  have hre_mul : (x.re - y.re) * (s - t) = 0 := by nlinarith
  have hre : x.re = y.re :=
    sub_eq_zero.mp ((mul_eq_zero.mp hre_mul).resolve_right (sub_ne_zero.mpr hst))
  have himsq : x.im ^ 2 = y.im ^ 2 := by
    rw [hre] at hs'
    nlinarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp himsq with him | him
  · exact Or.inl (Complex.ext hre him)
  · right
    apply Complex.ext
    · change x.re = y.re
      exact hre
    · change x.im = -y.im
      exact him

/-- With both points on the actual upper side, the reflected alternative is impossible. -/
theorem complex_eq_of_two_real_dist_eq_of_pos_im {s t : ℝ} (hst : s ≠ t)
    {x y : ℂ} (hs : dist x (s : ℂ) = dist y (s : ℂ))
    (ht : dist x (t : ℂ) = dist y (t : ℂ))
    (hx : 0 < x.im) (hy : 0 < y.im) : x = y := by
  rcases complex_eq_or_conj_of_two_real_dist_eq hst hs ht with h | h
  · exact h
  · have him : x.im = -y.im := congrArg Complex.im h
    linarith

/-- A genuine subset isometry fixing two distinct real points and keeping one
actual upper point above the real axis is the identity on its whole domain. -/
theorem complex_subset_isometry_eq_id_of_fixed_real_pair_same_side
    {U : Set ℂ} (f : U → ℂ) (hf : Isometry f)
    {s t : ℝ} (hst : s ≠ t) (hsU : (s : ℂ) ∈ U) (htU : (t : ℂ) ∈ U)
    (hs : f ⟨(s : ℂ), hsU⟩ = (s : ℂ))
    (ht : f ⟨(t : ℂ), htU⟩ = (t : ℂ))
    (q : U) (hq : 0 < q.1.im) (hfq : 0 < (f q).im) :
    ∀ x : U, f x = x.1 := by
  have hqfix : f q = q.1 := by
    apply complex_eq_of_two_real_dist_eq_of_pos_im hst _ _ hfq hq
    · simpa only [hs, Subtype.dist_eq] using hf.dist_eq q ⟨(s : ℂ), hsU⟩
    · simpa only [ht, Subtype.dist_eq] using hf.dist_eq q ⟨(t : ℂ), htU⟩
  have hp : ComplexTriangleNoncollinear (s : ℂ) (t : ℂ) q.1 := by
    simpa [ComplexTriangleNoncollinear, complexFrameDet] using
      mul_ne_zero (sub_ne_zero.mpr (Ne.symm hst)) (ne_of_gt hq)
  intro x
  apply complex_eq_of_three_dist_eq hp
  · simpa only [hs, Subtype.dist_eq] using hf.dist_eq x ⟨(s : ℂ), hsU⟩
  · simpa only [ht, Subtype.dist_eq] using hf.dist_eq x ⟨(t : ℂ), htU⟩
  · simpa only [hqfix, Subtype.dist_eq] using hf.dist_eq x q

/-- Boundary-interval formulation for actual normalized halfplane transitions.
Only two boundary points and one actual same-side point are used by the proof. -/
theorem complex_subset_isometry_eq_id_of_fixed_real_interval_same_side
    {U : Set ℂ} (f : U → ℂ) (hf : Isometry f)
    {a b : ℝ} (hab : a < b)
    (hsegment : ∀ t ∈ Ioo a b, (t : ℂ) ∈ U)
    (hfix : ∀ (t : ℝ) (ht : t ∈ Ioo a b),
      f ⟨(t : ℂ), hsegment t ht⟩ = (t : ℂ))
    (q : U) (hq : 0 < q.1.im) (hfq : 0 < (f q).im) :
    ∀ x : U, f x = x.1 := by
  let s : ℝ := (2 * a + b) / 3
  let t : ℝ := (a + 2 * b) / 3
  have hs : s ∈ Ioo a b := by dsimp [s]; constructor <;> linarith
  have ht : t ∈ Ioo a b := by dsimp [t]; constructor <;> linarith
  have hst : s ≠ t := by dsimp [s, t]; linarith
  exact complex_subset_isometry_eq_id_of_fixed_real_pair_same_side f hf hst
    (hsegment s hs) (hsegment t ht) (hfix s hs) (hfix t ht) q hq hfq

/-- Global form: a real-axis-fixing Euclidean motion cannot reflect when one
actual upper-side point remains above. -/
theorem complex_isometry_eq_refl_of_fixed_real_pair_same_side
    (e : ℂ ≃ᵢ ℂ) {s t : ℝ} (hst : s ≠ t)
    (hs : e (s : ℂ) = (s : ℂ)) (ht : e (t : ℂ) = (t : ℂ))
    {q : ℂ} (hq : 0 < q.im) (heq : 0 < (e q).im) :
    e = IsometryEquiv.refl ℂ := by
  have hqfix : e q = q := by
    apply complex_eq_of_two_real_dist_eq_of_pos_im hst _ _ heq hq
    · simpa only [hs] using e.dist_eq q (s : ℂ)
    · simpa only [ht] using e.dist_eq q (t : ℂ)
  have hp : ComplexTriangleNoncollinear (s : ℂ) (t : ℂ) q := by
    simpa [ComplexTriangleNoncollinear, complexFrameDet] using
      mul_ne_zero (sub_ne_zero.mpr (Ne.symm hst)) (ne_of_gt hq)
  exact complex_isometry_eq_of_three_points e (IsometryEquiv.refl ℂ) hp hs ht hqfix

end RepulsiveCoulomb
