import LeanResearch.RepulsiveCoulomb.JordanCornerInterpolation
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! A concrete regular quadratic smoothing of an actual noncuspidal radial
corner. Injectivity and exclusion of the retained radial tails are proved
algebraically, and its actual turn is the principal corner argument. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def euclideanBezierCorner (u v : ℂ) (t : ℝ) : ℂ :=
  -((1 - t) ^ 2 : ℝ) • u + (t ^ 2 : ℝ) • v

@[simp] theorem euclideanBezierCorner_zero (u v : ℂ) :
    euclideanBezierCorner u v 0 = -u := by simp [euclideanBezierCorner]

@[simp] theorem euclideanBezierCorner_one (u v : ℂ) :
    euclideanBezierCorner u v 1 = v := by simp [euclideanBezierCorner]

theorem euclideanBezierCorner_contDiff (u v : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanBezierCorner u v) := by
  unfold euclideanBezierCorner
  fun_prop

theorem euclideanBezierCorner_hasDerivAt (u v : ℂ) (t : ℝ) :
    HasDerivAt (euclideanBezierCorner u v) ((2 : ℝ) • euclideanCornerBlend u v t) t := by
  have h₁ : HasDerivAt (fun s : ℝ => -((1 - s) ^ 2)) (2 * (1 - t)) t := by
    convert! (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).fun_pow 2).neg using 1 <;>
      norm_num <;> ring
  have h₂ : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    convert! (hasDerivAt_id t).fun_pow 2 using 1 <;> norm_num <;> ring
  convert (h₁.smul_const u).add (h₂.smul_const v) using 1
  · rfl
  · simp only [euclideanCornerBlend, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_ofNat, Complex.ofReal_one]
    ring

@[simp] theorem euclideanBezierCorner_deriv (u v : ℂ) (t : ℝ) :
    deriv (euclideanBezierCorner u v) t = (2 : ℝ) • euclideanCornerBlend u v t :=
  (euclideanBezierCorner_hasDerivAt u v t).deriv

theorem euclideanBezierCorner_regular {u v : ℂ} (hu : u ≠ 0)
    (hc : v / u ∈ Complex.slitPlane) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    deriv (euclideanBezierCorner u v) t ≠ 0 := by
  rw [euclideanBezierCorner_deriv]
  exact smul_ne_zero (by norm_num) (euclideanCornerBlend_ne_zero hu hc ht)

/-- The exact secant is a positive multiple of the tangent blend at the
midpoint. In particular, the replacement arc has no self-intersection. -/
theorem euclideanBezierCorner_sub (u v : ℂ) (s t : ℝ) :
    euclideanBezierCorner u v t - euclideanBezierCorner u v s =
      (2 * (t - s)) • euclideanCornerBlend u v ((s + t) / 2) := by
  simp only [euclideanBezierCorner, euclideanCornerBlend, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_ofNat, Complex.ofReal_one]
  ring

theorem euclideanBezierCorner_injOn {u v : ℂ} (hu : u ≠ 0)
    (hc : v / u ∈ Complex.slitPlane) :
    InjOn (euclideanBezierCorner u v) (Icc (0 : ℝ) 1) := by
  intro s hs t ht heq
  have hmid : (s + t) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hn := euclideanCornerBlend_ne_zero hu hc hmid
  have hzero : (2 * (t - s)) • euclideanCornerBlend u v ((s + t) / 2) = 0 := by
    rw [← euclideanBezierCorner_sub, heq, sub_self]
  rcases smul_eq_zero.mp hzero with hz | hz
  · linarith
  · exact (hn hz).elim

/-- Every nontrivial positive combination of the two nonopposite tangent
vectors is nonzero. -/
theorem noncuspidal_positive_combination_ne_zero {u v : ℂ} (hu : u ≠ 0)
    (hc : v / u ∈ Complex.slitPlane) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) : a • u + b • v ≠ 0 := by
  have ht : b / (a + b) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hb hab.le, (div_le_one hab).mpr (by linarith)⟩
  have hn := smul_ne_zero hab.ne' (euclideanCornerBlend_ne_zero hu hc ht)
  have heq : (a + b) • euclideanCornerBlend u v (b / (a + b)) = a • u + b • v := by
    have habc : (a : ℂ) + (b : ℂ) ≠ 0 := by exact_mod_cast hab.ne'
    simp only [euclideanCornerBlend, Complex.real_smul, Complex.ofReal_sub,
      Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one]
    field_simp [habc]
    ring
  rwa [heq] at hn

/-- The open replacement arc misses the incoming retained radial tail. -/
theorem euclideanBezierCorner_ne_incoming_tail {u v : ℂ} (hu : u ≠ 0)
    (hc : v / u ∈ Complex.slitPlane) {t c : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) (hc1 : 1 ≤ c) :
    euclideanBezierCorner u v t ≠ -c • u := by
  have ht0 := ht.1
  have ht1 := ht.2
  have hsq : (1 - t) ^ 2 ≤ 1 := by nlinarith
  have hn := noncuspidal_positive_combination_ne_zero hu hc
    (show 0 ≤ c - (1 - t) ^ 2 by linarith)
    (sq_nonneg t) (show 0 < c - (1 - t) ^ 2 + t ^ 2 by nlinarith)
  intro heq
  apply hn
  have hzero := sub_eq_zero.mpr heq
  convert hzero using 1 <;>
    simp only [euclideanBezierCorner, sub_smul, neg_smul] <;> abel

/-- The open replacement arc misses the outgoing retained radial tail. -/
theorem euclideanBezierCorner_ne_outgoing_tail {u v : ℂ} (hu : u ≠ 0)
    (hc : v / u ∈ Complex.slitPlane) {t c : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) (hc1 : 1 ≤ c) :
    euclideanBezierCorner u v t ≠ c • v := by
  have ht0 := ht.1
  have ht1 := ht.2
  have hsq : t ^ 2 ≤ 1 := by nlinarith
  have hn := noncuspidal_positive_combination_ne_zero hu hc
    (sq_nonneg (1 - t))
    (show 0 ≤ c - t ^ 2 by linarith)
    (show 0 < (1 - t) ^ 2 + (c - t ^ 2) by nlinarith)
  intro heq
  apply hn
  have hzero := neg_eq_zero.mpr (sub_eq_zero.mpr heq)
  convert hzero using 1 <;>
    simp only [euclideanBezierCorner, sub_smul, neg_smul] <;> abel

/-- The replacement stays in the closed disk containing its two endpoints. -/
theorem euclideanBezierCorner_norm_le {u v : ℂ} {R t : ℝ}
    (hR : 0 ≤ R) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖euclideanBezierCorner u v t‖ ≤ R := by
  have h₁ : 0 ≤ (1 - t) ^ 2 := sq_nonneg _
  have h₂ : 0 ≤ t ^ 2 := sq_nonneg _
  have hsum : (1 - t) ^ 2 + t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  calc
    ‖euclideanBezierCorner u v t‖ ≤ ‖-((1 - t) ^ 2 : ℝ) • u‖ + ‖(t ^ 2 : ℝ) • v‖ := norm_add_le _ _
    _ = (1 - t) ^ 2 * ‖u‖ + t ^ 2 * ‖v‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg h₁, abs_of_nonneg h₂]
    _ ≤ (1 - t) ^ 2 * R + t ^ 2 * R :=
      add_le_add (mul_le_mul_of_nonneg_left hu h₁) (mul_le_mul_of_nonneg_left hv h₂)
    _ ≤ R := by nlinarith [mul_le_mul_of_nonneg_right hsum hR]

theorem euclideanDirection_smul_pos {z : ℂ} (hz : z ≠ 0) {a : ℝ} (ha : 0 < a) :
    euclideanDirection (a • z) (smul_ne_zero ha.ne' hz) = euclideanDirection z hz := by
  apply Circle.ext
  simp only [euclideanDirection_coe, Complex.real_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ha, Complex.ofReal_mul]
  have hac : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  field_simp

/-- Every tangent-angle lift along this actual regular replacement arc has
exactly the requested principal corner increment. -/
theorem euclideanBezierCorner_total_turn {u v : ℂ} (hu : u ≠ 0)
    (hc : v / u ∈ Complex.slitPlane)
    {θ : Icc (0 : ℝ) 1 → ℝ} (hθ : Continuous θ)
    (hlift : ∀ t, Circle.exp (θ t) = euclideanDirection
      (deriv (euclideanBezierCorner u v) t) (euclideanBezierCorner_regular hu hc t.2)) :
    θ 1 - θ 0 = Complex.arg (v / u) := by
  apply euclideanCornerBlend_lift_increment hu hc hθ
  intro t
  rw [hlift]
  have h := euclideanDirection_smul_pos (euclideanCornerBlend_ne_zero hu hc t.2)
    (show (0 : ℝ) < 2 by norm_num)
  apply Circle.ext
  simpa only [euclideanDirection_coe, euclideanBezierCorner_deriv] using
    congrArg (fun z : Circle => (z : ℂ)) h

end RepulsiveCoulomb
