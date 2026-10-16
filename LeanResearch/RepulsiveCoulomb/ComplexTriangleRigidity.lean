import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Source-only draft: elementary Euclidean rigidity from three actual distances.
No rigid-transition certificate, differentiability, or developing map is assumed.
The determinant condition below is the explicit coordinate noncollinearity test.
-/

noncomputable section
namespace RepulsiveCoulomb

/-- The oriented real determinant of two actual complex vectors. -/
def complexFrameDet (a b : ℂ) : ℝ := a.re * b.im - a.im * b.re

/-- The real Euclidean scalar product, in coordinates. -/
def complexFrameDot (a b : ℂ) : ℝ := a.re * b.re + a.im * b.im

/-- Three specified complex points are noncollinear, tested without a chosen chart. -/
def ComplexTriangleNoncollinear (p₀ p₁ p₂ : ℂ) : Prop :=
  complexFrameDet (p₁ - p₀) (p₂ - p₀) ≠ 0

theorem complex_normSq_sub_eq_of_dist_eq {a b c d : ℂ}
    (h : dist a b = dist c d) :
    Complex.normSq (a - b) = Complex.normSq (c - d) := by
  simpa only [Complex.dist_eq, Complex.normSq_eq_norm_sq] using
    congrArg (fun r : ℝ => r ^ 2) h

theorem complex_normSq_combination (r s : ℝ) (a b : ℂ) :
    Complex.normSq (r • a + s • b) =
      r ^ 2 * Complex.normSq a + 2 * r * s * complexFrameDot a b +
        s ^ 2 * Complex.normSq b := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul, complexFrameDot]
  ring

theorem complexFrameDot_eq_of_three_normSq {a b c d : ℂ}
    (ha : Complex.normSq c = Complex.normSq a)
    (hb : Complex.normSq d = Complex.normSq b)
    (hab : Complex.normSq (c - d) = Complex.normSq (a - b)) :
    complexFrameDot c d = complexFrameDot a b := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at ha hb hab
  dsimp [complexFrameDot]
  nlinarith

/-- First Cramer coordinate in a two-vector frame. -/
def complexFirstCoordinate (a b : ℂ) : ℂ →ₗ[ℝ] ℝ where
  toFun z := (z.re * b.im - z.im * b.re) / complexFrameDet a b
  map_add' := by
    intro z w
    simp only [Complex.add_re, Complex.add_im]
    ring
  map_smul' := by
    intro r z
    simp only [Complex.smul_re, Complex.smul_im, RingHom.id_apply, smul_eq_mul]
    ring

/-- Second Cramer coordinate in a two-vector frame. -/
def complexSecondCoordinate (a b : ℂ) : ℂ →ₗ[ℝ] ℝ where
  toFun z := (a.re * z.im - a.im * z.re) / complexFrameDet a b
  map_add' := by
    intro z w
    simp only [Complex.add_re, Complex.add_im]
    ring
  map_smul' := by
    intro r z
    simp only [Complex.smul_re, Complex.smul_im, RingHom.id_apply, smul_eq_mul]
    ring

@[simp] theorem complexFirstCoordinate_left (a b : ℂ)
    (h : complexFrameDet a b ≠ 0) : complexFirstCoordinate a b a = 1 := by
  change complexFrameDet a b / complexFrameDet a b = 1
  exact div_self h

@[simp] theorem complexFirstCoordinate_right (a b : ℂ) :
    complexFirstCoordinate a b b = 0 := by
  change (b.re * b.im - b.im * b.re) / complexFrameDet a b = 0
  rw [mul_comm b.re b.im, sub_self, zero_div]

@[simp] theorem complexSecondCoordinate_left (a b : ℂ) :
    complexSecondCoordinate a b a = 0 := by
  change (a.re * a.im - a.im * a.re) / complexFrameDet a b = 0
  rw [mul_comm a.re a.im, sub_self, zero_div]

@[simp] theorem complexSecondCoordinate_right (a b : ℂ)
    (h : complexFrameDet a b ≠ 0) : complexSecondCoordinate a b b = 1 := by
  change complexFrameDet a b / complexFrameDet a b = 1
  exact div_self h

theorem complex_coordinate_reconstruction (a b z : ℂ)
    (h : complexFrameDet a b ≠ 0) :
    complexFirstCoordinate a b z • a + complexSecondCoordinate a b z • b = z := by
  change ((z.re * b.im - z.im * b.re) / complexFrameDet a b) • a +
    ((a.re * z.im - a.im * z.re) / complexFrameDet a b) • b = z
  apply Complex.ext
  · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    field_simp [h]
    dsimp [complexFrameDet]
    ring
  · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    field_simp [h]
    dsimp [complexFrameDet]
    ring

/-- The explicitly constructed real linear map taking frame `(a,b)` to `(c,d)`. -/
def complexFrameLinear (a b c d : ℂ) : ℂ →ₗ[ℝ] ℂ :=
  (complexFirstCoordinate a b).smulRight c + (complexSecondCoordinate a b).smulRight d

@[simp] theorem complexFrameLinear_apply (a b c d z : ℂ) :
    complexFrameLinear a b c d z =
      complexFirstCoordinate a b z • c + complexSecondCoordinate a b z • d := rfl

@[simp] theorem complexFrameLinear_left (a b c d : ℂ)
    (h : complexFrameDet a b ≠ 0) : complexFrameLinear a b c d a = c := by
  simp [h]

@[simp] theorem complexFrameLinear_right (a b c d : ℂ)
    (h : complexFrameDet a b ≠ 0) : complexFrameLinear a b c d b = d := by
  simp [h]

/-- Gram preservation proves that the Cramer-coordinate map is an actual linear isometry. -/
def complexFrameLinearIsometry (a b c d : ℂ) (h : complexFrameDet a b ≠ 0)
    (ha : Complex.normSq c = Complex.normSq a)
    (hb : Complex.normSq d = Complex.normSq b)
    (hab : complexFrameDot c d = complexFrameDot a b) : ℂ →ₗᵢ[ℝ] ℂ where
  toLinearMap := complexFrameLinear a b c d
  norm_map' := by
    intro z
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    change Complex.normSq
      (complexFirstCoordinate a b z • c + complexSecondCoordinate a b z • d) =
        Complex.normSq z
    rw [complex_normSq_combination, ha, hb, hab,
      ← complex_normSq_combination, complex_coordinate_reconstruction a b z h]

@[simp] theorem complexFrameLinearIsometry_left (a b c d : ℂ) (h ha hb hab) :
    complexFrameLinearIsometry a b c d h ha hb hab a = c :=
  complexFrameLinear_left a b c d h

@[simp] theorem complexFrameLinearIsometry_right (a b c d : ℂ) (h ha hb hab) :
    complexFrameLinearIsometry a b c d h ha hb hab b = d :=
  complexFrameLinear_right a b c d h

/-- Three distances to noncollinear anchors determine an actual complex point. -/
theorem complex_eq_of_three_dist_eq {p₀ p₁ p₂ x y : ℂ}
    (hp : ComplexTriangleNoncollinear p₀ p₁ p₂)
    (h₀ : dist x p₀ = dist y p₀)
    (h₁ : dist x p₁ = dist y p₁)
    (h₂ : dist x p₂ = dist y p₂) : x = y := by
  have h₀' := complex_normSq_sub_eq_of_dist_eq h₀
  have h₁' := complex_normSq_sub_eq_of_dist_eq h₁
  have h₂' := complex_normSq_sub_eq_of_dist_eq h₂
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at h₀' h₁' h₂'
  have ha : (x.re - y.re) * (p₁ - p₀).re +
      (x.im - y.im) * (p₁ - p₀).im = 0 := by
    simp only [Complex.sub_re, Complex.sub_im]
    nlinarith
  have hb : (x.re - y.re) * (p₂ - p₀).re +
      (x.im - y.im) * (p₂ - p₀).im = 0 := by
    simp only [Complex.sub_re, Complex.sub_im]
    nlinarith
  have hre : (x.re - y.re) * complexFrameDet (p₁ - p₀) (p₂ - p₀) = 0 := by
    calc
      _ = ((x.re - y.re) * (p₁ - p₀).re +
          (x.im - y.im) * (p₁ - p₀).im) * (p₂ - p₀).im -
        ((x.re - y.re) * (p₂ - p₀).re +
          (x.im - y.im) * (p₂ - p₀).im) * (p₁ - p₀).im := by
            dsimp [complexFrameDet]
            ring
      _ = 0 := by rw [ha, hb]; ring
  have him : (x.im - y.im) * complexFrameDet (p₁ - p₀) (p₂ - p₀) = 0 := by
    calc
      _ = (p₁ - p₀).re * ((x.re - y.re) * (p₂ - p₀).re +
          (x.im - y.im) * (p₂ - p₀).im) -
        (p₂ - p₀).re * ((x.re - y.re) * (p₁ - p₀).re +
          (x.im - y.im) * (p₁ - p₀).im) := by
            dsimp [complexFrameDet]
            ring
      _ = 0 := by rw [ha, hb]; ring
  exact Complex.ext (sub_eq_zero.mp ((mul_eq_zero.mp hre).resolve_right hp))
    (sub_eq_zero.mp ((mul_eq_zero.mp him).resolve_right hp))

/-- No affine hypothesis is needed for uniqueness: actual global distance isometries suffice. -/
theorem complex_isometry_eq_of_three_points (e g : ℂ ≃ᵢ ℂ)
    {p₀ p₁ p₂ : ℂ} (hp : ComplexTriangleNoncollinear p₀ p₁ p₂)
    (h₀ : e p₀ = g p₀) (h₁ : e p₁ = g p₁) (h₂ : e p₂ = g p₂) : e = g := by
  apply IsometryEquiv.ext
  intro x
  have h : e.symm (g x) = x := by
    apply complex_eq_of_three_dist_eq hp
    · calc
        dist (e.symm (g x)) p₀ = dist (g x) (e p₀) := by
          rw [← e.dist_eq (e.symm (g x)) p₀, e.apply_symm_apply]
        _ = dist x p₀ := by rw [h₀, g.dist_eq]
    · calc
        dist (e.symm (g x)) p₁ = dist (g x) (e p₁) := by
          rw [← e.dist_eq (e.symm (g x)) p₁, e.apply_symm_apply]
        _ = dist x p₁ := by rw [h₁, g.dist_eq]
    · calc
        dist (e.symm (g x)) p₂ = dist (g x) (e p₂) := by
          rw [← e.dist_eq (e.symm (g x)) p₂, e.apply_symm_apply]
        _ = dist x p₂ := by rw [h₂, g.dist_eq]
  have := congrArg e h
  simpa only [e.apply_symm_apply] using this.symm

end RepulsiveCoulomb
