import LeanResearch.RepulsiveCoulomb.ComplexTriangleRigidity

/-!
Source-only draft: extension of an actual distance-preserving map on a literal
subset of the complex plane. The constructed map is a real affine isometry.
The open-overlap result uses only a ball in the interior and three explicit
anchors. There is no assumption that the local map is already rigid.
-/

noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Extend an actual subset isometry by reconstructing its linear part from three
noncollinear anchors. Surjectivity follows from equal finite real dimensions. -/
theorem exists_complex_affine_isometry_extension_of_triangle
    {U : Set ℂ} (f : U → ℂ) (hf : Isometry f) (p₀ p₁ p₂ : U)
    (hp : ComplexTriangleNoncollinear p₀.1 p₁.1 p₂.1) :
    ∃ e : ℂ ≃ᵃⁱ[ℝ] ℂ, ∀ x : U, e x.1 = f x := by
  let a : ℂ := p₁.1 - p₀.1
  let b : ℂ := p₂.1 - p₀.1
  let c : ℂ := f p₁ - f p₀
  let d : ℂ := f p₂ - f p₀
  have hdet : complexFrameDet a b ≠ 0 := hp
  have ha : Complex.normSq c = Complex.normSq a :=
    complex_normSq_sub_eq_of_dist_eq (hf.dist_eq p₁ p₀)
  have hb : Complex.normSq d = Complex.normSq b :=
    complex_normSq_sub_eq_of_dist_eq (hf.dist_eq p₂ p₀)
  have hcd : Complex.normSq (c - d) = Complex.normSq (a - b) := by
    dsimp [a, b, c, d]
    simpa only [sub_sub_sub_cancel_right] using
      complex_normSq_sub_eq_of_dist_eq (hf.dist_eq p₁ p₂)
  have hab : complexFrameDot c d = complexFrameDot a b :=
    complexFrameDot_eq_of_three_normSq ha hb hcd
  let L : ℂ ≃ₗᵢ[ℝ] ℂ :=
    (complexFrameLinearIsometry a b c d hdet ha hb hab).toLinearIsometryEquiv rfl
  let e : ℂ ≃ᵃⁱ[ℝ] ℂ := AffineIsometryEquiv.mk'
    (fun z : ℂ => L (z - p₀.1) + f p₀) L p₀.1 (by intro z; simp)
  have he₀ : e p₀.1 = f p₀ := by
    change L (p₀.1 - p₀.1) + f p₀ = f p₀
    simp
  have he₁ : e p₁.1 = f p₁ := by
    change complexFrameLinearIsometry a b c d hdet ha hb hab a + f p₀ = f p₁
    rw [complexFrameLinearIsometry_left]
    exact sub_add_cancel (f p₁) (f p₀)
  have he₂ : e p₂.1 = f p₂ := by
    change complexFrameLinearIsometry a b c d hdet ha hb hab b + f p₀ = f p₂
    rw [complexFrameLinearIsometry_right]
    exact sub_add_cancel (f p₂) (f p₀)
  refine ⟨e, fun x => ?_⟩
  let E : ℂ ≃ᵢ ℂ := e.toIsometryEquiv
  have h₀ : E p₀.1 = f p₀ := he₀
  have h₁ : E p₁.1 = f p₁ := he₁
  have h₂ : E p₂.1 = f p₂ := he₂
  have hx : E.symm (f x) = x.1 := by
    apply complex_eq_of_three_dist_eq hp
    · calc
        dist (E.symm (f x)) p₀.1 = dist (f x) (E p₀.1) := by
          rw [← E.dist_eq (E.symm (f x)) p₀.1, E.apply_symm_apply]
        _ = dist x.1 p₀.1 := by rw [h₀]; exact hf.dist_eq x p₀
    · calc
        dist (E.symm (f x)) p₁.1 = dist (f x) (E p₁.1) := by
          rw [← E.dist_eq (E.symm (f x)) p₁.1, E.apply_symm_apply]
        _ = dist x.1 p₁.1 := by rw [h₁]; exact hf.dist_eq x p₁
    · calc
        dist (E.symm (f x)) p₂.1 = dist (f x) (E p₂.1) := by
          rw [← E.dist_eq (E.symm (f x)) p₂.1, E.apply_symm_apply]
        _ = dist x.1 p₂.1 := by rw [h₂]; exact hf.dist_eq x p₂
  have h := congrArg E hx
  have hE : E x.1 = f x := by
    simpa only [E.apply_symm_apply] using h.symm
  simpa only [E, AffineIsometryEquiv.coe_toIsometryEquiv] using hE

/-- Existence and uniqueness among all actual global distance isometries. -/
theorem existsUnique_complex_isometry_extension_of_triangle
    {U : Set ℂ} (f : U → ℂ) (hf : Isometry f) (p₀ p₁ p₂ : U)
    (hp : ComplexTriangleNoncollinear p₀.1 p₁.1 p₂.1) :
    ∃! e : ℂ ≃ᵢ ℂ, ∀ x : U, e x.1 = f x := by
  obtain ⟨e, he⟩ := exists_complex_affine_isometry_extension_of_triangle f hf p₀ p₁ p₂ hp
  refine ⟨e.toIsometryEquiv, he, fun g hg => ?_⟩
  exact complex_isometry_eq_of_three_points g e.toIsometryEquiv hp
    ((hg p₀).trans (he p₀).symm) ((hg p₁).trans (he p₁).symm)
    ((hg p₂).trans (he p₂).symm)

/-- A genuine positive-radius ball contains three explicitly noncollinear anchors. -/
theorem exists_complex_noncollinear_triangle_of_ball_subset
    {U : Set ℂ} {p : ℂ} {r : ℝ} (hr : 0 < r) (hU : Metric.ball p r ⊆ U) :
    ∃ p₀ p₁ p₂ : U, ComplexTriangleNoncollinear p₀.1 p₁.1 p₂.1 := by
  let δ : ℝ := r / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδr : δ < r := by dsimp [δ]; linarith
  have h₀ : p ∈ U := hU (by simpa using hr)
  have h₁ : p + (δ : ℂ) ∈ U := by
    apply hU
    change dist (p + (δ : ℂ)) p < r
    simpa [Complex.dist_eq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hδ] using hδr
  have h₂ : p + (δ : ℂ) * Complex.I ∈ U := by
    apply hU
    change dist (p + (δ : ℂ) * Complex.I) p < r
    simpa [Complex.dist_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hδ] using hδr
  refine ⟨⟨p, h₀⟩, ⟨p + (δ : ℂ), h₁⟩, ⟨p + (δ : ℂ) * Complex.I, h₂⟩, ?_⟩
  change complexFrameDet ((p + (δ : ℂ)) - p)
    ((p + (δ : ℂ) * Complex.I) - p) ≠ 0
  simpa [complexFrameDet] using mul_ne_zero (ne_of_gt hδ) (ne_of_gt hδ)

/-- Direct positive-ball version; the domain need not be open or connected. -/
theorem existsUnique_complex_isometry_extension_of_ball_subset
    {U : Set ℂ} (f : U → ℂ) (hf : Isometry f)
    {p : ℂ} {r : ℝ} (hr : 0 < r) (hU : Metric.ball p r ⊆ U) :
    ∃! e : ℂ ≃ᵢ ℂ, ∀ x : U, e x.1 = f x := by
  obtain ⟨p₀, p₁, p₂, hp⟩ :=
    exists_complex_noncollinear_triangle_of_ball_subset hr hU
  exact existsUnique_complex_isometry_extension_of_triangle f hf p₀ p₁ p₂ hp

/-- Interior nonemptiness is sufficient; U itself need not be open or connected. -/
theorem exists_complex_noncollinear_triangle_of_interior_nonempty
    {U : Set ℂ} (hU : (interior U).Nonempty) :
    ∃ p₀ p₁ p₂ : U, ComplexTriangleNoncollinear p₀.1 p₁.1 p₂.1 := by
  obtain ⟨p, hp⟩ := hU
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
  exact exists_complex_noncollinear_triangle_of_ball_subset hr
    (hball.trans interior_subset)

/-- Main patch-continuation interface. It extends the given actual local map;
rigidity is the conclusion, not an input certificate. -/
theorem exists_complex_isometry_extension_of_open_overlap
    {U : Set ℂ} (f : U → ℂ) (hf : Isometry f) (hU : (interior U).Nonempty) :
    ∃ e : ℂ ≃ᵢ ℂ, ∀ x : U, e x.1 = f x := by
  obtain ⟨p₀, p₁, p₂, hp⟩ :=
    exists_complex_noncollinear_triangle_of_interior_nonempty hU
  exact (existsUnique_complex_isometry_extension_of_triangle f hf p₀ p₁ p₂ hp).exists

/-- Uniqueness of a genuine local chart extension on a nonempty open overlap. -/
theorem existsUnique_complex_isometry_extension_of_open_overlap
    {U : Set ℂ} (f : U → ℂ) (hf : Isometry f) (hU : (interior U).Nonempty) :
    ∃! e : ℂ ≃ᵢ ℂ, ∀ x : U, e x.1 = f x := by
  obtain ⟨p₀, p₁, p₂, hp⟩ :=
    exists_complex_noncollinear_triangle_of_interior_nonempty hU
  exact existsUnique_complex_isometry_extension_of_triangle f hf p₀ p₁ p₂ hp

/-- Literal pairwise distance preservation version of the main interface. -/
theorem existsUnique_complex_isometry_extension_of_dist_eq
    {U : Set ℂ} (f : U → ℂ)
    (hf : ∀ x y : U, dist (f x) (f y) = dist x y)
    (hU : (interior U).Nonempty) :
    ∃! e : ℂ ≃ᵢ ℂ, ∀ x : U, e x.1 = f x :=
  existsUnique_complex_isometry_extension_of_open_overlap f (Isometry.of_dist_eq hf) hU

/-- Agreement on an actual nonempty open overlap forces global agreement. -/
theorem complex_isometry_eq_of_open_overlap {U : Set ℂ}
    (e g : ℂ ≃ᵢ ℂ) (hU : (interior U).Nonempty)
    (heq : Set.EqOn e g U) : e = g := by
  obtain ⟨p₀, p₁, p₂, hp⟩ :=
    exists_complex_noncollinear_triangle_of_interior_nonempty hU
  exact complex_isometry_eq_of_three_points e g hp
    (heq p₀.property) (heq p₁.property) (heq p₂.property)

/-- Open-set formulation used by actual chart-germ uniqueness. -/
theorem complex_isometry_eq_of_agree_on_nonempty_open
    {V : Set ℂ} (hV : IsOpen V) (hne : V.Nonempty) {e₁ e₂ : ℂ ≃ᵢ ℂ}
    (hagree : Set.EqOn e₁ e₂ V) : e₁ = e₂ := by
  apply complex_isometry_eq_of_open_overlap (U := V) e₁ e₂
  · simpa only [hV.interior_eq] using hne
  · exact hagree

end RepulsiveCoulomb
