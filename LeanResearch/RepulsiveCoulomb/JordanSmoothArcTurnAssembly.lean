module

public import LeanResearch.RepulsiveCoulomb.JordanC1Joining
public import LeanResearch.RepulsiveCoulomb.JordanBezierCorner

@[expose] public section

/-! Actual angle-increment preservation under positive smooth reparameterizing
and additivity under the constructed matched-velocity C¹ concatenation.
These are geometric-to-algebra bridges for finite smoothing assembly, not input
turn certificates. Records-only phase-five candidate. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

private theorem normalized_real_smul_pos {z : ℂ} (hz : z ≠ 0) {a : ℝ} (ha : 0 < a) :
    (a • z) / (‖a • z‖ : ℂ) = z / (‖z‖ : ℂ) := by
  exact congrArg (fun z : Circle => (z : ℂ)) (euclideanDirection_smul_pos hz ha)

/-- Positive actual speed changes preserve the full signed tangent increment. -/
theorem regular_arc_turn_positive_reparameterization
    {η : ℝ → ℂ} (hη : ContDiff ℝ 1 η)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, deriv η t ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hmap : MapsTo φ (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hφ0 : φ 0 = 0) (hφ1 : φ 1 = 1)
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < deriv φ t)
    {θ Θ : Icc (0 : ℝ) 1 → ℝ} (hθ : Continuous θ) (hΘ : Continuous Θ)
    (hθlift : ∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
      deriv η t / (‖deriv η t‖ : ℂ))
    (hΘlift : ∀ t, Complex.exp ((Θ t : ℂ) * Complex.I) =
      deriv (η ∘ φ) t / (‖deriv (η ∘ φ) t‖ : ℂ)) :
    Θ 1 - Θ 0 = θ 1 - θ 0 := by
  let σ : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun t => ⟨φ t, hmap t.2⟩
  have hσ : Continuous σ := (hφ.continuous.comp continuous_subtype_val).subtype_mk _
  have hD (t : Icc (0 : ℝ) 1) : deriv (η ∘ φ) t = deriv φ t • deriv η (φ t) :=
    ((((hη.differentiable (by norm_num)) (φ t)).hasDerivAt).scomp (t : ℝ)
      (((hφ.differentiable (by norm_num)) (t : ℝ)).hasDerivAt)).deriv
  have hinc := euclidean_angle_lift_increment_eq hΘ (hθ.comp hσ)
    (fun t => by
      apply Circle.ext
      change Complex.exp ((Θ t : ℂ) * Complex.I) = Complex.exp ((θ (σ t) : ℂ) * Complex.I)
      rw [hΘlift, hθlift, hD, normalized_real_smul_pos (hreg _ (hmap t.2)) (hpos _ t.2)])
    (0 : Icc (0 : ℝ) 1) 1
  have hσ0 : σ 0 = 0 := by apply Subtype.ext; simpa [σ] using hφ0
  have hσ1 : σ 1 = 1 := by apply Subtype.ext; simpa [σ] using hφ1
  change Θ 1 - Θ 0 = θ (σ 1) - θ (σ 0) at hinc
  rwa [hσ0, hσ1] at hinc

/-- The actual matched-velocity concatenation adds tangent increments exactly.
The proof restricts its actual tangent lift to the two halves and uses the
positive speed factor 2; no angle additivity certificate is supplied. -/
theorem regular_arc_turn_concatenate
    {f g : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hval : f 1 = g 0) (hjet : deriv f 1 = deriv g 0)
    (hfr : ∀ t ∈ Icc (0 : ℝ) 1, deriv f t ≠ 0)
    (hgr : ∀ t ∈ Icc (0 : ℝ) 1, deriv g t ≠ 0)
    {θf θg Θ : Icc (0 : ℝ) 1 → ℝ}
    (hθf : Continuous θf) (hθg : Continuous θg) (hΘ : Continuous Θ)
    (hfLift : ∀ t, Complex.exp ((θf t : ℂ) * Complex.I) = deriv f t / (‖deriv f t‖ : ℂ))
    (hgLift : ∀ t, Complex.exp ((θg t : ℂ) * Complex.I) = deriv g t / (‖deriv g t‖ : ℂ))
    (hLift : ∀ t, Complex.exp ((Θ t : ℂ) * Complex.I) =
      deriv (euclideanSmoothConcatenate f g) t /
        (‖deriv (euclideanSmoothConcatenate f g) t‖ : ℂ)) :
    Θ 1 - Θ 0 = (θf 1 - θf 0) + (θg 1 - θg 0) := by
  let L : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun t =>
    ⟨t / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩
  let R : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun t =>
    ⟨(t + 1) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩
  have hL : Continuous L := (continuous_subtype_val.div_const 2).subtype_mk _
  have hR : Continuous R := ((continuous_subtype_val.add continuous_const).div_const 2).subtype_mk _
  have hdL (t : Icc (0 : ℝ) 1) :
      deriv (euclideanSmoothConcatenate f g) (L t) = (2 : ℝ) • deriv f t := by
    rw [euclideanSmoothConcatenate_deriv hf hg hval hjet,
      if_pos (show (L t : ℝ) ≤ 1 / 2 by dsimp [L]; linarith [t.2.2])]
    congr 2
    change 2 * ((t : ℝ) / 2) = t
    ring
  have hdR (t : Icc (0 : ℝ) 1) :
      deriv (euclideanSmoothConcatenate f g) (R t) = (2 : ℝ) • deriv g t := by
    rw [euclideanSmoothConcatenate_deriv hf hg hval hjet]
    by_cases hmid : (R t : ℝ) ≤ 1 / 2
    · have ht0 : (t : ℝ) = 0 := by dsimp [R] at hmid; linarith [t.2.1]
      rw [if_pos hmid]
      simpa [R, ht0] using congrArg (fun z : ℂ => (2 : ℝ) • z) hjet
    · rw [if_neg hmid]
      congr 2
      change 2 * (((t : ℝ) + 1) / 2) - 1 = t
      ring
  have hif := euclidean_angle_lift_increment_eq hθf (hΘ.comp hL)
    (fun t => by
      apply Circle.ext
      change Complex.exp ((θf t : ℂ) * Complex.I) = Complex.exp ((Θ (L t) : ℂ) * Complex.I)
      rw [hfLift, hLift, hdL, normalized_real_smul_pos (hfr _ t.2) (by norm_num)])
    (0 : Icc (0 : ℝ) 1) 1
  have hig := euclidean_angle_lift_increment_eq hθg (hΘ.comp hR)
    (fun t => by
      apply Circle.ext
      change Complex.exp ((θg t : ℂ) * Complex.I) = Complex.exp ((Θ (R t) : ℂ) * Complex.I)
      rw [hgLift, hLift, hdR, normalized_real_smul_pos (hgr _ t.2) (by norm_num)])
    (0 : Icc (0 : ℝ) 1) 1
  have hL0 : L 0 = 0 := by apply Subtype.ext; simp [L]
  have hR1 : R 1 = 1 := by apply Subtype.ext; norm_num [R]
  have hLR : L 1 = R 0 := by apply Subtype.ext; norm_num [L, R]
  change θf 1 - θf 0 = Θ (L 1) - Θ (L 0) at hif
  change θg 1 - θg 0 = Θ (R 1) - Θ (R 0) at hig
  rw [hL0, hLR] at hif
  rw [hR1] at hig
  linarith

end RepulsiveCoulomb
