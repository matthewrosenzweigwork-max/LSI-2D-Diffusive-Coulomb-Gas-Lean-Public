module

public import LeanResearch.RepulsiveCoulomb.PointScoreIntegrationByParts

@[expose] public section

/-! Actual two-coordinate integration of the ground-state cross term. -/
noncomputable section
open Set MeasureTheory Metric Filter InnerProductSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem complex_real_inner_one_I (u w : ℂ) :
    inner ℝ u w = inner ℝ u (1 : ℂ) * inner ℝ w (1 : ℂ) +
      inner ℝ u Complex.I * inner ℝ w Complex.I := by
  have h : inner ℝ u w = inner ℝ u (1 : ℂ) * inner ℝ (1 : ℂ) w +
      inner ℝ u Complex.I * inner ℝ Complex.I w := by
    simpa [Fin.sum_univ_two, Complex.coe_orthonormalBasisOneI] using
      (Complex.orthonormalBasisOneI.sum_inner_mul_inner u w).symm
  rw [← real_inner_comm (1 : ℂ) w, ← real_inner_comm Complex.I w] at h
  exact h

theorem pointCore_score_directional_cross_integral {m : ℕ} (γ : ℝ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) (v : ℂ) :
    2 * (∫ x : ℂ, φ x * fderiv ℝ (φ : ℂ → ℝ) x v * inner ℝ (pointScore γ a y x) v) =
      -(∫ x : ℂ, φ x ^ 2 * fderiv ℝ (fun z => inner ℝ (pointScore γ a y z) v) x v) := by
  rw [← integral_const_mul]
  convert! pointCoreSquare_score_integrationByParts γ ha y φ v using 1
  congr 1
  funext x
  ring

theorem pointCore_score_cross_integrable {m : ℕ} (γ : ℝ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    Integrable (fun x : ℂ => φ x * inner ℝ (gradient (φ : ℂ → ℝ) x) (pointScore γ a y x)) := by
  have h1 := pointCore_score_directional_cross_integrable γ ha y φ 1
  have hI := pointCore_score_directional_cross_integrable γ ha y φ Complex.I
  convert! h1.add hI using 1
  funext x
  change φ x * inner ℝ (gradient (φ : ℂ → ℝ) x) (pointScore γ a y x) =
    φ x * fderiv ℝ (φ : ℂ → ℝ) x 1 * inner ℝ (pointScore γ a y x) 1 +
    φ x * fderiv ℝ (φ : ℂ → ℝ) x Complex.I * inner ℝ (pointScore γ a y x) Complex.I
  rw [complex_real_inner_one_I, inner_gradient_left, inner_gradient_left]
  ring

theorem pointCore_score_cross_integral {m : ℕ} (γ : ℝ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    (∫ x : ℂ, φ x * inner ℝ (gradient (φ : ℂ → ℝ) x) (pointScore γ a y x)) =
      -γ * (∫ x : ℂ, φ x ^ 2) := by
  let A : ℂ → ℝ := fun x => φ x * fderiv ℝ (φ : ℂ → ℝ) x 1 * inner ℝ (pointScore γ a y x) 1
  let B : ℂ → ℝ := fun x => φ x * fderiv ℝ (φ : ℂ → ℝ) x Complex.I * inner ℝ (pointScore γ a y x) Complex.I
  have hA : Integrable A := pointCore_score_directional_cross_integrable γ ha y φ 1
  have hB : Integrable B := pointCore_score_directional_cross_integrable γ ha y φ Complex.I
  have hpoint (x : ℂ) : φ x * inner ℝ (gradient (φ : ℂ → ℝ) x) (pointScore γ a y x) = A x + B x := by
    rw [complex_real_inner_one_I, inner_gradient_left, inner_gradient_left]
    dsimp only [A, B]
    ring
  have hc : (∫ x : ℂ, φ x * inner ℝ (gradient (φ : ℂ → ℝ) x) (pointScore γ a y x)) =
      (∫ x, A x) + ∫ x, B x := by
    rw [integral_congr_ae (Eventually.of_forall hpoint), integral_add hA hB]
  have h1 := pointCore_score_directional_cross_integral γ ha y φ 1
  have hI := pointCore_score_directional_cross_integral γ ha y φ Complex.I
  have hd : (∫ x : ℂ, φ x ^ 2 * fderiv ℝ (fun z => inner ℝ (pointScore γ a y z) (1 : ℂ)) x 1) +
      (∫ x : ℂ, φ x ^ 2 * fderiv ℝ (fun z => inner ℝ (pointScore γ a y z) Complex.I) x Complex.I) =
      (2 * γ) * (∫ x : ℂ, φ x ^ 2) := by
    rw [← integral_add (pointCore_score_divergence_integrable γ ha y φ 1)
      (pointCore_score_divergence_integrable γ ha y φ Complex.I), ← integral_const_mul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    dsimp only
    by_cases hx : x ∉ pointPunctures a y
    · rw [← mul_add, pointScore_divergence γ ha y hx]
      ring
    · have hn : x ∉ tsupport (φ : ℂ → ℝ) := fun ht => hx (φ.tsupport_subset ht)
      simp [image_eq_zero_of_notMem_tsupport hn]
  change 2 * (∫ x, A x) = _ at h1
  change 2 * (∫ x, B x) = _ at hI
  rw [hc]
  linarith only [h1, hI, hd]

end RepulsiveCoulomb
