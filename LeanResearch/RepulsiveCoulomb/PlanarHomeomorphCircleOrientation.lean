module

public import LeanResearch.RepulsiveCoulomb.PositivePlanarJacobian

@[expose] public section

/-!
# Orientation from one genuine nondegenerate point

Source-only candidate, not compiled or accepted. No general orientation,
Jordan-degree, or oriented-atlas theorem is assumed. The explicit homotopy
moves the center and the strictly positive radius of an actual Euclidean
circle before applying the actual injective map. Injectivity makes every
vector in that homotopy nonzero. Thus all actual image circles have the same
argument increment. One genuine differentiable nondegenerate point determines
the sign, and a single output conjugation normalizes it.

The point-metric application obtains that point from Rademacher and the finite
atom null set. It is conditional on an already supplied metric homeomorphism;
it does not construct the Bonk--Lang map.
-/

noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace RepulsiveCoulomb

/-- Actual circles of strictly positive radius do not contain their center. -/
theorem planarCircleVector_ne_zero {r : ℝ} (hr : 0 < r)
    (t : Icc (0 : ℝ) 1) : planarCircleVector r t ≠ 0 := by
  apply norm_pos_iff.mp
  simpa only [planarSignedCircleVector_norm hr.le] using hr

/-- Injectivity supplies the exact nonvanishing needed for argument lifting. -/
theorem planarMapCircleVector_ne_zero {F : ℂ → ℂ} (hF : Function.Injective F)
    (z : ℂ) {r : ℝ} (hr : 0 < r) (t : Icc (0 : ℝ) 1) :
    F (z + planarCircleVector r t) - F z ≠ 0 := by
  intro h
  have he := hF (sub_eq_zero.mp h)
  have hz : planarCircleVector r t = 0 := add_left_cancel (he.trans (add_zero z).symm)
  exact planarCircleVector_ne_zero hr t hz

/-- An actual argument lift of every actual image circle is constructed. -/
theorem exists_planarMapCircle_argumentLift {F : ℂ → ℂ}
    (hcont : Continuous F) (hinj : Function.Injective F) (z : ℂ)
    {r : ℝ} (hr : 0 < r) :
    ∃ θ : Icc (0 : ℝ) 1 → ℝ,
      PlanarArgumentLift (fun t => F (z + planarCircleVector r t) - F z) θ := by
  obtain ⟨θ, hc, he⟩ := exists_interval_euclidean_angle_lift
    ((hcont.comp (continuous_const.add (planarSignedCircleVector_continuous r 1))).sub
      continuous_const)
    (planarMapCircleVector_ne_zero hinj z hr)
  exact ⟨θ, hc, he⟩

/-- The radius interpolation is strictly positive, including its endpoints. -/
theorem planarCircleRadius_interpolate_pos {r₀ r₁ : ℝ}
    (h₀ : 0 < r₀) (h₁ : 0 < r₁) (s : Icc (0 : ℝ) 1) :
    0 < (1 - (s : ℝ)) * r₀ + (s : ℝ) * r₁ := by
  rcases lt_or_eq_of_le s.2.2 with hs | hs
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hs) h₀)
      (mul_nonneg s.2.1 h₁.le)
  · simpa only [hs, sub_self, zero_mul, one_mul, zero_add] using h₁

/-- The actual simultaneous center/radius homotopy, not a homotopy witness
whose avoidance or winding is postulated. -/
def planarMapCircleHomotopy (F : ℂ → ℂ) (z₀ z₁ : ℂ) (r₀ r₁ : ℝ)
    (p : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1) : ℂ :=
  let z := (1 - (p.1 : ℝ)) • z₀ + (p.1 : ℝ) • z₁
  let r := (1 - (p.1 : ℝ)) * r₀ + (p.1 : ℝ) * r₁
  F (z + planarCircleVector r p.2) - F z

theorem planarMapCircleHomotopy_continuous {F : ℂ → ℂ} (hF : Continuous F)
    (z₀ z₁ : ℂ) (r₀ r₁ : ℝ) :
    Continuous (planarMapCircleHomotopy F z₀ z₁ r₀ r₁) := by
  unfold planarMapCircleHomotopy planarCircleVector planarSignedCircleVector
  fun_prop

theorem planarMapCircleHomotopy_ne_zero {F : ℂ → ℂ} (hF : Function.Injective F)
    (z₀ z₁ : ℂ) {r₀ r₁ : ℝ} (h₀ : 0 < r₀) (h₁ : 0 < r₁)
    (p : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1) :
    planarMapCircleHomotopy F z₀ z₁ r₀ r₁ p ≠ 0 :=
  planarMapCircleVector_ne_zero hF _ (planarCircleRadius_interpolate_pos h₀ h₁ p.1) p.2

theorem planarMapCircleHomotopy_closed (F : ℂ → ℂ) (z₀ z₁ : ℂ) (r₀ r₁ : ℝ)
    (s : Icc (0 : ℝ) 1) :
    planarMapCircleHomotopy F z₀ z₁ r₀ r₁ (s, 0) =
      planarMapCircleHomotopy F z₀ z₁ r₀ r₁ (s, 1) := by
  simp only [planarMapCircleHomotopy, planarCircleVector_closed]

/-- Global constancy of the argument increment follows directly from the
constructed moving-circle homotopy. Surjectivity is not needed. -/
theorem planarMapCircle_argument_increment_eq {F : ℂ → ℂ}
    (hcont : Continuous F) (hinj : Function.Injective F) (z₀ z₁ : ℂ)
    {r₀ r₁ : ℝ} (h₀ : 0 < r₀) (h₁ : 0 < r₁)
    {θ₀ θ₁ : Icc (0 : ℝ) 1 → ℝ}
    (hθ₀ : PlanarArgumentLift (fun t => F (z₀ + planarCircleVector r₀ t) - F z₀) θ₀)
    (hθ₁ : PlanarArgumentLift (fun t => F (z₁ + planarCircleVector r₁ t) - F z₁) θ₁) :
    θ₀ 1 - θ₀ 0 = θ₁ 1 - θ₁ 0 := by
  apply closed_vector_loop_argument_homotopy (planarMapCircleHomotopy F z₀ z₁ r₀ r₁)
    (planarMapCircleHomotopy_continuous hcont z₀ z₁ r₀ r₁)
    (planarMapCircleHomotopy_ne_zero hinj z₀ z₁ h₀ h₁)
    (planarMapCircleHomotopy_closed F z₀ z₁ r₀ r₁) θ₀ θ₁ hθ₀.1 hθ₁.1
  · intro t
    simpa [planarMapCircleHomotopy] using hθ₀.2 t
  · intro t
    simpa [planarMapCircleHomotopy] using hθ₁.2 t

/-- Every image circle has exactly the sign of the actual derivative at one
nondegenerate anchor. This is a consequence, not an orientation hypothesis. -/
theorem planarMapCircle_argument_increment_of_anchor {F : ℂ → ℂ}
    (hcont : Continuous F) (hinj : Function.Injective F)
    {z₀ : ℂ} {A : ℂ →L[ℝ] ℂ} (hF : HasFDerivAt F A z₀)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ v, c * ‖v‖ ≤ ‖A v‖)
    (z : ℂ) {r : ℝ} (hr : 0 < r)
    {θ : Icc (0 : ℝ) 1 → ℝ}
    (hθ : PlanarArgumentLift (fun t => F (z + planarCircleVector r t) - F z) θ) :
    θ 1 - θ 0 = if 0 < A.toLinearMap.det then 2 * Real.pi else -(2 * Real.pi) := by
  obtain ⟨R, hR, hinc⟩ := hasFDerivAt_small_circle_argument_increment hcont hF hc hlower
  have hRhalf : 0 < R / 2 := half_pos hR
  obtain ⟨φ, hφ⟩ := exists_planarMapCircle_argumentLift hcont hinj z₀ hRhalf
  have hne (t : Icc (0 : ℝ) 1) : A (planarCircleVector (R / 2) t) ≠ 0 := by
    apply norm_pos_iff.mp
    have h := hlower (planarCircleVector (R / 2) t)
    rw [planarSignedCircleVector_norm hRhalf.le] at h
    exact (mul_pos hc hRhalf).trans_le h
  obtain ⟨ψ, hψc, hψe⟩ := exists_interval_euclidean_angle_lift
    (A.continuous.comp (planarSignedCircleVector_continuous (R / 2) 1)) hne
  have hψ : PlanarArgumentLift (fun t => A (planarCircleVector (R / 2) t)) ψ := ⟨hψc, hψe⟩
  calc
    θ 1 - θ 0 = φ 1 - φ 0 :=
      (planarMapCircle_argument_increment_eq hcont hinj z₀ z hRhalf hr hφ hθ).symm
    _ = ψ 1 - ψ 0 := hinc (R / 2) hRhalf (half_lt_self hR) φ ψ hφ hψ
    _ = _ := planar_realLinear_circle_increment A
      (planarLinear_det_ne_zero_of_lower A hc hlower) hRhalf hψ

/-- Output conjugation reverses the actual continuous argument lift. -/
theorem PlanarArgumentLift.conj {v : Icc (0 : ℝ) 1 → ℂ}
    {θ : Icc (0 : ℝ) 1 → ℝ} (hθ : PlanarArgumentLift v θ) :
    PlanarArgumentLift (fun t => conj (v t)) (fun t => -θ t) := by
  refine ⟨hθ.1.neg, fun t => ?_⟩
  have he : Complex.exp (((-θ t : ℝ) : ℂ) * Complex.I) =
      conj (Complex.exp ((θ t : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  rw [he, hθ.2 t]
  simp only [map_div₀, Complex.conj_ofReal, Complex.norm_conj]

/-- The two allowed global normalizations. No pointwise sign choice occurs. -/
def planarOutputConjugate (F : ℂ ≃ₜ ℂ) : ℂ ≃ₜ ℂ :=
  F.trans Complex.conjCLE.toHomeomorph

@[simp] theorem planarOutputConjugate_apply (F : ℂ ≃ₜ ℂ) (z : ℂ) :
    planarOutputConjugate F z = conj (F z) := rfl

@[simp] theorem planarOutputConjugate_norm_sub (F : ℂ ≃ₜ ℂ) (p z : ℂ) :
    ‖planarOutputConjugate F p - planarOutputConjugate F z‖ = ‖F p - F z‖ := by
  simp only [planarOutputConjugate_apply, ← map_sub, Complex.norm_conj]

/-- Normalize one actual nondegenerate derivative, then propagate the genuine
positive local circle winding to every point, including possible atoms. -/
theorem exists_positive_circle_normalization_of_anchor (F : ℂ ≃ₜ ℂ)
    {z₀ : ℂ} {A : ℂ →L[ℝ] ℂ} (hF : HasFDerivAt F A z₀)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ v, c * ‖v‖ ≤ ‖A v‖) :
    ∃ G : ℂ ≃ₜ ℂ, (G = F ∨ G = planarOutputConjugate F) ∧
      (∀ p z, ‖G p - G z‖ = ‖F p - F z‖) ∧
      ∀ z, PositiveLocalCircleWindingAt G z := by
  by_cases hp : 0 < A.toLinearMap.det
  · refine ⟨F, Or.inl rfl, fun _ _ => rfl, fun z => ⟨1, zero_lt_one, ?_⟩⟩
    intro r hr _
    obtain ⟨θ, hθ⟩ := exists_planarMapCircle_argumentLift F.continuous F.injective z hr
    refine ⟨θ, hθ, ?_⟩
    simpa only [if_pos hp] using
      planarMapCircle_argument_increment_of_anchor F.continuous F.injective hF hc hlower z hr hθ
  · refine ⟨planarOutputConjugate F, Or.inr rfl,
      planarOutputConjugate_norm_sub F, fun z => ⟨1, zero_lt_one, ?_⟩⟩
    intro r hr _
    obtain ⟨θ, hθ⟩ := exists_planarMapCircle_argumentLift F.continuous F.injective z hr
    have hi := planarMapCircle_argument_increment_of_anchor
      F.continuous F.injective hF hc hlower z hr hθ
    rw [if_neg hp] at hi
    refine ⟨fun t => -θ t, ?_, ?_⟩
    · simpa only [planarOutputConjugate_apply, map_sub] using hθ.conj
    · dsimp
      linarith

/-- The anchor is constructed from the actual metric estimates: a.e.
differentiability and the finite atom null set leave a nondegenerate point. -/
theorem pointMetricMap_exists_nondegenerate_anchor {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {F : ℂ → ℂ} {L : ℝ} (hL : 0 < L)
    (hlower : ∀ p z, (pointSmoothConformalEDist a y p z).toReal ≤ L * dist (F p) (F z))
    (hupper : ∀ p z, dist (F p) (F z) ≤ L * (pointSmoothConformalEDist a y p z).toReal) :
    ∃ z : ℂ, ∃ c : ℝ, 0 < c ∧ HasFDerivAt F (fderiv ℝ F z) z ∧
      ∀ v, c * ‖v‖ ≤ ‖fderiv ℝ F z v‖ := by
  have hnot : ∀ᵐ z : ℂ ∂volume, z ∉ pointPunctures a y := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using (pointPunctures_finite a y).measure_zero volume
  have hall : ∀ᵐ z : ℂ ∂volume,
      DifferentiableAt ℝ F z ∧ z ∉ pointPunctures a y :=
    (pointMetricMap_ae_differentiableAt ha y hL.le hupper).and hnot
  obtain ⟨z, hdiff, hz⟩ := hall.exists
  refine ⟨z, pointConformalDensity a y z / L,
    div_pos (pointConformalDensity_pos_off_punctures ha y hz) hL,
    hdiff.hasFDerivAt, fun v => ?_⟩
  exact (pointMetricMap_fderiv_bounds ha y hL hlower hupper hdiff v).1

/-- Every supplied actual point-metric homeomorphism has one globally
reflection-normalized representative with genuine positive local circle
winding. Neither the anchor nor an orientation certificate is an input. -/
theorem pointMetricHomeomorph_exists_positive_circle_normalization
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (F : ℂ ≃ₜ ℂ) {L : ℝ} (hL : 0 < L)
    (hmetric : ∀ p z,
      L⁻¹ * (pointSmoothConformalEDist a y p z).toReal ≤ ‖F p - F z‖ ∧
      ‖F p - F z‖ ≤ L * (pointSmoothConformalEDist a y p z).toReal) :
    ∃ G : ℂ ≃ₜ ℂ, (G = F ∨ G = planarOutputConjugate F) ∧
      (∀ p z, ‖G p - G z‖ = ‖F p - F z‖) ∧
      ∀ z, PositiveLocalCircleWindingAt G z := by
  have hlower : ∀ p z, (pointSmoothConformalEDist a y p z).toReal ≤ L * dist (F p) (F z) := by
    intro p z
    have h := mul_le_mul_of_nonneg_left (hmetric p z).1 hL.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul, dist_eq_norm] using h
  have hupper : ∀ p z, dist (F p) (F z) ≤ L * (pointSmoothConformalEDist a y p z).toReal := by
    intro p z
    simpa only [dist_eq_norm] using (hmetric p z).2
  obtain ⟨z, c, hc, hd, hl⟩ := pointMetricMap_exists_nondegenerate_anchor ha y hL hlower hupper
  exact exists_positive_circle_normalization_of_anchor F hd hc hl

end RepulsiveCoulomb
