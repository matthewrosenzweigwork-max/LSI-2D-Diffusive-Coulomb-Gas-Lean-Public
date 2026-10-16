import LeanResearch.RepulsiveCoulomb.JordanFiniteCornerBoundaryPointSum

/-! Actual inside/outside point sums for the original finite family, allowing
only open-edge point identities. Endpoint identities are recovered from
compact avoidance and continuous circle lifts; the positive sign is selected
by an actual inside witness rather than a prescribed flux function. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

theorem point_argument_open_identity_extends_to_endpoints
    (η : Icc (0 : ℝ) 1 → ℂ) (hη : Continuous η) (p : ℂ) (hp : ∀ t, η t ≠ p)
    (ψ : Icc (0 : ℝ) 1 → ℝ) (hψ : Continuous ψ)
    (hlift : ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((ψ t : ℂ) * Complex.I) = (η t - p) / (‖η t - p‖ : ℂ)) :
    ∀ t, Complex.exp ((ψ t : ℂ) * Complex.I) = (η t - p) / (‖η t - p‖ : ℂ) := by
  obtain ⟨φ, hφ, hφlift⟩ := exists_interval_euclidean_angle_lift
    (hη.sub continuous_const) (fun t => sub_ne_zero.mpr (hp t))
  have heq := unit_interval_circle_exp_eq_of_open ψ φ hψ hφ (by
    intro t ht
    exact Circle.ext ((hlift t ht).trans (hφlift t).symm))
  intro t
  exact (congrArg (fun z : Circle => (z : ℂ)) (heq t)).trans (hφlift t)

/-- A point in either actual complementary component is avoided by every
closed original edge, so the endpoint values of any open-edge lift are forced. -/
theorem finite_corner_complement_open_point_lift_closed
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    {U V : Set ℂ} (hcover : U ∪ V = (⋃ k ≤ n, f k '' Icc (0 : ℝ) 1)ᶜ)
    {w : ℂ} (hw : w ∈ U ∪ V) (ψ : ℕ → Icc (0 : ℝ) 1 → ℝ)
    (hψ : ∀ k ≤ n, Continuous (ψ k))
    (hψlift : ∀ k ≤ n, ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((ψ k t : ℂ) * Complex.I) = (f k t - w) / (‖f k t - w‖ : ℂ)) :
    ∀ k ≤ n, ∀ t, Complex.exp ((ψ k t : ℂ) * Complex.I) =
      (f k t - w) / (‖f k t - w‖ : ℂ) := by
  have hwC : w ∉ ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1 := by
    have hw' : w ∈ U ∪ V := hw
    rw [hcover] at hw'
    exact hw' 
  intro k hk
  apply point_argument_open_identity_extends_to_endpoints
    (fun t : Icc (0 : ℝ) 1 => f k t) ((hf k hk).comp continuous_subtype_val) w
    (fun t heq => hwC (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, ⟨t, t.2, heq⟩⟩⟩))
    (ψ k) (hψ k hk) (hψlift k hk)

/-- Every inside point has actual point sum +2π once a positive actual
inside witness chooses traversal. The alternative sign is disproved. -/
theorem finite_corner_inside_open_point_sum_positive
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, ContDiff ℝ 1 (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 → f i s = f j t → i = j ∧ s = t)
    (hreg : deriv (f 0) (1 / 2) ≠ 0)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hK : IsCompact (closure U))
    (hcover : U ∪ V = (⋃ k ≤ n, f k '' Icc (0 : ℝ) 1)ᶜ)
    {w₀ : ℂ} (hw₀ : w₀ ∈ U) (Ξ : ℕ → Icc (0 : ℝ) 1 → ℝ)
    (hΞ : ∀ k ≤ n, Continuous (Ξ k))
    (hΞlift : ∀ k ≤ n, ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((Ξ k t : ℂ) * Complex.I) = (f k t - w₀) / (‖f k t - w₀‖ : ℂ))
    (hΞturn : (∑ k ∈ Finset.range (n + 1), (Ξ k 1 - Ξ k 0)) = 2 * Real.pi)
    {w : ℂ} (hw : w ∈ U) (ψ : ℕ → Icc (0 : ℝ) 1 → ℝ)
    (hψ : ∀ k ≤ n, Continuous (ψ k))
    (hψlift : ∀ k ≤ n, ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((ψ k t : ℂ) * Complex.I) = (f k t - w) / (‖f k t - w‖ : ℂ)) :
    (∑ k ∈ Finset.range (n + 1), (ψ k 1 - ψ k 0)) = 2 * Real.pi := by
  have hfc : ∀ k ≤ n, Continuous (f k) := fun k hk => (hf k hk).continuous
  have hΞclosed := finite_corner_complement_open_point_lift_closed f n hfc hcover
    (Or.inl hw₀) Ξ hΞ hΞlift
  have hψclosed := finite_corner_complement_open_point_lift_closed f n hfc hcover
    (Or.inl hw) ψ hψ hψlift
  rcases finite_corner_inside_point_sum_classification f n hf hv hclose hinj hreg
    hU hUc hV hVc hK hcover with hplus | hminus
  · exact hplus w hw ψ hψ hψclosed
  · have hcontra := hminus w₀ hw₀ Ξ hΞ hΞclosed
    nlinarith [Real.pi_pos]

/-- The actual outside sum vanishes for continuous endpoint-extended
open-edge lifts, without imposing an identity at a possible zero chord. -/
theorem finite_corner_outside_open_point_sum_zero
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    {U V : Set ℂ} (hK : IsCompact (closure U)) (hV : IsOpen V) (hVc : IsConnected V)
    (hcover : U ∪ V = (⋃ k ≤ n, f k '' Icc (0 : ℝ) 1)ᶜ)
    {w : ℂ} (hw : w ∈ V) (ψ : ℕ → Icc (0 : ℝ) 1 → ℝ)
    (hψ : ∀ k ≤ n, Continuous (ψ k))
    (hψlift : ∀ k ≤ n, ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((ψ k t : ℂ) * Complex.I) = (f k t - w) / (‖f k t - w‖ : ℂ)) :
    (∑ k ∈ Finset.range (n + 1), (ψ k 1 - ψ k 0)) = 0 := by
  exact finite_corner_outside_point_sum_zero f n hf hv hclose hK hV hVc hcover hw ψ hψ
    (finite_corner_complement_open_point_lift_closed f n hf hcover (Or.inr hw) ψ hψ hψlift)

end RepulsiveCoulomb
