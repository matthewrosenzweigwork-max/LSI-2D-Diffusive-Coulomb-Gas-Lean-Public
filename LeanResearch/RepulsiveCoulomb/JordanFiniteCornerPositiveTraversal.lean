import LeanResearch.RepulsiveCoulomb.JordanFiniteCornerReversal

/-! Choose the positive traversal of the actual original finite family.
The sign is first derived from the original Jordan theorem; only the negative
case reverses every actual arc and the finite slot order. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

/-- Positive inside winding expressed using actual point-argument lifts. -/
def FiniteCornerPositiveInside (f : ℕ → ℝ → ℂ) (n : ℕ) (U : Set ℂ) : Prop :=
  ∀ w ∈ U, ∀ ψ : ℕ → Icc (0 : ℝ) 1 → ℝ,
    (∀ k ≤ n, Continuous (ψ k)) →
    (∀ k ≤ n, ∀ t, Complex.exp ((ψ k t : ℂ) * Complex.I) =
      (f k t - w) / (‖f k t - w‖ : ℂ)) →
    (∑ k ∈ Finset.range (n + 1), (ψ k 1 - ψ k 0)) = 2 * Real.pi

/-- Actual reversal changes the negative inside value to the positive one.
This lemma is used only after the original sign has been geometrically derived. -/
theorem finiteCornerReverse_positive_of_negative
    (f : ℕ → ℝ → ℂ) (n : ℕ) (U : Set ℂ)
    (hnegative : ∀ w ∈ U, ∀ ψ : ℕ → Icc (0 : ℝ) 1 → ℝ,
      (∀ k ≤ n, Continuous (ψ k)) →
      (∀ k ≤ n, ∀ t, Complex.exp ((ψ k t : ℂ) * Complex.I) =
        (f k t - w) / (‖f k t - w‖ : ℂ)) →
      (∑ k ∈ Finset.range (n + 1), (ψ k 1 - ψ k 0)) = -(2 * Real.pi)) :
    FiniteCornerPositiveInside (finiteCornerReverse f n) n U := by
  intro w hw ψ hψ hψlift
  let φ : ℕ → Icc (0 : ℝ) 1 → ℝ := fun k t => ψ (n - k) (unitInterval.symm t)
  have hφ (k : ℕ) (_ : k ≤ n) : Continuous (φ k) :=
    (hψ (n - k) (Nat.sub_le _ _)).comp unitInterval.continuous_symm
  have hφlift (k : ℕ) (hk : k ≤ n) (t : Icc (0 : ℝ) 1) :
      Complex.exp ((φ k t : ℂ) * Complex.I) = (f k t - w) / (‖f k t - w‖ : ℂ) := by
    change Complex.exp ((ψ (n - k) (unitInterval.symm t) : ℂ) * Complex.I) = _
    rw [hψlift (n - k) (Nat.sub_le _ _)]
    simp only [finiteCornerReverse, Nat.sub_sub_self hk, unitInterval.coe_symm_eq, sub_sub_cancel]
  have he := hnegative w hw φ hφ hφlift
  simp only [φ, unitInterval.symm_one, unitInterval.symm_zero] at he
  rw [finite_corner_reflection_sum n (fun k => ψ k 0 - ψ k 1)] at he
  have hsign : (∑ k ∈ Finset.range (n + 1), (ψ k 0 - ψ k 1)) =
      -(∑ k ∈ Finset.range (n + 1), (ψ k 1 - ψ k 0)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hsign] at he
  linarith

/-- One of the two literal traversals of the original finite curve is
positive. Its original carrier, regularity, joins and actual simplicity
are retained. A winding-sign assumption is not required. -/
theorem exists_finite_corner_positive_traversal
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, ContDiff ℝ 1 (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      f i s = f j t → i = j ∧ s = t)
    (hreg : ∀ k ≤ n, ∀ t ∈ Icc (0 : ℝ) 1, deriv (f k) t ≠ 0)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hK : IsCompact (closure U))
    (hcover : U ∪ V = (⋃ k ≤ n, f k '' Icc (0 : ℝ) 1)ᶜ) :
    ∃ g : ℕ → ℝ → ℂ, (g = f ∨ g = finiteCornerReverse f n) ∧
      (∀ k ≤ n, ContDiff ℝ 1 (g k)) ∧
      (∀ k < n, g k 1 = g (k + 1) 0) ∧ g n 1 = g 0 0 ∧
      (∀ i j, i ≤ n → j ≤ n → ∀ s t,
        s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
        g i s = g j t → i = j ∧ s = t) ∧
      (∀ k ≤ n, ∀ t ∈ Icc (0 : ℝ) 1, deriv (g k) t ≠ 0) ∧
      (⋃ k ≤ n, g k '' Icc (0 : ℝ) 1) = (⋃ k ≤ n, f k '' Icc (0 : ℝ) 1) ∧
      FiniteCornerPositiveInside g n U := by
  rcases finite_corner_inside_point_sum_classification f n hf hv hclose hinj
    (hreg 0 (Nat.zero_le n) (1 / 2) (by norm_num)) hU hUc hV hVc hK hcover with hplus | hminus
  · exact ⟨f, Or.inl rfl, hf, hv, hclose, hinj, hreg, rfl, hplus⟩
  · obtain ⟨hg, hgv, hgc, hgi, hgr, hgimage⟩ := finiteCornerReverse_properties f n hf hv hclose hinj hreg
    exact ⟨finiteCornerReverse f n, Or.inr rfl, hg, hgv, hgc, hgi, hgr, hgimage,
      finiteCornerReverse_positive_of_negative f n U hminus⟩

end RepulsiveCoulomb
