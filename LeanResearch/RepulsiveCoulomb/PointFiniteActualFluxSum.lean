module

public import LeanResearch.RepulsiveCoulomb.PointFiniteBoundaryCoalescence
public import LeanResearch.RepulsiveCoulomb.PointFiniteRadialCornerGeometry

@[expose] public section

/-! Finite point-flux assembly for an actual simple original radial family.
Inside/outside/boundary values are derived by the corresponding geometric
argument theorems. Positive boundary locations are proved to be actual vertices,
and the literal input exponents are coalesced there. Only positive boundary-atom vertices need radial chart data; ordinary
zero-mass corners may have arbitrary regular C1 collars. No point-sum values
or Gauss–Bonnet equality are hypotheses. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace RepulsiveCoulomb

/-- Actual finite weighted argument sum, with full reflex boundary-sector
terms and each coalesced atom counted exactly at its physical vertex. -/
theorem finite_actual_radial_boundary_weighted_argument_sum
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, ContDiff ℝ 1 (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 → f i s = f j t → i = j ∧ s = t)
    (hreg : deriv (f 0) (1 / 2) ≠ 0)
    (havoid : ∀ k ≤ n, ∀ t ∈ Ioo (0 : ℝ) 1, f k t ∉ pointPunctures a y)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hdisj : Disjoint U V)
    (hK : IsCompact (closure U))
    (hcover : U ∪ V = (⋃ k ≤ n, f k '' Icc (0 : ℝ) 1)ᶜ)
    (hvertexU : ∀ k ≤ n, f k 0 ∈ closure U) (hvertexV : ∀ k ≤ n, f k 0 ∈ closure V)
    {w : ℂ} (hw : w ∈ U) (Ξ : ℕ → Icc (0 : ℝ) 1 → ℝ)
    (hΞ : ∀ k ≤ n, Continuous (Ξ k))
    (hΞlift : ∀ k ≤ n, ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((Ξ k t : ℂ) * Complex.I) = (f k t - w) / (‖f k t - w‖ : ℂ))
    (hΞturn : (∑ k ∈ Finset.range (n + 1), (Ξ k 1 - Ξ k 0)) = 2 * Real.pi)
    (θ : ℕ → ℝ)
    (D : ∀ k ≤ n, 0 < coalescedPointExponent a y (f k 0) → PointFiniteRadialCornerAt f n k (θ k))
    (ψ : Fin m → ℕ → Icc (0 : ℝ) 1 → ℝ)
    (hψ : ∀ j k, k ≤ n → Continuous (ψ j k))
    (hψlift : ∀ j, a j ≠ 0 → ∀ k ≤ n, ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((ψ j k t : ℂ) * Complex.I) = (f k t - y j) / (‖f k t - y j‖ : ℂ)) :
    (∑ j, (a j / 2) * (∑ k ∈ Finset.range (n + 1), (ψ j k 1 - ψ j k 0))) =
      2 * Real.pi * (∑ j, if y j ∈ U then a j / 2 else 0) +
        ∑ k ∈ Finset.range (n + 1), (coalescedPointExponent a y (f k 0) / 2) * θ k := by
  let A : Fin m → ℝ := fun j => ∑ k ∈ Finset.range (n + 1), (ψ j k 1 - ψ j k 0)
  let B : Fin m → ℝ := fun j => ∑ k ∈ Finset.range (n + 1), if y j = f k 0 then θ k else 0
  have hfc : ∀ k ≤ n, Continuous (f k) := fun k hk => (hf k hk).continuous
  have hterm (j : Fin m) : (a j / 2) * A j =
      (if y j ∈ U then 2 * Real.pi * (a j / 2) else 0) + (a j / 2) * B j := by
    by_cases haj : a j = 0
    · simp [haj]
    by_cases hyU : y j ∈ U
    · have hAj : A j = 2 * Real.pi := finite_corner_inside_open_point_sum_positive
        f n hf hv hclose hinj hreg hU hUc hV hVc hK hcover hw Ξ hΞ hΞlift hΞturn
        hyU (ψ j) (hψ j) (hψlift j haj)
      have hyC : y j ∉ ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1 := by
        have hyC' : y j ∈ U ∪ V := Or.inl hyU
        rw [hcover] at hyC'
        exact hyC' 
      have hBj : B j = 0 := finite_boundary_selector_zero_of_not_mem_carrier f n θ hyC
      rw [hAj, hBj, if_pos hyU]
      ring
    by_cases hyC : y j ∈ ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1
    · obtain ⟨k, hk, hyk⟩ := active_location_on_finite_boundary_is_vertex ha y f n hv hclose havoid haj hyC
      have hψk : ∀ i ≤ n, ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
          Complex.exp ((ψ j i t : ℂ) * Complex.I) = (f i t - f k 0) / (‖f i t - f k 0‖ : ℂ) := by
        intro i hi t ht
        simpa only [hyk] using hψlift j haj i hi t ht
      have hkP : f k 0 ∈ positivePointLocations a y :=
        (mem_positivePointLocations a y (f k 0)).mpr
          ⟨j, lt_of_le_of_ne (ha j) (Ne.symm haj), hyk⟩
      have hκ : 0 < coalescedPointExponent a y (f k 0) := coalescedPointExponent_pos a y hkP
      have hAj : A j = θ k := (D k hk hκ).point_sum hfc hinj hU hUc hV hVc hdisj hK hcover
        (hvertexU k hk) (hvertexV k hk) hw Ξ hΞ hΞlift hΞturn (ψ j) (hψ j) hψk
      have hBj : B j = θ k := by
        dsimp [B]
        rw [hyk]
        exact finite_boundary_selector_eq_vertex_angle f n θ hinj hk
      rw [hAj, hBj, if_neg hyU, zero_add]
    · have hyUV : y j ∈ U ∪ V := by
        rw [hcover]
        exact hyC
      have hyV : y j ∈ V := by
        rcases hyUV with h | h
        · exact False.elim (hyU h)
        · exact h
      have hAj : A j = 0 := finite_corner_outside_open_point_sum_zero f n hfc hv hclose hK hV hVc
        hcover hyV (ψ j) (hψ j) (hψlift j haj)
      have hBj : B j = 0 := finite_boundary_selector_zero_of_not_mem_carrier f n θ hyC
      rw [hAj, hBj, if_neg hyU]
      ring
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => hterm j)
  change (∑ j, (a j / 2) * A j) = _
  rw [hsum, Finset.sum_add_distrib]
  have hboundary : (∑ j, (a j / 2) * B j) =
      ∑ k ∈ Finset.range (n + 1), (coalescedPointExponent a y (f k 0) / 2) * θ k :=
    finite_boundary_weighted_selector_coalesces ha y f n θ
  rw [hboundary]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hy : y j ∈ U <;> simp [hy]

end RepulsiveCoulomb
