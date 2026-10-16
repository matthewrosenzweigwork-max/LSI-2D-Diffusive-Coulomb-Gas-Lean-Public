import LeanResearch.RepulsiveCoulomb.PointLineCapActualFamily
import LeanResearch.RepulsiveCoulomb.PointLineCapAtomSupport

/-! Records-only, uncompiled. The constructed fixed side/common anchor now
instantiate compact-path exhaustion for the actual cap family. Interior atom
selectors stabilize exactly. Physical on-line angle coefficients still need
the mixed-GB/fixed-line-side local-chart transport; that is not assumed here. -/
noncomputable section
open Set Metric
open scoped BigOperators Classical
namespace RepulsiveCoulomb

theorem pointMetricLine_actual_cap_side_exhaustion
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {R₀ s : ℝ} (hsR : ‖c s‖ < R₀) (hds : DifferentiableAt ℝ c s) (hvs : deriv c s ≠ 0)
    (C : ∀ R : ℝ, R₀ < R → LineCapGeometry c R) :
    ∃ A B : Set ℂ, IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = (range c)ᶜ ∧ frontier A = range c ∧ frontier B = range c ∧
      (∀ R (hR : R₀ < R), (C R hR).inside ⊆ A) ∧
      ∀ z : ℂ, ∃ S : ℝ, ∃ hS : R₀ < S, ∀ R (hR : S < R),
        z ∈ (C R (hS.trans hR)).inside ↔ z ∈ A := by
  obtain ⟨A, B, hA, hB, hAc, hBc, hAB, hcover, hfa, hfb, x, hx, hside, hanchor⟩ :=
    pointMetricLine_cap_family_fixed_side ha y c hd hsR hds hvs C
  have hAline : Disjoint A (range c) := by
    apply disjoint_left.mpr
    intro z hz hl
    have hn : z ∈ (range c)ᶜ := hcover ▸ (show z ∈ A ∪ B from Or.inl hz)
    exact hn hl
  refine ⟨A, B, hA, hB, hAc, hBc, hAB, hcover, hfa, hfb, hside, ?_⟩
  intro z
  by_cases hz : z ∈ A
  · have hj := (hA.isConnected_iff_isPathConnected.mp hAc).joinedIn x hx z hz
    let γ := hj.somePath
    obtain ⟨b, hb⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).mp
      (isCompact_range γ.continuous).isBounded
    let S := max (R₀ + 1) (b + 1)
    have hS : R₀ < S := by dsimp [S]; linarith [le_max_left (R₀ + 1) (b + 1)]
    refine ⟨S, hS, ?_⟩
    intro R hR
    have hR₀ : R₀ < R := hS.trans hR
    let D := C R hR₀
    have hKR : range γ ⊆ ball (0 : ℂ) R := by
      intro w hw
      have hwb : ‖w‖ ≤ b := by simpa only [mem_closedBall, dist_zero_right] using hb hw
      have hbR : b + 1 ≤ R := (le_max_right _ _).trans hR.le
      rw [mem_ball, dist_zero_right]
      linarith
    have hKA : range γ ⊆ A := by rintro w ⟨t, rfl⟩; exact hj.somePath_mem t
    have hxD : x ∈ D.inside := hanchor R ((le_max_left _ _).trans hR.le)
    have hsub := lineCap_connected_trace_inside (isConnected_range γ.continuous).isPreconnected
      D.inside_open D.outside_open D.disjoint D.cover D.boundary_subset hKR
      (hAline.mono_left hKA) ⟨x, γ.source_mem_range, hxD⟩
    exact ⟨fun hz' => hside R hR₀ hz', fun _ => hsub γ.target_mem_range⟩
  · refine ⟨R₀ + 1, by linarith, ?_⟩
    intro R hR
    exact ⟨fun hz' => hside R (by linarith) hz', fun h => False.elim (hz h)⟩

/-- Exact finite-support interior AND boundary selectors of actual cap regions
stabilize. On-line points remain boundary points rather than being allocated
by a weak limit. The arbitrary weights are honest finite selectors only. -/
theorem pointMetricLine_actual_cap_atomic_selectors
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {R₀ s : ℝ} (hsR : ‖c s‖ < R₀) (hds : DifferentiableAt ℝ c s) (hvs : deriv c s ≠ 0)
    (C : ∀ R : ℝ, R₀ < R → LineCapGeometry c R) :
    ∃ A : Set ℂ, ∃ S : ℝ, ∃ hS : R₀ < S, ∀ R (hR : S < R),
      (∀ j, y j ∈ (C R (hS.trans hR)).inside ↔ y j ∈ A) ∧
      (∀ j, y j ∈ frontier (C R (hS.trans hR)).inside ↔ y j ∈ range c) ∧
      ∀ w : Fin m → ℝ,
        (∑ j, if y j ∈ (C R (hS.trans hR)).inside then w j else 0) =
          ∑ j, if y j ∈ A then w j else 0 := by
  classical
  obtain ⟨A, B, _, _, _, _, _, _, _, _, _, hexhaust⟩ :=
    pointMetricLine_actual_cap_side_exhaustion ha y c hd hsR hds hvs C
  choose S hS hmem using fun j : Fin m => hexhaust (y j)
  obtain ⟨A₀, hA₀, hatoms⟩ := lineCap_all_atoms_below_radius y
  let M := max (R₀ + 1) (max A₀ (∑ j, max (S j) 0))
  have hM : R₀ < M := by dsimp [M]; linarith [le_max_left (R₀ + 1) (max A₀ (∑ j, max (S j) 0))]
  have hSM (j : Fin m) : S j ≤ M := by
    apply (le_max_left (S j) 0).trans
    apply le_trans (Finset.single_le_sum (fun i _ => le_max_right (S i) 0) (Finset.mem_univ j))
    exact (le_max_right A₀ _).trans (le_max_right _ _)
  refine ⟨A, M, hM, ?_⟩
  intro R hR
  have hR₀ : R₀ < R := hM.trans hR
  let D := C R hR₀
  have hi (j : Fin m) : y j ∈ D.inside ↔ y j ∈ A := hmem j R ((hSM j).trans_lt hR)
  have hA₀R : A₀ ≤ R := ((le_max_left A₀ _).trans (le_max_right _ _)).trans hR.le
  refine ⟨hi, lineCap_atomic_boundary_support_stable y D.radius_pos D.disk_preimage
    (hatoms R hA₀R) D.frontier_inside, ?_⟩
  intro w
  apply Finset.sum_congr rfl
  intro j _
  rw [hi j]

end RepulsiveCoulomb
