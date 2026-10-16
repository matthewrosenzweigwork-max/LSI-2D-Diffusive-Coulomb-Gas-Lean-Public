module

public import LeanResearch.RepulsiveCoulomb.PointChosenRadialGapTriple
public import LeanResearch.RepulsiveCoulomb.JordanThreePieceGap

@[expose] public section

/-! Actual C¹ regular embedded representatives of puncture gaps, retaining
both exact affine radial germs in the charts chosen once per physical vertex.
Artificial joins are removed by changing only the middle parameter, and all
intersection hypotheses for gluing are proved from geodesic injectivity. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- This interval-image fact is applied to the actual injective geodesic,
not supplied as an additional drawing hypothesis. -/
theorem injective_adjacent_interval_images_inter_subset {X Y : Type*}
    [LinearOrder X] {f : X → Y} (hi : Function.Injective f) (s u t : X) :
    f '' Icc s u ∩ f '' Icc u t ⊆ {f u} := by
  rintro z ⟨⟨v, hv, hvz⟩, ⟨w, hw, hwz⟩⟩
  have hvw : v = w := hi (hvz.trans hwz.symm)
  subst w
  have hvu : v = u := le_antisymm hv.2 hw.1
  exact hvz.symm.trans (congrArg f hvu)

/-- All data are obtained from the literal metric, its given geodesic, and
the absence of interior punctures. Neither a C¹ representative nor a local
radial boundary drawing is an input. -/
theorem exists_pointConformal_chosen_radial_C1_gap {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p q : ℂ} (hpq : p ≠ q)
    (γ : Icc (0 : ℝ) 1 → ℂ)
    (hd : ∀ u v, (pointSmoothConformalEDist a y (γ u) (γ v)).toReal =
      |v.1 - u.1| * (pointSmoothConformalEDist a y p q).toReal)
    (s t : Icc (0 : ℝ) 1) (hst : s < t)
    (hgap : ∀ u ∈ Ioo s t, γ u ∉ pointPunctures a y) :
    ∃ l r : Icc (0 : ℝ) 1, s < l ∧ l < r ∧ r < t ∧
      ∃ η : ℝ → ℂ, ContDiff ℝ 1 η ∧ InjOn η (Icc (0 : ℝ) 1) ∧
        (∀ u ∈ Icc (0 : ℝ) 1, deriv η u ≠ 0) ∧
        η 0 = γ s ∧ η 1 = γ t ∧ η '' Icc (0 : ℝ) 1 = γ '' Icc s t ∧
        η =ᶠ[𝓝 (0 : ℝ)] (fun u : ℝ =>
          (pointChosenSmoothRadialChart ha y (γ s)).symm
            ((3 * u) • (pointChosenSmoothRadialChart ha y (γ s)) (γ l))) ∧
        η =ᶠ[𝓝 (1 : ℝ)] (fun u : ℝ =>
          (pointChosenSmoothRadialChart ha y (γ t)).symm
            ((3 * (1 - u)) • (pointChosenSmoothRadialChart ha y (γ t)) (γ r))) := by
  obtain ⟨G⟩ := exists_pointConformal_chosen_radial_gap_triple ha y hpq γ hd s t hst hgap
  obtain ⟨φ, hφ, _, _, _, _, _, hM, hMi, hMr, hM0, hM1, hMd0, hMd1, hMimage⟩ :=
    exists_middle_only_collar_velocity_reparameterization G.leftSpeed_pos G.rightSpeed_pos
      G.middleArc.smooth G.middleArc.injective G.middleArc.regular G.left_jet G.right_jet
  have hLi : G.leftArc.curve '' Icc (0 : ℝ) 1 = γ '' Icc s G.leftCut := by
    rw [G.leftArc.image, G.left_start, G.left_finish]
  have hMi' : (G.middleArc.curve ∘ φ) '' Icc (0 : ℝ) 1 =
      γ '' Icc G.leftCut G.rightCut := by
    rw [hMimage, G.middleArc.image, G.middle_start, G.middle_finish]
  have hRi : G.rightArc.curve '' Icc (0 : ℝ) 1 = γ '' Icc G.rightCut t := by
    rw [G.rightArc.image, G.right_start, G.right_finish]
  have hL1 : G.leftArc.curve 1 = γ G.leftCut := by rw [G.leftArc.at_one, G.left_finish]
  have hM0' : (G.middleArc.curve ∘ φ) 0 = γ G.leftCut := by
    rw [hM0, G.middleArc.at_zero, G.middle_start]
  have hM1' : (G.middleArc.curve ∘ φ) 1 = γ G.rightCut := by
    rw [hM1, G.middleArc.at_one, G.middle_finish]
  have hR0 : G.rightArc.curve 0 = γ G.rightCut := by rw [G.rightArc.at_zero, G.right_start]
  have hi := pointConformal_geodesic_injective ha y hpq γ hd
  have hLMmeet : G.leftArc.curve '' Icc (0 : ℝ) 1 ∩
      (G.middleArc.curve ∘ φ) '' Icc (0 : ℝ) 1 ⊆ {G.leftArc.curve 1} := by
    rw [hLi, hMi', hL1]
    exact injective_adjacent_interval_images_inter_subset hi s G.leftCut G.rightCut
  have hMRmeet : (G.middleArc.curve ∘ φ) '' Icc (0 : ℝ) 1 ∩
      G.rightArc.curve '' Icc (0 : ℝ) 1 ⊆ {(G.middleArc.curve ∘ φ) 1} := by
    rw [hMi', hRi, hM1']
    exact injective_adjacent_interval_images_inter_subset hi G.leftCut G.rightCut t
  have hLR : Disjoint (G.leftArc.curve '' Icc (0 : ℝ) 1)
      (G.rightArc.curve '' Icc (0 : ℝ) 1) := by
    rw [hLi, hRi]
    apply Set.disjoint_left.mpr
    rintro z ⟨u, hu, huz⟩ ⟨v, hv, hvz⟩
    have huv : u = v := hi (huz.trans hvz.symm)
    subst v
    exact (not_le.mpr G.middle_lt) (hv.1.trans hu.2)
  obtain ⟨η, hη, hηi, hηr, hη0, hη1, hηimage, hηL, hηR⟩ :=
    exists_three_piece_regular_C1_gap (G.leftArc.smooth.of_le (by simp))
      (hM.of_le (by simp)) (G.rightArc.smooth.of_le (by simp))
      (hL1.trans hM0'.symm) (hM1'.trans hR0.symm) hMd0.symm hMd1
      G.leftArc.regular hMr G.rightArc.regular G.leftArc.injective hMi G.rightArc.injective
      hLMmeet hMRmeet hLR
  refine ⟨G.leftCut, G.rightCut, G.left_lt, G.middle_lt, G.right_lt,
    η, hη, hηi, hηr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hη0, G.leftArc.at_zero, G.left_start]
  · rw [hη1, G.rightArc.at_one, G.right_finish]
  · rw [hηimage, hLi, hMi', hRi, ← image_union,
      Icc_union_Icc_eq_Icc G.left_lt.le G.middle_lt.le, ← image_union,
      Icc_union_Icc_eq_Icc (G.left_lt.trans G.middle_lt).le G.right_lt.le]
  · have hmap : Tendsto (fun u : ℝ => 3 * u) (𝓝 0) (𝓝 0) := by
      have h : Continuous (fun u : ℝ => 3 * u) := by fun_prop
      simpa only [mul_zero] using h.tendsto 0
    exact hηL.trans ((G.left_radial 0 (by norm_num)).comp_tendsto hmap)
  · have hmap : Tendsto (fun u : ℝ => 3 * u - 2) (𝓝 1) (𝓝 1) := by
      have h : Continuous (fun u : ℝ => 3 * u - 2) := by fun_prop
      simpa only [mul_one, show (3 : ℝ) - 2 = 1 by norm_num] using h.tendsto 1
    have hgerm := (G.right_radial 1 (by norm_num)).comp_tendsto hmap
    filter_upwards [hηR, hgerm] with u hu hv
    simp only [Function.comp_def] at hv
    rw [hu, hv]
    congr 2
    ring

end RepulsiveCoulomb
