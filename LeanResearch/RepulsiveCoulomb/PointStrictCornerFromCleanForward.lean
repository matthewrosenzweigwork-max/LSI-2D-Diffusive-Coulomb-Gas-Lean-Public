import LeanResearch.RepulsiveCoulomb.PointZeroCornerStripExhaustion

/-!
SOURCE-ONLY, UNCOMPILED. Positive residual angle is derived at the actual
finite-width corner from an actual clean opposite boundary end. The proof
rules out zero angle by whole-region exhaustion and the original positive
budget. Neither strict angle, exact contact, nor exhaustion is an input.

The separate original outermost/no-clean construction must identify that
opposite extreme with this corner in the zero-angle branch. The sharp two-atom
budget helper performs the coefficient part of that identification.
-/
noncomputable section
open Set
namespace RepulsiveCoulomb.PointTranslatedRegularData.FiniteWidthLimit
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j}
  {P : Set ℂ} {ν α : ℂ →₀ ℝ} {D : PointTranslatedRegularData a y ha P ν α}
  (T : D.FiniteWidthLimit)

/-- A clean forward old end is actual geometric data. Its existence is not
deduced from an arbitrary ambient geodesic extension or assumed as a residual
certificate. Once it is present, all zero-angle geometric implications are
proved here using the attained map. -/
theorem corner_residual_positive_of_clean_forward
    (C : PointRetainedConeNeighborhood a y P
      (T.map (translatedStripTop T.positive.le 0)).1) (hC : C.Admissible)
    (g : NNReal → P)
    (hg : @Isometry NNReal P inferInstance
      (pointRegionMetricSpace ha y P).toPseudoEMetricSpace g)
    (hg0 : g 0 = T.map (translatedStripTop T.positive.le 0))
    (hfront : ∀ t, (g t).1 ∈ frontier P)
    (hclean : Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {(g 0).1})
      (range (fun t ↦ (g t).1)))
    (hforward : ∀ t : NNReal, 0 < t →
      (g t).1 ∉ range (fun r ↦ (T.map (translatedStripBottom T.positive.le r)).1) ∪
        range (fun u ↦ (T.map (translatedStripEdge u)).1)) :
    Real.pi - D.angle < C.flatPhysicalWidth := by
  have hnonneg := T.corner_residual_nonnegative C hC
  by_contra hn
  have hzero : C.flatPhysicalWidth = Real.pi - D.angle := by
    have hle := le_of_not_gt hn
    linarith
  have htop := T.top_eq_clean_forward_of_zero_corner C hC hzero g hg hg0 hfront hclean hforward
  have htopfront : ∀ r : NNReal,
      (T.map (translatedStripTop T.positive.le r)).1 ∈ frontier P := by
    intro r
    exact (congrArg Subtype.val (congrFun htop r)).symm ▸ hfront r
  have honto := T.surjective_of_zero_corner_and_boundary_top C hC hzero htopfront
  obtain ⟨_, _, hαp, hαz, _, _, _⟩ := T.zero_corner_consequences C hC hzero
  apply pointSignedBudgetInvariant.not_support_on_two_zero_atoms D.budget hαp hαz
  intro x hx
  by_cases hxp : x = (D.ray 0).1
  · exact Or.inl hxp
  · right
    by_contra hxz
    let xp : P := ⟨x, D.allocation_support x hx⟩
    obtain ⟨q, hq⟩ := honto xp
    have hqx : (T.map q).1 = x := congrArg Subtype.val hq
    have hmarked : x ∈ pointSignedMarked ν α :=
      (mem_pointSignedMarked ν α x).mpr (Or.inr hx)
    obtain ⟨r, hr, u, hu, hqu⟩ := q.2
    by_cases hub : u < sSup D.regularWidths
    · have hqe : q = ⟨flatShearedPoint (conePhase D.angle) r u,
          r, hr, u, hu, rfl⟩ := Subtype.ext hqu
      have hbad : (T.map q).1 ∈
          (↑(pointSignedMarked ν α) : Set ℂ) \ {(D.ray 0).1} := by
        rw [hqx]
        exact ⟨hmarked, hxp⟩
      exact T.below_unmarked ⟨r, hr⟩ ⟨u, hu⟩ hub (hqe ▸ hbad)
    · have hueq : u = sSup D.regularWidths := le_antisymm hu.2 (le_of_not_gt hub)
      have hqt : q = translatedStripTop T.positive.le (⟨r, hr⟩ : NNReal) := by
        apply Subtype.ext
        change q.1 = flatShearedPoint (conePhase D.angle) r (sSup D.regularWidths)
        simpa only [hueq] using hqu
      have hgr : (g (⟨r, hr⟩ : NNReal)).1 = x :=
        (congrArg Subtype.val (congrFun htop ⟨r, hr⟩)).symm.trans
          ((congrArg (fun w ↦ (T.map w).1) hqt.symm).trans hqx)
      have hxg0 : x ≠ (g 0).1 := by
        intro he
        exact hxz (he.trans (congrArg Subtype.val hg0))
      exact (Set.disjoint_left.mp hclean) ⟨hmarked, hxg0⟩ ⟨⟨r, hr⟩, hgr⟩

end RepulsiveCoulomb.PointTranslatedRegularData.FiniteWidthLimit
