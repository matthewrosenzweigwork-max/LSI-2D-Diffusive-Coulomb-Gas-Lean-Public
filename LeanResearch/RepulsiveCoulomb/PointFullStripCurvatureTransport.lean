import LeanResearch.RepulsiveCoulomb.PointFullStripResidualWidths

/-! Exact equality of signed coefficients as functions on the ambient plane.
The old interior coefficient is -pi times the coalesced exponent; the boundary
coefficient is the given genuine retained turn. This is stronger than equality
of a finite sum and does not impose distinctness or positivity of atom weights. -/
noncomputable section
open scoped Classical
open Set Metric Topology
namespace RepulsiveCoulomb

def pointFullStripSignedCoefficient {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (P : Set ℂ) (nu : ℂ → ℝ) (p : ℂ) : ℝ :=
  if p ∈ interior P then -Real.pi * coalescedPointExponent a y p
  else if p ∈ frontier P then nu p else 0

theorem PlanarLineHalfplaneHomeomorphs.negative_interior {line : ℝ → ℂ}
    (D : PlanarLineHalfplaneHomeomorphs line) : interior (closure D.negative) = D.negative := by
  apply Subset.antisymm
  · intro z hz
    have hm : z ∈ D.negative ∪ range line := by
      rw [← D.negative_frontier, ← closure_eq_self_union_frontier]
      exact interior_subset hz
    exact hm.resolve_right (fun ht ↦ (D.negative_closed_frontier.symm ▸ ht).2 hz)
  · exact interior_maximal subset_closure D.negative_open

theorem pointFullStrip_removed_coefficient_zero
    {m : ℕ} {a : Fin m → ℝ} (y : Fin m → ℂ) {P : Set ℂ} {h : ℝ}
    (hh : 0 < h) (F : flatFullNormalStrip h → P)
    (hinj : Function.Injective (fun z ↦ (F z).1))
    (hboundary : frontier P = range (fun r ↦ (F (fullStripBottom hh.le r)).1))
    (hpositive : ∀ z, 0 < z.1.im → (F z).1 ∈ interior P)
    (nu : ℂ → ℝ) (marks : Set ℂ)
    (hmarkedInterior : ∀ p ∈ interior P, coalescedPointExponent a y p ≠ 0 → p ∈ marks)
    (hmarkedBoundary : ∀ p ∈ frontier P, nu p ≠ 0 → p ∈ marks)
    (hcleanBottom : ∀ r, (F (fullStripBottom hh.le r)).1 ∉ marks)
    (hcleanOpen : ∀ z, 0 < z.1.im → z.1.im < h → (F z).1 ∉ marks) :
    ∀ p ∈ range (fun z ↦ (F z).1) \ range (fun r ↦ (F (fullStripTop hh.le r)).1),
      pointFullStripSignedCoefficient a y P nu p = 0 := by
  rintro p ⟨⟨z,rfl⟩,hztop⟩
  have hzt : z.1.im < h := lt_of_le_of_ne z.2.2
    (fun he ↦ hztop ((fullStrip_image_mem_top_iff hh.le hinj z).mpr he))
  by_cases hz0 : z.1.im = 0
  · have he : fullStripBottom hh.le z.1.re = z := Subtype.ext (Complex.ext rfl hz0.symm)
    have hp : (F z).1 ∈ frontier P := by rw [hboundary]; exact ⟨z.1.re, congrArg (fun u ↦ (F u).1) he⟩
    have hn : nu (F z).1 = 0 := by
      by_contra hn
      exact hcleanBottom z.1.re (he.symm ▸ hmarkedBoundary _ hp hn)
    simp only [pointFullStripSignedCoefficient, if_neg hp.2, if_pos hp, hn]
  · have hzpos : 0 < z.1.im := lt_of_le_of_ne z.2.1 (Ne.symm hz0)
    have hp := hpositive z hzpos
    have hzexp : coalescedPointExponent a y (F z).1 = 0 := by
      by_contra hzexp
      exact hcleanOpen z hzpos hzt (hmarkedInterior _ hp hzexp)
    simp only [pointFullStripSignedCoefficient, if_pos hp, hzexp, mul_zero]

/-- Set-theoretic transport once the actual topology and the clean removed
coefficients have been proved. The final endpoint supplies both, rather than
asking for an update witness or a total-mass identity. -/
theorem pointFullStrip_all_point_coefficient_eq
    {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) {P Q S T : Set ℂ}
    (hP : IsClosed P) (hQ : IsClosed Q) (hQP : Q ⊆ P)
    (hinterior : interior Q = P \ S) (hfrontier : frontier Q = T)
    (hTint : T ⊆ interior P) (nu : ℂ → ℝ)
    (hremoved : ∀ p ∈ S \ T, pointFullStripSignedCoefficient a y P nu p = 0) :
    ∀ p, pointFullStripSignedCoefficient a y Q
      (fun z ↦ -Real.pi * coalescedPointExponent a y z) p =
      pointFullStripSignedCoefficient a y P nu p := by
  intro p
  by_cases hpI : p ∈ interior Q
  · have hpP : p ∈ interior P := interior_mono hQP hpI
    simp only [pointFullStripSignedCoefficient, if_pos hpI, if_pos hpP]
  by_cases hpF : p ∈ frontier Q
  · have hpP : p ∈ interior P := hTint (hfrontier ▸ hpF)
    simp only [pointFullStripSignedCoefficient, if_neg hpI, if_pos hpF, if_pos hpP]
  have hpQ : p ∉ Q := fun hp ↦ hpF ⟨hQ.closure_eq.symm ▸ hp,hpI⟩
  by_cases hpP : p ∈ P
  · have hpS : p ∈ S := by
      by_contra hpS
      exact hpI (hinterior.symm ▸ And.intro hpP hpS)
    have hpT : p ∉ T := fun hp ↦ hpF (hfrontier.symm ▸ hp)
    rw [hremoved p ⟨hpS,hpT⟩]
    simp only [pointFullStripSignedCoefficient, if_neg hpI, if_neg hpF]
  · have hpPI : p ∉ interior P := fun hp ↦ hpP (interior_subset hp)
    have hpPF : p ∉ frontier P := fun hp ↦ hpP (hP.frontier_subset hp)
    simp only [pointFullStripSignedCoefficient, if_neg hpI, if_neg hpF, if_neg hpPI, if_neg hpPF]

/-- All ordinary budget-support points are retained on the CLOSED new side.
A support point may be exposed on the top; it is not incorrectly excluded by an
open-side claim. No positivity, nonempty support, or first-contact hypothesis is
needed for a supplied strip. -/
theorem pointFullStrip_budget_support_retained
    {P Q marks budget : Set ℂ} {h : ℝ} (hh : 0 < h) (F : flatFullNormalStrip h → P)
    (hQ : Q = closure (P \ range (fun z ↦ (F z).1)))
    (hfrontier : frontier Q = range (fun r ↦ (F (fullStripTop hh.le r)).1))
    (hbudgetP : budget ⊆ P) (hbudgetMarks : budget ⊆ marks)
    (hcleanBottom : ∀ r, (F (fullStripBottom hh.le r)).1 ∉ marks)
    (hcleanOpen : ∀ z, 0 < z.1.im → z.1.im < h → (F z).1 ∉ marks) : budget ⊆ Q := by
  have hQclosed : IsClosed Q := hQ.symm ▸ isClosed_closure
  intro p hp
  by_cases hpS : p ∈ range (fun z ↦ (F z).1)
  · obtain ⟨z,rfl⟩ := hpS
    have hz0 : z.1.im ≠ 0 := by
      intro hz0
      have he : fullStripBottom hh.le z.1.re = z := Subtype.ext (Complex.ext rfl hz0.symm)
      exact hcleanBottom z.1.re (he.symm ▸ hbudgetMarks hp)
    have hzt : z.1.im = h := by
      by_contra hzt
      exact hcleanOpen z (lt_of_le_of_ne z.2.1 (Ne.symm hz0))
        (lt_of_le_of_ne z.2.2 hzt) (hbudgetMarks hp)
    have ht : (F z).1 ∈ range (fun r ↦ (F (fullStripTop hh.le r)).1) := by
      obtain ⟨r,hr⟩ := (fullStrip_mem_top_range_iff hh.le z).mpr hzt
      exact ⟨r,congrArg (fun u ↦ (F u).1) hr⟩
    exact hQclosed.frontier_subset (hfrontier.symm ▸ ht)
  · rw [hQ]
    exact subset_closure ⟨hbudgetP hp,hpS⟩

end RepulsiveCoulomb
