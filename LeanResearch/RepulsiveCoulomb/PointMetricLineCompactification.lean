import LeanResearch.RepulsiveCoulomb.PointMetricRaySegments
import LeanResearch.RepulsiveCoulomb.PlanarProperRayCompactification
import LeanResearch.RepulsiveCoulomb.PlanarClosedRayTopology
import LeanResearch.RepulsiveCoulomb.PointGeodesicJordanBigon

/-! An actual minimizing complete line has two proper rays, a nonempty planar
complement, and an actual Jordan compactification under inversion. This is the
topological entry to constructing its two side regions. No plane-straightening
map, halfplane metric, or curvature-balance certificate is assumed. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- The two literal halves are proper embedded rays with exactly one common
point, and their union is the entire supplied complete line. -/
theorem pointMetricLine_half_rays {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ℓ : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (ℓ s) (ℓ t)).toReal = dist s t) :
    IsClosedEmbedding (fun t : NNReal ↦ ℓ (t : ℝ)) ∧
      IsClosedEmbedding (fun t : NNReal ↦ ℓ (-(t : ℝ))) ∧
      range (fun t : NNReal ↦ ℓ (t : ℝ)) ∩
        range (fun t : NNReal ↦ ℓ (-(t : ℝ))) = {ℓ 0} ∧
      range (fun t : NNReal ↦ ℓ (t : ℝ)) ∪
        range (fun t : NNReal ↦ ℓ (-(t : ℝ))) = range ℓ := by
  have hpos : ∀ s t : NNReal,
      (pointSmoothConformalEDist a y (ℓ (s : ℝ)) (ℓ (t : ℝ))).toReal = dist s t := by
    intro s t
    rw [hd, Real.dist_eq, NNReal.dist_eq]
  have hneg : ∀ s t : NNReal,
      (pointSmoothConformalEDist a y (ℓ (-(s : ℝ))) (ℓ (-(t : ℝ)))).toReal = dist s t := by
    intro s t
    rw [hd, Real.dist_eq, NNReal.dist_eq, neg_sub_neg, abs_sub_comm]
  have hinj := (pointMetricLine_isClosedEmbedding ha y ℓ hd).injective
  refine ⟨pointMetricRay_isClosedEmbedding ha y _ hpos,
    pointMetricRay_isClosedEmbedding ha y _ hneg, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
      have he : (s : ℝ) = -(t : ℝ) := hinj (hs.trans ht.symm)
      have hs0 : (s : ℝ) = 0 :=
        le_antisymm (by rw [he]; exact neg_nonpos.mpr t.2) s.2
      exact mem_singleton_iff.mpr (hs.symm.trans (congrArg ℓ hs0))
    · intro hz
      have hz0 : z = ℓ 0 := mem_singleton_iff.mp hz
      subst z
      exact ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩
  · ext z
    constructor
    · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
      · exact mem_range_self _
      · exact mem_range_self _
    · rintro ⟨t, rfl⟩
      by_cases ht : 0 ≤ t
      · exact Or.inl ⟨⟨t, ht⟩, rfl⟩
      · refine Or.inr ⟨⟨-t, neg_nonneg.mpr (le_of_not_ge ht)⟩, ?_⟩
        change ℓ (-(-t)) = ℓ t
        rw [neg_neg]

/-- A complete minimizing line does not fill the complex plane. The proof is
the actual cut-point argument applied to its two literal proper rays. -/
theorem pointMetricLine_compl_nonempty {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ℓ : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (ℓ s) (ℓ t)).toReal = dist s t) :
    (range ℓ)ᶜ.Nonempty := by
  obtain ⟨hp, hn, hmeet, hunion⟩ := pointMetricLine_half_rays ha y ℓ hd
  have h := complex_closed_ray_attachment_compl_nonempty hn.isClosed_range hp
    (by simpa using hmeet)
  rwa [union_comm, hunion] at h

/-- Inversion sends the two proper halves to compact arcs meeting exactly at
their common finite endpoint and the new point at infinity. -/
theorem compactifiedPlanarRay_pair_intersection {f g : NNReal → ℂ} {q p : ℂ}
    (hf0 : f 0 = q) (hg0 : g 0 = q) (hmeet : range f ∩ range g = {q}) :
    range (compactifiedPlanarRay p f) ∩ range (compactifiedPlanarRay p g) =
      {planarInversion p q, 0} := by
  rw [range_compactifiedPlanarRay, range_compactifiedPlanarRay]
  ext z
  constructor
  · rintro ⟨hzf, hzg⟩
    by_cases hz0 : z = 0
    · simp only [hz0, mem_insert_iff, mem_singleton_iff, or_true]
    · rcases hzf with hz | ⟨x, hxf, hxz⟩
      · exact False.elim (hz0 hz)
      · rcases hzg with hz | ⟨w, hwg, hwz⟩
        · exact False.elim (hz0 hz)
        · have hxw := planarInversion_injective p (hxz.trans hwz.symm)
          have hxq : x = q := mem_singleton_iff.mp (hmeet ▸ And.intro hxf (by simpa only [hxw] using hwg))
          exact Or.inl (hxz.symm.trans (congrArg (planarInversion p) hxq))
  · intro hz
    rcases mem_insert_iff.mp hz with hzq | hz0
    · subst z
      exact ⟨Or.inr ⟨q, ⟨0, hf0⟩, rfl⟩, Or.inr ⟨q, ⟨0, hg0⟩, rfl⟩⟩
    · have he : z = 0 := mem_singleton_iff.mp hz0
      subst z
      exact ⟨Or.inl rfl, Or.inl rfl⟩

/-- The literal inverted line plus its point at infinity is a genuine Jordan
curve in the approved planar coordinates. -/
theorem pointMetricLine_inverted_jordan {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ℓ : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (ℓ s) (ℓ t)).toReal = dist s t)
    {p : ℂ} (hp : p ∉ range ℓ) :
    Schoenflies.IsJordanCurve
      (Complex.orthonormalBasisOneI.repr '' insert 0 (planarInversion p '' range ℓ)) := by
  obtain ⟨hpos, hneg, hmeet, hunion⟩ := pointMetricLine_half_rays ha y ℓ hd
  let f : NNReal → ℂ := fun t ↦ ℓ (t : ℝ)
  let g : NNReal → ℂ := fun t ↦ ℓ (-(t : ℝ))
  have hpf : p ∉ range f := fun h ↦ hp (hunion ▸ Or.inl h)
  have hpg : p ∉ range g := fun h ↦ hp (hunion ▸ Or.inr h)
  let F := compactifiedPlanarRay p f
  let G := compactifiedPlanarRay p g
  have hF := compactifiedPlanarRay_isClosedEmbedding hpos hpf
  have hG := compactifiedPlanarRay_isClosedEmbedding hneg hpg
  have hF0 : F ⟨0, by norm_num⟩ = planarInversion p (ℓ 0) := by
    change compactifiedPlanarRay p f 0 = _
    rw [compactifiedPlanarRay_zero]
    rfl
  have hG0 : G ⟨0, by norm_num⟩ = planarInversion p (ℓ 0) := by
    change compactifiedPlanarRay p g 0 = _
    rw [compactifiedPlanarRay_zero]
    change planarInversion p (ℓ (-((0 : NNReal) : ℝ))) = _
    rw [NNReal.coe_zero, neg_zero]
  have hF1 : F ⟨1, by norm_num⟩ = 0 := compactifiedPlanarRay_one p f
  have hG1 : G ⟨1, by norm_num⟩ = 0 := compactifiedPlanarRay_one p g
  have hFG : range F ∩ range G = {planarInversion p (ℓ 0), 0} :=
    compactifiedPlanarRay_pair_intersection (by simp [f]) (by simp [g]) hmeet
  let e := Complex.orthonormalBasisOneI.repr
  have hFA := isArcBetween_of_continuous_injective_interval (e ∘ F)
    (e.continuous.comp hF.continuous) (e.injective.comp hF.injective)
  have hGA := isArcBetween_of_continuous_injective_interval (e ∘ G)
    (e.continuous.comp hG.continuous) (e.injective.comp hG.injective)
  simp only [Function.comp_apply, hF0, hG0, hF1, hG1] at hFA hGA
  have hintersection : range (e ∘ F) ∩ range (e ∘ G) =
      {e (planarInversion p (ℓ 0)), e 0} := by
    rw [range_comp, range_comp, ← image_inter e.injective, hFG, image_insert_eq, image_singleton]
  have hJ := Schoenflies.IsJordanCurve.two_arcs_of_two_arcs hFA hGA hintersection
  have hcarrier : range F ∪ range G = insert 0 (planarInversion p '' range ℓ) := by
    rw [range_compactifiedPlanarRay, range_compactifiedPlanarRay,
      insert_union, union_insert, insert_idem, ← image_union, hunion]
  rw [range_comp, range_comp, ← image_union, hcarrier] at hJ
  exact hJ

end RepulsiveCoulomb
