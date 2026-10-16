module

public import LeanResearch.RepulsiveCoulomb.PointRetainedSectorRelativeOpenness
public import LeanResearch.RepulsiveCoulomb.TranslatedStripResidualTopology
public import LeanResearch.RepulsiveCoulomb.PlanarOldBoundaryComplementRay
public import LeanResearch.RepulsiveCoulomb.PointMetricRaySegments

@[expose] public section

/-!
SOURCE-ONLY, NOT COMPILED. Actual global residual construction after the
independent no-return theorem has proved exact old-boundary contact. The old
complementary boundary ray is constructed by the exact real-clock theorem.
No old complementary ray, new line, component, residual
homeomorphism, residual identity, retained chart or update is an input.
-/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- Construct the bent-boundary halfplane and identify the LITERAL closed
residual. Relative openness and connectedness of the actual sector below its
free edge are outputs of the preceding actual source geometry modules. -/
theorem pointRetainedSector_construct_residual_of_contact
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z, (pointSmoothConformalEDist a y (σ x) (σ z)).toReal = dist x z)
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hHP : P = H ⁻¹' planarClosedUpperHalfplane)
    (hσP : ∀ x, σ x ∈ P)
    (hbottom : ∀ u : NNReal, σ (retainedApexBottomSource hβ.le hβπ u) ∈ frontier P)
    (hOld : ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p, C.Admissible)
    (hregular : ∀ x : closedEuclideanSector β,
      0 < ‖x.1‖ → 0 < Complex.arg x.1 → Complex.arg x.1 < β →
        σ x ∈ interior P ∧ coalescedPointExponent a y (σ x) = 0)
    (hcontact : range σ ∩ frontier P =
      range (fun u : NNReal ↦ σ (retainedApexBottomSource hβ.le hβπ u)))
    :
    let S := range σ
    let top := fun u : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ u)
    let Q := closure (P \ S)
    ∃ g : NNReal → ℂ, IsClosedEmbedding g ∧ g 0 = σ (flatLinkSectorApex hβ.le) ∧
    ∃ D : PlanarLineHalfplaneHomeomorphs (planarTwoRayJoin top g),
      Pᶜ ∪ (S \ range top) = D.positive ∧
      interior P \ S = D.negative ∧
      Q = closure D.negative ∧ Q = P \ (S \ range top) ∧ Q ⊆ P ∧
      frontier Q = range top ∪ (frontier P \ S) ∧
      Nonempty (Q ≃ₜ planarClosedUpperHalfplane) ∧
      (∀ u : NNReal, 0 < (u:ℝ) → top u ∈ interior P) := by
  let p := σ (flatLinkSectorApex hβ.le)
  let top := fun u : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ u)
  let bottom := fun u : NNReal ↦ σ (retainedApexBottomSource hβ.le hβπ u)
  let S := range σ
  have hP : IsClosed P := by
    rw [hHP]
    exact (isClosed_le continuous_const Complex.continuous_im).preimage H.continuous
  have htop0 : top 0 = p := congrArg σ (Subtype.ext (sectorPolar_zero β))
  have hbottom0 : bottom 0 = p := congrArg σ (Subtype.ext (sectorPolar_zero 0))
  have hpfront : p ∈ frontier P := hbottom0 ▸ hbottom 0
  have hSP : S ⊆ P := by rintro z ⟨x,rfl⟩; exact hσP x
  have hTS : range top ⊆ S := by rintro z ⟨u,rfl⟩; exact mem_range_self _
  have hBS : range bottom ⊆ S := by rintro z ⟨u,rfl⟩; exact mem_range_self _
  have hbmetric (u v : NNReal) :
      (pointSmoothConformalEDist a y (bottom u) (bottom v)).toReal = dist u v := by
    rw [hσ]
    change dist (sectorPolar u 0) (sectorPolar v 0) = dist (u:ℝ) (v:ℝ)
    simp only [sectorPolar,conePhase,Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one]
    exact Complex.isometry_ofReal.dist_eq _ _
  have hbclosed := pointMetricRay_isClosedEmbedding ha y bottom hbmetric
  obtain ⟨g,hg,hg0,hgimage,hgS⟩ := exists_straightened_oldBoundary_complement_ray H hHP
    hbclosed hbottom0 hcontact.symm
  have hgfront : range g ⊆ frontier P := by
    rw [hgimage]
    intro z hz
    rcases mem_insert_iff.mp hz with he | hz
    · exact he.symm ▸ hpfront
    · exact hz.1
  have htopint (u : NNReal) (hu : 0 < (u:ℝ)) : top u ∈ interior P := by
    by_contra hi
    have hf : top u ∈ frontier P := ⟨subset_closure (hσP _),hi⟩
    have hb : top u ∈ range bottom := hcontact ▸ And.intro (mem_range_self _) hf
    exact retainedApex_free_ray_avoids_bottom y hβ hβπ σ hσ u hu hb
  have htmetric (u v : NNReal) :
      (pointSmoothConformalEDist a y (top u) (top v)).toReal = dist u v :=
    (hσ _ _).trans ((retainedApexUpperSource_isometry hβ.le hβπ).dist_eq u v)
  have htclosed := pointMetricRay_isClosedEmbedding ha y top htmetric
  have hzero : top 0 = g 0 := htop0.trans hg0.symm
  have hmeet : range top ∩ range g = {top 0} := by
    ext z
    constructor
    · rintro ⟨⟨u,hu⟩,hzg⟩
      by_cases hu0 : u = 0
      · rw [mem_singleton_iff]
        simpa only [hu0] using hu.symm
      · have hup : 0 < (u:ℝ) := lt_of_le_of_ne u.2
          (fun he ↦ hu0 (Subtype.ext he.symm))
        have hi : z ∈ interior P := hu ▸ htopint u hup
        exact False.elim ((hgfront hzg).2 hi)
    · intro hz
      have he : z = top 0 := mem_singleton_iff.mp hz
      exact ⟨⟨0,he.symm⟩,⟨0,hzero.symm.trans he.symm⟩⟩
  have hline : range (planarTwoRayJoin top g) = range top ∪ (frontier P \ S) := by
    rw [planarTwoRayJoin_range hzero,hgimage]
    ext z
    constructor
    · rintro (hz | hz)
      · exact Or.inl hz
      · rcases mem_insert_iff.mp hz with he | hz
        · exact Or.inl ⟨0,htop0.trans he.symm⟩
        · exact Or.inr hz
    · rintro (hz | hz)
      · exact Or.inl hz
      · exact Or.inr (mem_insert_of_mem _ hz)
  have hbottomOneS : bottom 1 ∈ S := mem_range_self _
  have hbottomOneNotTop : bottom 1 ∉ range top := by
    rintro ⟨u,hu⟩
    have hnorm := hσ (retainedApexUpperSource hβ.le hβπ u) (flatLinkSectorApex hβ.le)
    have hnormB := hσ (retainedApexBottomSource hβ.le hβπ 1) (flatLinkSectorApex hβ.le)
    change (pointSmoothConformalEDist a y (top u) p).toReal =
      dist (sectorPolar u β) 0 at hnorm
    change (pointSmoothConformalEDist a y (bottom 1) p).toReal =
      dist (sectorPolar 1 0) 0 at hnormB
    rw [hu, dist_zero_right, sectorPolar_norm (NNReal.coe_nonneg u)] at hnorm
    rw [dist_zero_right, sectorPolar_norm (show (0 : ℝ) ≤ 1 by norm_num)] at hnormB
    have he : (u:ℝ) = 1 := hnorm.symm.trans hnormB
    have huP : 0 < (u:ℝ) := by rw [he]; norm_num
    have hbi : bottom 1 ∈ interior P := hu ▸ htopint u huP
    exact (hbottom 1).2 hbi
  have hbelow : bottom 1 ∈ S \ range top := ⟨hbottomOneS,hbottomOneNotTop⟩
  have hnotline : bottom 1 ∉ range (planarTwoRayJoin top g) := by
    rw [hline]
    rintro (ht | hf)
    · exact hbottomOneNotTop ht
    · exact hf.2 hbottomOneS
  obtain ⟨D,hpositive⟩ := exists_planarTwoRayJoin_halfplaneHomeomorphs_positive_at
    htclosed hg hzero hmeet hnotline
  obtain ⟨hclosed,_⟩ := pointRetainedSector_closed_proper ha y hβ hβπ σ hσ
  have hSclosed : IsClosed S := hclosed.isClosed_range
  have hrelative := pointRetainedSector_without_free_ray_relative_open ha y hβ hβπ σ hσ
    hσP hbottom hOld hregular
  have hconn := retainedSector_without_free_ray_connected hβ hβπ σ hclosed.continuous hclosed.injective
  have houtside := translatedCut_old_exterior_connected H hHP
  obtain ⟨hA,hR,hcl,_,hQeq,hQP,hfrontQ,hhomeo⟩ := translatedCut_identify_actual_sides D
    hP hSclosed hSP hTS hline hrelative houtside hconn hbelow (hbottom 1) hpositive
  refine ⟨g,hg,hg0,D,hA,hR,hcl,hQeq,hQP,?_,hhomeo,htopint⟩
  exact hfrontQ.trans hline

end RepulsiveCoulomb
