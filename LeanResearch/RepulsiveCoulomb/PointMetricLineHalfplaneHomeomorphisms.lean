module

public import LeanResearch.RepulsiveCoulomb.PointMetricLineStraightening
public import LeanResearch.RepulsiveCoulomb.PlanarLineHalfplaneSides

@[expose] public section

/-! Genuine initial closed topological halfplanes. Every field below is
constructed from an actual proper isometric line, rather than assumed as a
halfplane certificate. The topology is the ordinary complex subspace topology. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- Output data, including the actual complementary components, their literal
closures, and homeomorphisms respecting every point of the oriented line. -/
structure PlanarLineHalfplaneHomeomorphs (ℓ : ℝ → ℂ) where
  straightening : ℂ ≃ₜ ℂ
  on_line : ∀ t : ℝ, straightening (ℓ t) = (t : ℂ)
  positive : Set ℂ
  negative : Set ℂ
  positive_eq : positive = straightening ⁻¹' planarOpenUpperHalfplane
  negative_eq : negative = straightening ⁻¹' planarOpenLowerHalfplane
  positive_open : IsOpen positive
  negative_open : IsOpen negative
  positive_connected : IsConnected positive
  negative_connected : IsConnected negative
  disjoint : Disjoint positive negative
  cover : positive ∪ negative = (range ℓ)ᶜ
  positive_frontier : frontier positive = range ℓ
  negative_frontier : frontier negative = range ℓ
  positive_closed_frontier : frontier (closure positive) = range ℓ
  negative_closed_frontier : frontier (closure negative) = range ℓ
  positive_component : ∀ x ∈ positive, connectedComponentIn (range ℓ)ᶜ x = positive
  negative_component : ∀ x ∈ negative, connectedComponentIn (range ℓ)ᶜ x = negative
  positive_homeomorph : closure positive ≃ₜ planarClosedUpperHalfplane
  negative_homeomorph : closure negative ≃ₜ planarClosedUpperHalfplane
  positive_formula : ∀ x : closure positive,
    (positive_homeomorph x : ℂ) = straightening x
  negative_formula : ∀ x : closure negative,
    (negative_homeomorph x : ℂ) = starRingEnd ℂ (straightening x)

/-- Both endpoint boundary maps are the literal parameter `t`, including on the
reflected side. No assertion of ambient orientation preservation is smuggled in. -/
theorem PlanarLineHalfplaneHomeomorphs.boundary_respected {ℓ : ℝ → ℂ}
    (D : PlanarLineHalfplaneHomeomorphs ℓ) (t : ℝ) :
    (D.positive_homeomorph ⟨ℓ t, frontier_subset_closure
      (D.positive_frontier.symm ▸ mem_range_self t)⟩ : ℂ) = (t : ℂ) ∧
    (D.negative_homeomorph ⟨ℓ t, frontier_subset_closure
      (D.negative_frontier.symm ▸ mem_range_self t)⟩ : ℂ) = (t : ℂ) := by
  constructor
  · rw [D.positive_formula, D.on_line]
  · rw [D.negative_formula, D.on_line]
    simp

/-- The boundary correspondence is onto and exact, not merely inclusion of
some line points in the boundary. -/
theorem PlanarLineHalfplaneHomeomorphs.boundary_iff {ℓ : ℝ → ℂ}
    (D : PlanarLineHalfplaneHomeomorphs ℓ) :
    (∀ x : closure D.positive, (D.positive_homeomorph x : ℂ).im = 0 ↔
      (x : ℂ) ∈ range ℓ) ∧
    (∀ x : closure D.negative, (D.negative_homeomorph x : ℂ).im = 0 ↔
      (x : ℂ) ∈ range ℓ) := by
  constructor
  · intro x
    rw [D.positive_formula]
    exact (line_straightening_mem_iff D.straightening D.on_line x).symm
  · intro x
    rw [D.negative_formula]
    simpa only [Complex.conj_im, neg_eq_zero] using
      (line_straightening_mem_iff D.straightening D.on_line x).symm

/-- Convert a proved, parameter-preserving ambient straightening into its two
actual component closures. Both side maps are restrictions of explicit maps. -/
def lineHalfplaneHomeomorphs_of_straightening {ℓ : ℝ → ℂ}
    (H : ℂ ≃ₜ ℂ) (hH : ∀ t : ℝ, H (ℓ t) = (t : ℂ)) :
    PlanarLineHalfplaneHomeomorphs ℓ := by
  have hU := planar_halfplane_partition.1
  have hV := planar_halfplane_partition.2.1
  have hUc := planar_halfplane_partition.2.2.1
  have hVc := planar_halfplane_partition.2.2.2.1
  have hUV := planar_halfplane_partition.2.2.2.2.1
  have hcover := planar_halfplane_partition.2.2.2.2.2.1
  have hfu := planar_halfplane_partition.2.2.2.2.2.2.2.2.1
  have hfv := planar_halfplane_partition.2.2.2.2.2.2.2.2.2
  let U := H ⁻¹' planarOpenUpperHalfplane
  let V := H ⁻¹' planarOpenLowerHalfplane
  have hline : H ⁻¹' {z : ℂ | z.im = 0} = range ℓ := by
    ext z
    exact (line_straightening_mem_iff H hH z).symm
  have hUo : IsOpen U := hU.preimage H.continuous
  have hVo : IsOpen V := hV.preimage H.continuous
  have hUconn : IsConnected U := H.isConnected_preimage.mpr hUc
  have hVconn : IsConnected V := H.isConnected_preimage.mpr hVc
  have hdis : Disjoint U V := hUV.preimage H
  have hcov : U ∪ V = (range ℓ)ᶜ := by
    change (H ⁻¹' planarOpenUpperHalfplane) ∪ (H ⁻¹' planarOpenLowerHalfplane) = _
    rw [← preimage_union, hcover, preimage_compl, hline]
  have hfrontU : frontier U = range ℓ := by
    rw [← H.preimage_frontier, hfu, hline]
  have hfrontV : frontier V = range ℓ := by
    rw [← H.preimage_frontier, hfv, hline]
  have hclosedfrontU : frontier (closure U) = range ℓ := by
    change frontier (closure (H ⁻¹' planarOpenUpperHalfplane)) = range ℓ
    rw [← H.preimage_closure, ← H.preimage_frontier]
    change H ⁻¹' frontier (closure {z : ℂ | 0 < z.im}) = range ℓ
    rw [Complex.closure_setOfPred_lt_im, Complex.frontier_setOfPred_le_im, hline]
  have hclosedfrontV : frontier (closure V) = range ℓ := by
    change frontier (closure (H ⁻¹' planarOpenLowerHalfplane)) = range ℓ
    rw [← H.preimage_closure, ← H.preimage_frontier]
    change H ⁻¹' frontier (closure {z : ℂ | z.im < 0}) = range ℓ
    rw [Complex.closure_setOfPred_im_lt, Complex.frontier_setOfPred_im_le, hline]
  exact
    { straightening := H
      on_line := hH
      positive := U
      negative := V
      positive_eq := rfl
      negative_eq := rfl
      positive_open := hUo
      negative_open := hVo
      positive_connected := hUconn
      negative_connected := hVconn
      disjoint := hdis
      cover := hcov
      positive_frontier := hfrontU
      negative_frontier := hfrontV
      positive_closed_frontier := hclosedfrontU
      negative_closed_frontier := hclosedfrontV
      positive_component := fun _ hx ↦
        component_of_two_open_connected_sets hUo hVo hUconn hdis hcov hx
      negative_component := fun _ hx ↦
        component_of_two_open_connected_sets hVo hUo hVconn hdis.symm
          (by simpa only [union_comm] using hcov) hx
      positive_homeomorph := straighteningUpperHalfplaneHomeomorph H
      negative_homeomorph := straighteningLowerHalfplaneHomeomorph H
      positive_formula := straighteningUpperHalfplaneHomeomorph_apply H
      negative_formula := straighteningLowerHalfplaneHomeomorph_apply H }

/-- Main endpoint: the supplied metric line really bounds two closed Euclidean
halfplanes topologically, and the homeomorphisms respect its boundary parameter.
The assumptions are only nonnegative point weights and the actual isometry law. -/
theorem nonempty_pointMetricLine_halfplaneHomeomorphs {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ℓ : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (ℓ s) (ℓ t)).toReal = dist s t) :
    Nonempty (PlanarLineHalfplaneHomeomorphs ℓ) := by
  obtain ⟨H, hH⟩ := exists_pointMetricLine_parameter_straightening ha y ℓ hd
  exact ⟨lineHalfplaneHomeomorphs_of_straightening H hH⟩

/-- A specified complementary point fixes the side assignment: its actual
component is the positive side. The oriented boundary coordinate is unchanged. -/
theorem exists_pointMetricLine_halfplaneHomeomorphs_positive_at {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ℓ : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (ℓ s) (ℓ t)).toReal = dist s t)
    {p : ℂ} (hp : p ∉ range ℓ) :
    ∃ D : PlanarLineHalfplaneHomeomorphs ℓ, p ∈ D.positive := by
  obtain ⟨H, hpH, hH⟩ := exists_pointMetricLine_parameter_straightening_at_pole ha y ℓ hd hp
  let D := lineHalfplaneHomeomorphs_of_straightening H hH
  refine ⟨D, ?_⟩
  rw [D.positive_eq]
  change 0 < (H p).im
  rw [hpH]
  simp

/-- Align with any pre-existing actual side pair (including the pair returned
by a re-centered half-cone theorem), with a fully explicit alternative. -/
theorem PlanarLineHalfplaneHomeomorphs.align_actual_sides {ℓ : ℝ → ℂ}
    (D : PlanarLineHalfplaneHomeomorphs ℓ) {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hUc : IsConnected U) (hVc : IsConnected V)
    (hUV : Disjoint U V) (hcover : U ∪ V = (range ℓ)ᶜ) :
    (U = D.positive ∧ V = D.negative) ∨ (U = D.negative ∧ V = D.positive) :=
  two_open_connected_partitions_eq_or_swap hU hV hUc hVc hUV hcover
    D.positive_open D.negative_open D.positive_connected D.negative_connected
    D.disjoint D.cover

/-- Homeomorphisms for the literal closures of any supplied actual component
pair. The side-choice disjunction remains visible and is not silently replaced. -/
theorem PlanarLineHalfplaneHomeomorphs.homeomorphs_actual_sides {ℓ : ℝ → ℂ}
    (D : PlanarLineHalfplaneHomeomorphs ℓ) {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hUc : IsConnected U) (hVc : IsConnected V)
    (hUV : Disjoint U V) (hcover : U ∪ V = (range ℓ)ᶜ) :
    ∃ eU : closure U ≃ₜ planarClosedUpperHalfplane,
      ∃ eV : closure V ≃ₜ planarClosedUpperHalfplane,
        ((U = D.positive ∧ V = D.negative) ∧
          (∀ x : closure U, (eU x : ℂ) = D.straightening x) ∧
          (∀ x : closure V, (eV x : ℂ) = starRingEnd ℂ (D.straightening x))) ∨
        ((U = D.negative ∧ V = D.positive) ∧
          (∀ x : closure U, (eU x : ℂ) = starRingEnd ℂ (D.straightening x)) ∧
          (∀ x : closure V, (eV x : ℂ) = D.straightening x)) := by
  rcases D.align_actual_sides hU hV hUc hVc hUV hcover with ⟨hUp, hVn⟩ | ⟨hUn, hVp⟩
  · subst U
    subst V
    exact ⟨D.positive_homeomorph, D.negative_homeomorph,
      Or.inl ⟨⟨rfl, rfl⟩, D.positive_formula, D.negative_formula⟩⟩
  · subst U
    subst V
    exact ⟨D.negative_homeomorph, D.positive_homeomorph,
      Or.inr ⟨⟨rfl, rfl⟩, D.negative_formula, D.positive_formula⟩⟩

end RepulsiveCoulomb
