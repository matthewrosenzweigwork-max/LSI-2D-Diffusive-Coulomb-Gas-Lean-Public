import LeanResearch.RepulsiveCoulomb.PointFiniteBoundaryRayContacts
import LeanResearch.RepulsiveCoulomb.PlanarLineHalfplaneSides
import LeanResearch.RepulsiveCoulomb.FiniteClosedIntervalCoverSubdivision
import LeanResearch.RepulsiveCoulomb.PointOrderedBoundaryRadialChains

/-! Successor draft. The actual finite old geodesic-piece cover is sufficient:
its pullback to any simple compact old-boundary arc is a finite closed interval
cover. Literal contained geodesics give the local macro-chains, and finite
transition-time recursion assembles the whole original boundary subarc. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

def unitIntervalAffineSegment (s t : unitInterval) (u : unitInterval) : unitInterval :=
  ⟨(1 - u.1) * s.1 + u.1 * t.1,
    convex_Icc (0 : ℝ) 1 s.2 t.2 (sub_nonneg.mpr u.2.2) u.2.1 (by ring)⟩

@[simp] theorem unitIntervalAffineSegment_zero (s t : unitInterval) :
    unitIntervalAffineSegment s t 0 = s := by
  apply Subtype.ext
  simp [unitIntervalAffineSegment]

@[simp] theorem unitIntervalAffineSegment_one (s t : unitInterval) :
    unitIntervalAffineSegment s t 1 = t := by
  apply Subtype.ext
  simp [unitIntervalAffineSegment]

theorem unitIntervalAffineSegment_continuous (s t : unitInterval) :
    Continuous (unitIntervalAffineSegment s t) := by
  unfold unitIntervalAffineSegment
  fun_prop

theorem unitIntervalAffineSegment_strictMono {s t : unitInterval} (hst : s < t) :
    StrictMono (unitIntervalAffineSegment s t) := by
  intro u v huv
  change (1 - u.1) * s.1 + u.1 * t.1 < (1 - v.1) * s.1 + v.1 * t.1
  nlinarith [mul_pos (show 0 < v.1 - u.1 from sub_pos.mpr huv)
    (show 0 < t.1 - s.1 from sub_pos.mpr hst)]

theorem unitIntervalAffineSegment_range {s t : unitInterval} (hst : s < t) :
    range (unitIntervalAffineSegment s t) = Icc s t := by
  have hI : Icc (0 : unitInterval) 1 = univ := by
    apply eq_univ_of_forall
    exact fun u => u.2
  have he := (unitIntervalAffineSegment_continuous s t).image_Icc_of_strictMono
    (unitIntervalAffineSegment_strictMono hst) (a := (0 : unitInterval)) (b := 1)
  simpa only [hI, image_univ, unitIntervalAffineSegment_zero,
    unitIntervalAffineSegment_one] using he

theorem real_simple_unit_arc_range {f : unitInterval → ℝ}
    (hf : Continuous f) (hi : Function.Injective f) : range f = uIcc (f 0) (f 1) := by
  have hI : uIcc (0 : unitInterval) 1 = univ := by
    rw [uIcc_of_le (by norm_num)]
    apply eq_univ_of_forall
    exact fun u => u.2
  rcases hf.strictMono_of_inj hi with hm | hm
  · simpa only [hI, image_univ] using
      hf.continuousOn.image_uIcc_of_monotoneOn (a := (0 : unitInterval)) (b := 1)
        (hm.monotone.monotoneOn _)
  · simpa only [hI, image_univ] using
      hf.continuousOn.image_uIcc_of_antitoneOn (a := (0 : unitInterval)) (b := 1)
        (hm.antitone.antitoneOn _)

/-- The real coordinate of a genuine boundary straightening is injective on
that actual frontier. No metric/geodesic property of the entire line is used. -/
theorem straightened_boundary_coordinate_injective
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hP : P = H ⁻¹' planarClosedUpperHalfplane) :
    InjOn (fun z => (H z).re) (frontier P) := by
  have hfront : frontier P = H ⁻¹' {z : ℂ | z.im = 0} := by
    rw [hP, ← H.preimage_frontier]
    exact congrArg (fun S : Set ℂ => H ⁻¹' S) (Complex.frontier_setOfPred_le_im 0)
  intro p hp q hq he
  apply H.injective
  apply Complex.ext he
  have hp0 : (H p).im = 0 := by simpa only [hfront, mem_preimage, mem_setOf_eq] using hp
  have hq0 : (H q).im = 0 := by simpa only [hfront, mem_preimage, mem_setOf_eq] using hq
  exact hp0.trans hq0.symm

/-- Two genuine simple arcs in an actual topological boundary line, with the
same oriented endpoints, have the same trace. This supplies the needed old
subarc equality for a minimizing segment constructed in one actual old piece. -/
theorem boundary_simple_arcs_same_trace
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hP : P = H ⁻¹' planarClosedUpperHalfplane)
    (γ η : unitInterval → ℂ) (hγ : Continuous γ) (hη : Continuous η)
    (hγi : Function.Injective γ) (hηi : Function.Injective η)
    (hγP : ∀ u, γ u ∈ frontier P) (hηP : ∀ u, η u ∈ frontier P)
    (h0 : γ 0 = η 0) (h1 : γ 1 = η 1) : range γ = range η := by
  let F : ℂ → ℝ := fun z => (H z).re
  have hF : Continuous F := Complex.continuous_re.comp H.continuous
  have hFi := straightened_boundary_coordinate_injective H hP
  have hFγi : Function.Injective (F ∘ γ) := by
    intro u v he
    exact hγi (hFi (hγP u) (hγP v) he)
  have hFηi : Function.Injective (F ∘ η) := by
    intro u v he
    exact hηi (hFi (hηP u) (hηP v) he)
  have hcoord : range (F ∘ γ) = range (F ∘ η) := by
    rw [real_simple_unit_arc_range (hF.comp hγ) hFγi,
      real_simple_unit_arc_range (hF.comp hη) hFηi]
    simp only [Function.comp_apply, h0, h1]
  apply Subset.antisymm
  · rintro z ⟨u, rfl⟩
    obtain ⟨v, hv⟩ : F (γ u) ∈ range (F ∘ η) := hcoord ▸ mem_range_self u
    exact ⟨v, hFi (hηP v) (hγP u) hv⟩
  · rintro z ⟨v, rfl⟩
    obtain ⟨u, hu⟩ : F (η v) ∈ range (F ∘ γ) := hcoord.symm ▸ mem_range_self v
    exact ⟨u, hFi (hγP u) (hηP v) hu⟩

/-- Pullbacks of the actual old geodesic pieces are closed order intervals on
any simple compact boundary parametrization, even when cover members overlap. -/
theorem boundary_arc_finite_piece_contacts
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hP : P = H ⁻¹' planarClosedUpperHalfplane)
    (E : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P = ⋃ i, range (E i).curve)
    (b : unitInterval → ℂ) (hb : Continuous b) (hbi : Function.Injective b)
    (hbP : ∀ u, b u ∈ frontier P) :
    (∀ i, IsClosed (b ⁻¹' range (E i).curve)) ∧
      (∀ i, OrdConnected (b ⁻¹' range (E i).curve)) ∧
      ∀ u, ∃ i, b u ∈ range (E i).curve := by
  let F : ℂ → ℝ := fun z => (H z).re
  have hF : Continuous F := Complex.continuous_re.comp H.continuous
  have hFi := straightened_boundary_coordinate_injective H hP
  have hE (i : Fin N) : range (E i).curve ⊆ frontier P := by
    rw [hpieces]
    exact subset_iUnion (fun j : Fin N => range (E j).curve) i
  have hFb : Function.Injective (F ∘ b) := by
    intro u v he
    exact hbi (hFi (hbP u) (hbP v) he)
  have hmono := (hF.comp hb).strictMono_of_inj hFb
  refine ⟨fun i => ((E i).closedEmbedding ha y).isClosed_range.preimage hb, ?_, ?_⟩
  · intro i
    letI : PreconnectedSpace (E i).interval := Subtype.preconnectedSpace (E i).interval_convex.isPreconnected
    have hK : IsPreconnected (F '' range (E i).curve) :=
      (isPreconnected_range ((E i).closedEmbedding ha y).continuous).image F hF.continuousOn
    have hJ : b ⁻¹' range (E i).curve = (F ∘ b) ⁻¹' (F '' range (E i).curve) := by
      ext u
      constructor
      · intro hu
        exact ⟨b u, hu, rfl⟩
      · rintro ⟨z, hz, he⟩
        have heq : z = b u := hFi (hE i hz) (hbP u) he
        change b u ∈ range (E i).curve
        rwa [← heq]
    rw [hJ]
    exact hmono.elim (fun h => hK.ordConnected.preimage_mono h.monotone)
      (fun h => hK.ordConnected.preimage_anti h.antitone)
  · intro u
    have h := hbP u
    rw [hpieces] at h
    exact mem_iUnion.mp h

/-- Construct the actual complete old-boundary radial macro-chain directly
from the finite geodesic-piece cover. Local trace equality is proved, not an
input. All ambient positive atoms on the old arc are allowed and subdivided by
the accepted metric-segment constructor. -/
theorem exists_actual_old_boundary_radial_chain
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hP : P = H ⁻¹' planarClosedUpperHalfplane)
    (E : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P = ⋃ i, range (E i).curve)
    (b : unitInterval → ℂ) (hb : Continuous b) (hbi : Function.Injective b)
    (hbP : ∀ u, b u ∈ frontier P) :
    ∃ L, PointBoundaryRadialChainOn ha y b 0 1 L := by
  obtain ⟨hclosed, hinterval, hcover⟩ := boundary_arc_finite_piece_contacts ha y H hP E hpieces b hb hbi hbP
  obtain ⟨Q, hQ⟩ := finite_closed_interval_cover_transition_times
    (fun i => b ⁻¹' range (E i).curve) hclosed hinterval hcover
  apply exists_boundary_radial_chain_of_finite_exceptions ha y b hbi Q _ 0 1 (by norm_num)
  intro s t hst hgap
  obtain ⟨i, hi⟩ := hQ s t hst hgap
  have hsE : b s ∈ range (E i).curve := hi ⟨le_rfl, hst.le⟩
  have htE : b t ∈ range (E i).curve := hi ⟨hst.le, le_rfl⟩
  obtain ⟨γ, h0, h1, hc, hγE, hd⟩ := (E i).geodesicallyConvex ha y (b s) hsE (b t) htE
  have hneq : b s ≠ b t := fun he => hst.ne (hbi he)
  have hγi := pointConformal_geodesic_injective ha y hneq γ hd
  let η := b ∘ unitIntervalAffineSegment s t
  have hη : Continuous η := hb.comp (unitIntervalAffineSegment_continuous s t)
  have hηi : Function.Injective η := hbi.comp (unitIntervalAffineSegment_strictMono hst).injective
  have hγP : ∀ u, γ u ∈ frontier P := by
    intro u
    rw [hpieces]
    exact mem_iUnion.mpr ⟨i, hγE u⟩
  have hηP : ∀ u, η u ∈ frontier P := fun u => hbP _
  have hη0 : η 0 = b s := by simp only [η, Function.comp_apply, unitIntervalAffineSegment_zero]
  have hη1 : η 1 = b t := by simp only [η, Function.comp_apply, unitIntervalAffineSegment_one]
  have htrace : range γ = b '' Icc s t := by
    rw [boundary_simple_arcs_same_trace H hP γ η hc hη hγi hηi hγP hηP
      (h0.trans hη0.symm) (h1.trans hη1.symm), range_comp, unitIntervalAffineSegment_range hst]
  exact exists_boundary_radial_chain_of_metric_subarc ha y b hbi hst γ h0 h1 hd htrace

end RepulsiveCoulomb
