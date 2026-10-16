import LeanResearch.RepulsiveCoulomb.PointLineCapBoundedSide
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Records-only, uncompiled. The actual compact-path exhaustion argument.
The inputs are region geometry, boundary location, and a common interior
anchor. There is no exhaustion, atom-membership, or mass assumption. The
common anchor must still be installed from the cap-normal overlap construction. -/
noncomputable section
open Set Metric Topology
open scoped BigOperators
namespace RepulsiveCoulomb

/-- A connected trace avoiding the actual Jordan boundary cannot change sides. -/
theorem lineCap_connected_trace_in_region {K U V C : Set ℂ}
    (hK : IsPreconnected K) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V) (hcover : U ∪ V = Cᶜ)
    (havoid : Disjoint K C) (hmeet : (K ∩ U).Nonempty) : K ⊆ U := by
  have hsub : K ⊆ U ∪ V := by
    intro z hz
    rw [hcover]
    exact fun hC => disjoint_left.mp havoid hz hC
  rcases IsPreconnected.subset_or_subset hU hV hUV hsub hK with h | h
  · exact h
  · obtain ⟨z, hzK, hzU⟩ := hmeet
    exact False.elim (disjoint_left.mp hUV hzU (h hzK))

/-- Enclosing the whole trace, rather than just its endpoints, excludes the
circle portion of the boundary. The line portion is excluded separately. -/
theorem lineCap_connected_trace_inside {c : ℝ → ℂ} {R : ℝ} {K U V C : Set ℂ}
    (hK : IsPreconnected K) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V) (hcover : U ∪ V = Cᶜ)
    (hboundary : C ⊆ range c ∪ sphere (0 : ℂ) R)
    (hball : K ⊆ ball (0 : ℂ) R) (hline : Disjoint K (range c))
    (hmeet : (K ∩ U).Nonempty) : K ⊆ U := by
  apply lineCap_connected_trace_in_region hK hU hV hUV hcover ?_ hmeet
  apply disjoint_left.mpr
  intro z hz hC
  rcases hboundary hC with hl | hs
  · exact disjoint_left.mp hline hz hl
  · have hlt : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hball hz
    have heq : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hs
    exact hlt.ne heq

/-- Overlapping correctly oriented caps are genuinely nested whenever the
later circle encloses the earlier bounded region. -/
theorem lineCap_earlier_region_subset {c : ℝ → ℂ} {r R : ℝ} {W U V C : Set ℂ}
    (hW : IsConnected W) (hWr : W ⊆ ball (0 : ℂ) r) (hrR : r ≤ R)
    (hWline : Disjoint W (range c)) (hmeet : (W ∩ U).Nonempty)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U ∪ V = Cᶜ) (hboundary : C ⊆ range c ∪ sphere (0 : ℂ) R) :
    W ⊆ U :=
  lineCap_connected_trace_inside hW.isPreconnected hU hV hUV hcover hboundary
    (hWr.trans (ball_subset_ball hrR)) hWline hmeet

/-- A point in the actual fixed line component is eventually in every cap
containing the common anchor. The path and its radius bound are constructed
from connectedness, not supplied as another conclusion certificate. -/
theorem lineCap_point_exhaustion_from_anchor {c : ℝ → ℂ} {A : Set ℂ}
    (hA : IsOpen A) (hAc : IsConnected A) (hAline : Disjoint A (range c))
    {x : ℂ} (hx : x ∈ A) (U V C : ℝ → Set ℂ) (R₀ : ℝ)
    (hU : ∀ R, R₀ ≤ R → IsOpen (U R))
    (hV : ∀ R, R₀ ≤ R → IsOpen (V R))
    (hUV : ∀ R, R₀ ≤ R → Disjoint (U R) (V R))
    (hcover : ∀ R, R₀ ≤ R → U R ∪ V R = (C R)ᶜ)
    (hboundary : ∀ R, R₀ ≤ R → C R ⊆ range c ∪ sphere (0 : ℂ) R)
    (hanchor : ∀ R, R₀ ≤ R → x ∈ U R) :
    ∀ z ∈ A, ∃ S : ℝ, R₀ ≤ S ∧ ∀ R, S ≤ R → z ∈ U R := by
  intro z hz
  have hpath := (hA.isConnected_iff_isPathConnected.mp hAc).joinedIn x hx z hz
  let γ := hpath.somePath
  have hK : IsCompact (range γ) := isCompact_range γ.continuous
  obtain ⟨s, hs⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).mp hK.isBounded
  let S := max R₀ (s + 1)
  refine ⟨S, le_max_left _ _, ?_⟩
  intro R hR
  have hR₀ : R₀ ≤ R := (le_max_left _ _).trans hR
  have hKR : range γ ⊆ ball (0 : ℂ) R := by
    intro w hw
    have hws : ‖w‖ ≤ s := by simpa only [mem_closedBall, dist_zero_right] using hs hw
    have hsR : s + 1 ≤ R := (le_max_right _ _).trans hR
    rw [mem_ball, dist_zero_right]
    linarith
  have hKA : range γ ⊆ A := by
    rintro w ⟨t, rfl⟩
    exact hpath.somePath_mem t
  have hKU := lineCap_connected_trace_inside (isConnected_range γ.continuous).isPreconnected
    (hU R hR₀) (hV R hR₀) (hUV R hR₀) (hcover R hR₀) (hboundary R hR₀)
    hKR (hAline.mono_left hKA)
    (show (range γ ∩ U R).Nonempty from ⟨x, γ.source_mem_range, hanchor R hR₀⟩)
  exact hKU γ.target_mem_range

/-- Finitely many actual atom locations admit one common stabilization radius.
Off-side points are excluded by the actual side containment, not by a budget. -/
theorem lineCap_finite_atomic_interior_stability {m : ℕ} (y : Fin m → ℂ)
    {c : ℝ → ℂ} {A : Set ℂ} (hA : IsOpen A) (hAc : IsConnected A)
    (hAline : Disjoint A (range c)) {x : ℂ} (hx : x ∈ A)
    (U V C : ℝ → Set ℂ) (R₀ : ℝ)
    (hU : ∀ R, R₀ ≤ R → IsOpen (U R))
    (hV : ∀ R, R₀ ≤ R → IsOpen (V R))
    (hUV : ∀ R, R₀ ≤ R → Disjoint (U R) (V R))
    (hcover : ∀ R, R₀ ≤ R → U R ∪ V R = (C R)ᶜ)
    (hboundary : ∀ R, R₀ ≤ R → C R ⊆ range c ∪ sphere (0 : ℂ) R)
    (hanchor : ∀ R, R₀ ≤ R → x ∈ U R)
    (hside : ∀ R, R₀ ≤ R → U R ⊆ A) :
    ∃ S : ℝ, R₀ ≤ S ∧ ∀ R, S ≤ R → ∀ j, y j ∈ U R ↔ y j ∈ A := by
  classical
  have hone (j : Fin m) : ∃ S : ℝ, R₀ ≤ S ∧
      ∀ R, S ≤ R → (y j ∈ U R ↔ y j ∈ A) := by
    by_cases hj : y j ∈ A
    · obtain ⟨S, hS, hmem⟩ := lineCap_point_exhaustion_from_anchor hA hAc hAline hx
        U V C R₀ hU hV hUV hcover hboundary hanchor (y j) hj
      exact ⟨S, hS, fun R hR => ⟨fun _ => hj, fun _ => hmem R hR⟩⟩
    · refine ⟨R₀, le_rfl, ?_⟩
      intro R hR
      exact ⟨fun h => hside R hR h, fun h => False.elim (hj h)⟩
  choose S hS hmem using hone
  let M := max R₀ (∑ j, max (S j) 0)
  refine ⟨M, le_max_left _ _, ?_⟩
  intro R hR j
  have hjS : S j ≤ M := by
    apply (le_max_left (S j) 0).trans
    apply le_trans (Finset.single_le_sum (fun i _ => le_max_right (S i) 0) (Finset.mem_univ j))
    exact le_max_right _ _
  exact hmem j R (hjS.trans hR)

end RepulsiveCoulomb
