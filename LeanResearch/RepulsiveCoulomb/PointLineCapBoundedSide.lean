import LeanResearch.RepulsiveCoulomb.PointLineCapJordan
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-! Records-only, uncompiled. A constructed bounded cap lies in the actual
large disk and entirely in one of the actual open sides of the complete line.
This does not assume or assert which fixed side is selected as R varies. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem lineCap_bounded_region_subset_ball {U : Set ℂ} {R : ℝ}
    (hU : IsOpen U) (hK : IsCompact (closure U))
    (hfront : ∀ z ∈ frontier U, ‖z‖ ≤ R) (hR : R ≠ 0) :
    U ⊆ ball (0 : ℂ) R := by
  have hclosed : U ⊆ closedBall (0 : ℂ) R := by
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    exact Complex.norm_le_of_forall_mem_frontier_norm_le
      (hK.isBounded.subset subset_closure) differentiable_id.diffContOnCl hfront (subset_closure hz)
  have h := hU.subset_interior_iff.mpr hclosed
  simpa only [interior_closedBall _ hR] using h

/-- The Jordan cap cannot contain an exterior tail: the tails lie outside the
disk and the central line segment is its actual boundary. -/
theorem lineCap_bounded_region_disjoint_line {c : ℝ → ℂ} {tm tp R α β : ℝ}
    {U : Set ℂ} (hU : IsOpen U) (hK : IsCompact (closure U)) (hR : 0 < R)
    (hinside : ∀ t, ‖c t‖ < R ↔ t ∈ Ioo tm tp)
    (hends : ‖c tm‖ = R ∧ ‖c tp‖ = R)
    (hfront : frontier U = c '' Icc tm tp ∪ pointCircleCapArc R α β '' Icc (0 : ℝ) 1) :
    U ⊆ ball (0 : ℂ) R ∧ Disjoint U (range c) := by
  have hboundary : ∀ z ∈ frontier U, ‖z‖ ≤ R := by
    intro z hz
    rw [hfront] at hz
    rcases hz with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · by_cases hm : t = tm
      · simpa only [hm, hends.1] using (le_rfl : R ≤ R)
      by_cases hp : t = tp
      · simpa only [hp, hends.2] using (le_rfl : R ≤ R)
      exact ((hinside t).mpr ⟨lt_of_le_of_ne ht.1 (Ne.symm hm),
        lt_of_le_of_ne ht.2 hp⟩).le
    · exact (pointCircleCapArc_norm hR.le α β t).le
  have hball := lineCap_bounded_region_subset_ball hU hK hboundary hR.ne'
  refine ⟨hball, disjoint_left.mpr ?_⟩
  rintro z hz ⟨t, rfl⟩
  have hnorm : ‖c t‖ < R := by simpa only [mem_ball, dist_zero_right] using hball hz
  have ht := (hinside t).mp hnorm
  have hbd : c t ∈ frontier U := hfront.symm ▸ Or.inl ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
  exact (hU.frontier_eq ▸ hbd).2 hz

/-- Connectedness forces each actual cap wholly into one genuine side. The
choice has not been replaced by the conclusion that all radii pick one side. -/
theorem lineCap_bounded_region_in_one_line_side {c : ℝ → ℂ}
    {U A B : Set ℂ} (hUc : IsConnected U) (hdisj : Disjoint U (range c))
    (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hcover : A ∪ B = (range c)ᶜ) : U ⊆ A ∨ U ⊆ B := by
  apply IsPreconnected.subset_or_subset hA hB hAB ?_ hUc.isPreconnected
  intro z hz
  rw [hcover]
  exact fun hline => disjoint_left.mp hdisj hz hline

end RepulsiveCoulomb
