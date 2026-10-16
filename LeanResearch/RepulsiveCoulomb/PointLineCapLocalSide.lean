module

public import LeanResearch.RepulsiveCoulomb.PointLineCapActualFamily
public import LeanResearch.RepulsiveCoulomb.PointLineCapAtomSupport
public import LeanResearch.RepulsiveCoulomb.PointMetricLineHalfConeSides
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Records-only, uncompiled. An actual cap and the fixed line component have
the SAME full local closed side in a common cone chart. This is a local set
identity, including at on-line atoms, rather than a boundary-support claim.
The numerical comparison with the mixed-GB original-germ chart is separate. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem lineCap_open_sector_nonempty {R α β : ℝ} (hR : 0 < R) (hab : α < β) :
    (pointOpenRadialSector R α β).Nonempty := by
  refine ⟨pointRadialSectorPoint (R / 2) ((α + β) / 2), ?_⟩
  exact ⟨(R / 2, (α + β) / 2), ⟨by constructor <;> linarith,
    by constructor <;> linarith⟩, rfl⟩

theorem lineCap_disk_ray_radius_restrict {r R θ : ℝ} (hrR : r ≤ R)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    z ∈ pointDiskRay R θ ↔ z ∈ pointDiskRay r θ := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, ⟨hs.1, by simpa only [mem_ball, dist_zero_right,
      pointRadialSectorPoint_norm hs.1] using hz⟩, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, ⟨hs.1, hs.2.trans_le hrR⟩, rfl⟩

/-- Nested actual regions with the same two-ray local boundary must select
the same sector. Both possible existential side swaps are handled explicitly. -/
theorem lineCap_chart_closed_side_eq
    {L K A B U V : Set ℂ}
    (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hline : A ∪ B = Lᶜ) (hfA : frontier A = L) (hfB : frontier B = L)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcap : U ∪ V = Kᶜ) (hfU : frontier U = K) (hfV : frontier V = K)
    (hUA : U ⊆ A) {p : ℂ} (hpL : p ∈ L) (hpK : p ∈ K)
    (F : OpenPartialHomeomorph ℂ ℂ) (hpF : p ∈ F.source) (hF0 : F p = 0)
    {r θ : ℝ} (hr : 0 < r) (hθ : 0 < θ) (hθ2 : θ < 2 * Real.pi)
    (htarget : ball (0 : ℂ) r ⊆ F.target)
    (hbL : ∀ z ∈ ball (0 : ℂ) r,
      F.symm z ∈ L ↔ z ∈ pointDiskRay r 0 ∪ pointDiskRay r θ)
    (hbK : ∀ z ∈ ball (0 : ℂ) r,
      F.symm z ∈ K ↔ z ∈ pointDiskRay r 0 ∪ pointDiskRay r θ) :
    ∀ z ∈ ball (0 : ℂ) r, F.symm z ∈ closure U ↔ F.symm z ∈ closure A := by
  have hpa : p ∈ closure A := frontier_subset_closure (hfA.symm ▸ hpL)
  have hpb : p ∈ closure B := frontier_subset_closure (hfB.symm ▸ hpL)
  have hpu : p ∈ closure U := frontier_subset_closure (hfU.symm ▸ hpK)
  have hpv : p ∈ closure V := frontier_subset_closure (hfV.symm ▸ hpK)
  have hls := pointRadialChart_region_side_choice hA hB hAB hline hpa hpb F hpF hF0
    hr hθ hθ2 htarget hbL
  have hcs := pointRadialChart_region_side_choice hU hV hUV hcap hpu hpv F hpF hF0
    hr hθ hθ2 htarget hbK
  have hpart := pointDiskRay_complement_eq_sectors hr hθ hθ2
  have hpart' : ball (0 : ℂ) r \ (pointDiskRay r 0 ∪ pointDiskRay r θ) =
      pointOpenRadialSector r θ (2 * Real.pi) ∪ pointOpenRadialSector r 0 θ := by
    simpa only [union_comm] using hpart
  rcases hls with ⟨hSA, hTB⟩ | ⟨hSB, hTA⟩
  · rcases hcs with ⟨hSU, hTV⟩ | ⟨hSV, hTU⟩
    · intro z hz
      exact (chart_closed_side_membership hUV hcap hfU F hbK hpart hSU hTV z hz).trans
        (chart_closed_side_membership hAB hline hfA F hbL hpart hSA hTB z hz).symm
    · obtain ⟨z, hz⟩ := lineCap_open_sector_nonempty hr hθ2
      exact False.elim (disjoint_left.mp hAB (hUA (hTU hz)) (hTB hz))
  · rcases hcs with ⟨hSU, hTV⟩ | ⟨hSV, hTU⟩
    · obtain ⟨z, hz⟩ := lineCap_open_sector_nonempty hr hθ
      exact False.elim (disjoint_left.mp hAB (hUA (hSU hz)) (hSB hz))
    · intro z hz
      exact (chart_closed_side_membership hUV hcap hfU F hbK hpart' hTU hSV z hz).trans
        (chart_closed_side_membership hAB hline hfA F hbL hpart' hTA hSB z hz).symm

/-- Once an actual cap encloses the line point, the two full local sides
coincide in any actual normalized line chart after reducing its radius. -/
theorem LineCapGeometry.local_fixed_side
    {c : ℝ → ℂ} {R : ℝ} (D : LineCapGeometry c R)
    {A B : Set ℂ} (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hcover : A ∪ B = (range c)ᶜ) (hfA : frontier A = range c) (hfB : frontier B = range c)
    (hDA : D.inside ⊆ A) {s : ℝ} (hs : ‖c s‖ < R)
    (F : OpenPartialHomeomorph ℂ ℂ) (hsF : c s ∈ F.source) (hF0 : F (c s) = 0)
    {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ) (hθ2 : θ < 2 * Real.pi)
    (htarget : ball (0 : ℂ) ρ ⊆ F.target)
    (hboundary : ∀ z ∈ ball (0 : ℂ) ρ,
      F.symm z ∈ range c ↔ z ∈ pointDiskRay ρ 0 ∪ pointDiskRay ρ θ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧
      ∀ z ∈ ball (0 : ℂ) r, F.symm z ∈ closure D.inside ↔ F.symm z ∈ closure A := by
  have h0target : (0 : ℂ) ∈ F.target := hF0 ▸ F.mapsTo hsF
  have hinv : F.symm 0 = c s := by rw [← hF0, F.left_inv hsF]
  have hnhds : F.symm ⁻¹' ball (0 : ℂ) R ∈ 𝓝 (0 : ℂ) := by
    apply (F.symm.continuousAt h0target).preimage_mem_nhds
    rw [hinv]
    exact isOpen_ball.mem_nhds (by simpa only [mem_ball, dist_zero_right] using hs)
  obtain ⟨ε, hε, hεmap⟩ := Metric.mem_nhds_iff.mp hnhds
  let r := min ε ρ
  have hr : 0 < r := lt_min hε hρ
  have hrρ : r ≤ ρ := min_le_right _ _
  have hmap : ∀ z ∈ ball (0 : ℂ) r, ‖F.symm z‖ < R := by
    intro z hz
    have hzε : z ∈ ball (0 : ℂ) ε := ball_subset_ball (min_le_left ε ρ) hz
    simpa only [mem_preimage, mem_ball, dist_zero_right] using hεmap hzε
  have hbL : ∀ z ∈ ball (0 : ℂ) r,
      F.symm z ∈ range c ↔ z ∈ pointDiskRay r 0 ∪ pointDiskRay r θ := by
    intro z hz
    rw [hboundary z (ball_subset_ball hrρ hz)]
    exact or_congr (lineCap_disk_ray_radius_restrict hrρ hz)
      (lineCap_disk_ray_radius_restrict hrρ hz)
  have hbK : ∀ z ∈ ball (0 : ℂ) r,
      F.symm z ∈ D.boundary ↔ z ∈ pointDiskRay r 0 ∪ pointDiskRay r θ := by
    intro z hz
    exact (lineCap_boundary_membership_inside_circle D.radius_pos D.disk_preimage (hmap z hz)).trans
      (hbL z hz)
  have hpK : c s ∈ D.boundary :=
    (lineCap_boundary_membership_inside_circle D.radius_pos D.disk_preimage hs).mpr (mem_range_self s)
  exact ⟨r, hr, hrρ, lineCap_chart_closed_side_eq hA hB hAB hcover hfA hfB
    D.inside_open D.outside_open D.disjoint D.cover D.frontier_inside D.frontier_outside
    hDA (mem_range_self s) hpK F hsF hF0 hr hθ hθ2
    (fun z hz => htarget (ball_subset_ball hrρ hz)) hbL hbK⟩

end RepulsiveCoulomb
