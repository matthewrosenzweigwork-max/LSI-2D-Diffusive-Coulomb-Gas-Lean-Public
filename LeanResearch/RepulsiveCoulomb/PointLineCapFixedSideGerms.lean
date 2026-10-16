import LeanResearch.RepulsiveCoulomb.PointLineFixedSideAllPoints
import LeanResearch.RepulsiveCoulomb.PointActualCapGaussBonnetData
import LeanResearch.RepulsiveCoulomb.PointLineCapCoalescedVertices
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Uncompiled records-only successor. Cap and fixed-side equality is promoted
from a cone-chart disk to an actual ambient neighborhood germ, then transported
into the original-germ chart used by mixed GB. Both complementary sides remain
explicit. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem region_mem_iff_closure_not_boundary {U V K : Set ℂ}
    (hcover : U ∪ V = Kᶜ) (hfront : frontier U = K) (z : ℂ) :
    z ∈ U ↔ z ∈ closure U ∧ z ∉ K := by
  have hcl : closure U = U ∪ K := by rw [closure_eq_self_union_frontier, hfront]
  constructor
  · intro hz
    refine ⟨subset_closure hz, ?_⟩
    have hUV : z ∈ U ∪ V := Or.inl hz
    rw [hcover] at hUV
    exact hUV
  · rintro ⟨hz, hn⟩
    rw [hcl] at hz
    exact hz.resolve_right hn

theorem region_complement_closure {U V K : Set ℂ}
    (hd : Disjoint U V) (hcover : U ∪ V = Kᶜ) (hfrontV : frontier V = K) :
    closure V = Uᶜ := by
  rw [closure_eq_self_union_frontier, hfrontV]
  ext z
  constructor
  · rintro (hz | hz) hu
    · exact disjoint_left.mp hd hu hz
    · have hUV : z ∈ U ∪ V := Or.inl hu
      rw [hcover] at hUV
      exact hUV hz
  · intro hz
    by_cases hK : z ∈ K
    · exact Or.inr hK
    · exact Or.inl ((show z ∈ U ∪ V from hcover.symm ▸ hK).resolve_left hz)

theorem LineCapGeometry.fixed_side_ambient_germs
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {c : ℝ → ℂ}
    (hd : ∀ u v, (pointSmoothConformalEDist a y (c u) (c v)).toReal = dist u v)
    {R : ℝ} (D : LineCapGeometry c R)
    {A B : Set ℂ} (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hcover : A ∪ B = (range c)ᶜ) (hfA : frontier A = range c) (hfB : frontier B = range c)
    (hDA : D.inside ⊆ A) {s : ℝ} (hs : ‖c s‖ < R) :
    ∀ᶠ z in 𝓝 (c s),
      (z ∈ closure D.inside ↔ z ∈ closure A) ∧
      (z ∈ closure D.outside ↔ z ∈ closure B) := by
  obtain ⟨F, ρ, θ, hρ, hθ, hθ2, hpF, hF0, _, _, _, hlocal⟩ :=
    exists_pointMetricLine_cap_stable_chart_at ha y c hd hA hB hAB hcover hfA hfB s
  obtain ⟨r, hr, _, hsame⟩ := hlocal D hDA hs
  have hmap : ∀ᶠ z in 𝓝 (c s), F z ∈ ball (0 : ℂ) r :=
    (F.continuousAt hpF).preimage_mem_nhds (by rw [hF0]; exact ball_mem_nhds 0 hr)
  have hinside : ∀ᶠ z in 𝓝 (c s), z ∈ closure D.inside ↔ z ∈ closure A := by
    filter_upwards [F.open_source.mem_nhds hpF, hmap] with z hz hzr
    simpa only [F.left_inv hz] using hsame (F z) hzr
  have hnorm : ∀ᶠ z in 𝓝 (c s), ‖z‖ < R :=
    (continuous_norm.continuousAt.eventually (gt_mem_nhds hs))
  have houtD := region_complement_closure D.disjoint D.cover D.frontier_outside
  have houtB := region_complement_closure hAB hcover hfB
  filter_upwards [hinside, hnorm] with z hz hzr
  have hb : z ∈ D.boundary ↔ z ∈ range c :=
    lineCap_boundary_membership_inside_circle D.radius_pos D.disk_preimage hzr
  have hopen : z ∈ D.inside ↔ z ∈ A := by
    exact (region_mem_iff_closure_not_boundary (K := D.boundary) D.cover
      D.frontier_inside z).trans ((and_congr hz (not_congr hb)).trans
        (region_mem_iff_closure_not_boundary hcover hfA z).symm)
  exact ⟨hz, by rw [houtD, houtB]; exact not_congr hopen⟩

/-- The angle read by actual mixed GB is the full interval of the SAME fixed
ambient side, in its actual chosen smooth chart and its explicit radial-power
metric chart. This transports sets, not a short-angle or cosine surrogate. -/
theorem PointActualCapGBData.fixed_side_physical_interval
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {c : ℝ → ℂ}
    (hd : ∀ u v, (pointSmoothConformalEDist a y (c u) (c v)).toReal = dist u v)
    {R : ℝ} {D : LineCapGeometry c R} (H : PointActualCapGBData ha y c D)
    (hy : ∀ j, ‖y j‖ < R)
    {A B : Set ℂ} (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hcover : A ∪ B = (range c)ᶜ) (hfA : frontier A = range c) (hfB : frontier B = range c)
    (hDA : D.inside ⊆ A) {k : ℕ} (hk : k ≤ H.pieces.length)
    (hκ : 0 < coalescedPointExponent a y (H.curve k 0)) :
    ∃ E F : OpenPartialHomeomorph ℂ ℂ, ∃ δ r : ℝ, 0 < r ∧ r ≤ δ ∧
      (∀ z ∈ ball (0 : ℂ) r,
        (E.symm z ∈ closure A ↔ z ∈ lineClosedInitialSector δ (H.angle k)) ∧
        (E.symm z ∈ closure B ↔ z ∈ lineClosedTerminalSector δ (H.angle k))) ∧
      H.curve k 0 ∈ F.source ∧ F (H.curve k 0) = 0 ∧ F.source ⊆ E.source ∧
      (∀ z, F z = coneRadialEquiv (coalescedPointExponent a y (H.curve k 0) / 2)
        (div_nonneg (coalescedPointExponent_nonneg a y (H.curve k 0)) (by norm_num)) (E z)) ∧
      (∀ u ∈ F.source, ∀ v ∈ F.source,
        (pointSmoothConformalEDist a y u v).toReal =
          pointClassicalConeDist a y (H.curve k 0) (F u) (F v)) := by
  obtain ⟨E, F, δ, hδ, hball, hinside, houtside, hpF, hF0, hFsrc, hF, hmetric⟩ :=
    H.positive_vertex_physical_side hk hκ
  have hpLoc := (coalescedPointExponent_pos_iff_location a y _).mp hκ
  obtain ⟨j, _, hj⟩ := (mem_positivePointLocations a y (H.curve k 0)).mp hpLoc
  have hpR : ‖H.curve k 0‖ < R := by rw [← hj]; exact hy j
  have hpCap : H.curve k 0 ∈ D.boundary := by
    rw [← H.carrier]
    exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, ⟨0, by norm_num, rfl⟩⟩⟩
  have hpLine := (lineCap_boundary_membership_inside_circle D.radius_pos D.disk_preimage hpR).mp hpCap
  obtain ⟨s, hs⟩ := hpLine
  have hEp : E (H.curve k 0) = 0 := by
    apply (coneRadialEquiv (coalescedPointExponent a y (H.curve k 0) / 2)
      (div_nonneg (coalescedPointExponent_nonneg a y (H.curve k 0)) (by norm_num))).injective
    rw [← hF, hF0, coneRadialEquiv_zero]
  have hpE := hFsrc hpF
  have h0E : (0 : ℂ) ∈ E.target := hEp ▸ E.mapsTo hpE
  have hinv : E.symm 0 = H.curve k 0 := by rw [← hEp, E.left_inv hpE]
  have hsame := D.fixed_side_ambient_germs ha y hd hA hB hAB hcover hfA hfB hDA (by rwa [hs])
  rw [hs] at hsame
  have hcomp : ∀ᶠ z in 𝓝 (0 : ℂ),
      (E.symm z ∈ closure D.inside ↔ E.symm z ∈ closure A) ∧
      (E.symm z ∈ closure D.outside ↔ E.symm z ∈ closure B) := by
    have hmap : Tendsto E.symm (𝓝 (0 : ℂ)) (𝓝 (H.curve k 0)) := by
      simpa only [hinv] using (E.symm.continuousAt h0E).tendsto
    exact hmap.eventually hsame
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hcomp
  let r := min ε δ
  have hr : 0 < r := lt_min hε hδ
  refine ⟨E, F, δ, r, hr, min_le_right _ _, ?_, hpF, hF0, hFsrc, hF, hmetric⟩
  intro z hz
  have hze := ball_subset_ball (min_le_left ε δ) hz
  have hzδ := ball_subset_ball (min_le_right ε δ) hz
  exact ⟨(hεsub hze).1.symm.trans (hinside z hzδ),
    (hεsub hze).2.symm.trans (houtside z hzδ)⟩

end RepulsiveCoulomb
