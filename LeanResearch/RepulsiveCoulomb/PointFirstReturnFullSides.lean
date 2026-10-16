module

public import LeanResearch.RepulsiveCoulomb.PointFirstReturnFiniteGBData
public import LeanResearch.RepulsiveCoulomb.FirstReturnOldBoundaryLocalEquality

@[expose] public section

/-! Source-only draft. Every actual finite first-return corner, including
zero-mass vertices, has an actual full positive Jordan interval. At an old
vertex away from the stopped ray, cap containment forces this same interval
to describe P. Thus the full directed cap interval is not assumed equal to P. -/
noncomputable section
open Set Filter Metric
open scoped BigOperators Topology
namespace RepulsiveCoulomb

/-- The full-side and physical-transition conclusions apply at ALL vertices.
This strengthens the positive-atom-only circle-cap consumer for first returns. -/
theorem PointFirstReturnFiniteGBData.vertex_physical_side
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {arcs : ℕ → PointRadialC1PlaneArc ha y} {n : ℕ} {U V : Set ℂ}
    (H : PointFirstReturnFiniteGBData ha y arcs n U V)
    (hU : IsOpen U) (hUc : IsConnected U) (hV : IsOpen V) (hVc : IsConnected V)
    (hdisj : Disjoint U V) (hK : IsCompact (closure U))
    (hcover : U ∪ V = (⋃ i ≤ n, (arcs i).curve '' Icc (0 : ℝ) 1)ᶜ)
    (hfrontU : frontier U = ⋃ i ≤ n, (arcs i).curve '' Icc (0 : ℝ) 1)
    (hfrontV : frontier V = ⋃ i ≤ n, (arcs i).curve '' Icc (0 : ℝ) 1)
    {k : ℕ} (hk : k ≤ n) :
    ∃ E F : OpenPartialHomeomorph ℂ ℂ, ∃ δ : ℝ,
      0 < δ ∧ ball (0 : ℂ) δ ⊆ E.target ∧
      (∀ z ∈ ball (0 : ℂ) δ, E.symm z ∈ closure U ↔
        z ∈ lineClosedInitialSector δ (H.angle k)) ∧
      (∀ z ∈ ball (0 : ℂ) δ, E.symm z ∈ closure V ↔
        z ∈ lineClosedTerminalSector δ (H.angle k)) ∧
      (H.oriented k).curve 0 ∈ F.source ∧ F ((H.oriented k).curve 0) = 0 ∧ F.source ⊆ E.source ∧
      (∀ z, F z = coneRadialEquiv (coalescedPointExponent a y ((H.oriented k).curve 0) / 2)
        (div_nonneg (coalescedPointExponent_nonneg a y ((H.oriented k).curve 0)) (by norm_num)) (E z)) ∧
      (∀ u ∈ F.source, ∀ v ∈ F.source,
        (pointSmoothConformalEDist a y u v).toReal =
          pointClassicalConeDist a y ((H.oriented k).curve 0) (F u) (F v)) := by
  obtain ⟨G, q, hq, hGsrc, hG⟩ := H.radial_corner k hk
  have hcover : U ∪ V = (⋃ i ≤ n, (fun i => (H.oriented i).curve) i '' Icc (0 : ℝ) 1)ᶜ := by
    rw [H.carrier]
    exact hcover
  have hpC : (fun i => (H.oriented i).curve) k 0 ∈ (⋃ i ≤ n, (arcs i).curve '' Icc (0 : ℝ) 1) := by
    rw [← H.carrier]
    exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, ⟨0, by norm_num, rfl⟩⟩⟩
  obtain ⟨δ, hδ, hball, hboundary, hinside, houtside⟩ := G.actual_full_inside_sector
    (fun i _ => (H.oriented i).smooth.continuous) H.simple hU hUc
    hV hVc hdisj hK hcover
    (frontier_subset_closure (hfrontU.symm ▸ hpC))
    (frontier_subset_closure (hfrontV.symm ▸ hpC)) H.observer_inside H.observerAngle
    H.observer_continuous (fun i hi t _ => H.observer_lift i hi t) H.observer_turn
  have hfrontBU : frontier U = ⋃ i ≤ n, (fun i => (H.oriented i).curve) i '' Icc (0 : ℝ) 1 := by
    rw [H.carrier]
    exact hfrontU
  have hfrontBV : frontier V = ⋃ i ≤ n, (fun i => (H.oriented i).curve) i '' Icc (0 : ℝ) 1 := by
    rw [H.carrier]
    exact hfrontV
  have hpart := pointDiskRay_complement_eq_sectors hδ G.angle_pos G.angle_lt
  have hpart' : ball (0 : ℂ) δ \ (pointDiskRay δ 0 ∪ pointDiskRay δ (H.angle k)) =
      pointOpenRadialSector δ (H.angle k) (2 * Real.pi) ∪ pointOpenRadialSector δ 0 (H.angle k) := by
    simpa only [union_comm] using hpart
  obtain ⟨F, hpF, hF0, hFsrc, hF, hmetric, _⟩ :=
    exists_pointCorner_physical_metric_transition ha y G.chart hq hGsrc hG
  exact ⟨G.chart, F, δ, hδ, hball,
    fun z hz => chart_closed_side_membership hdisj hcover hfrontBU G.chart hboundary hpart hinside houtside z hz,
    fun z hz => chart_closed_side_membership hdisj.symm (by simpa only [union_comm] using hcover)
      hfrontBV G.chart hboundary hpart' houtside hinside z hz,
    hpF, hF0, hFsrc, hF, hmetric⟩


/-- At an old-arc vertex outside the stopped ray, the complete normalized
initial interval constructed by mixed GB is a literal local interval for P.
The halfplane/cap local equality is proved inside the body. This remains valid
when the retained physical width is reflex. -/
theorem PointFirstReturnFiniteGBData.old_vertex_full_interval
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {arcs : ℕ → PointRadialC1PlaneArc ha y} {n : ℕ} {U V P K A : Set ℂ}
    (D : PointFirstReturnFiniteGBData ha y arcs n U V)
    (T : ℂ ≃ₜ ℂ) (hP : P = T ⁻¹' planarClosedUpperHalfplane)
    (hU : IsOpen U) (hUc : IsConnected U) (hV : IsOpen V) (hVc : IsConnected V)
    (hdisj : Disjoint U V) (hcompact : IsCompact (closure U))
    (hcover : U ∪ V = (⋃ i ≤ n, (arcs i).curve '' Icc (0 : ℝ) 1)ᶜ)
    (hfrontU : frontier U = ⋃ i ≤ n, (arcs i).curve '' Icc (0 : ℝ) 1)
    (hfrontV : frontier V = ⋃ i ≤ n, (arcs i).curve '' Icc (0 : ℝ) 1)
    (hUP : closure U ⊆ P) (hK : IsClosed K) (hA : A ⊆ frontier P)
    (hboundary : frontier U = K ∪ A)
    {k : ℕ} (hk : k ≤ n) (hpK : (D.oriented k).curve 0 ∉ K) :
    ∃ E F : OpenPartialHomeomorph ℂ ℂ, ∃ δ r : ℝ,
      0 < r ∧ r ≤ δ ∧ ball (0 : ℂ) δ ⊆ E.target ∧
      (∀ z ∈ ball (0 : ℂ) r, E.symm z ∈ P ↔
        z ∈ lineClosedInitialSector δ (D.angle k)) ∧
      (D.oriented k).curve 0 ∈ F.source ∧ F ((D.oriented k).curve 0) = 0 ∧ F.source ⊆ E.source ∧
      (∀ z, F z = coneRadialEquiv (coalescedPointExponent a y ((D.oriented k).curve 0) / 2)
        (div_nonneg (coalescedPointExponent_nonneg a y ((D.oriented k).curve 0)) (by norm_num)) (E z)) ∧
      (∀ u ∈ F.source, ∀ v ∈ F.source,
        (pointSmoothConformalEDist a y u v).toReal =
          pointClassicalConeDist a y ((D.oriented k).curve 0) (F u) (F v)) := by
  obtain ⟨E, F, δ, hδ, hball, hinside, _, hpF, hF0, hFsrc, hF, hmetric⟩ :=
    D.vertex_physical_side hU hUc hV hVc hdisj hcompact hcover hfrontU hfrontV hk
  have hpC : (D.oriented k).curve 0 ∈ frontier U := by
    rw [hfrontU, ← D.carrier]
    exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, ⟨0, by norm_num, rfl⟩⟩⟩
  obtain ⟨W, hW, hpW, _, _, hsame⟩ :=
    firstReturn_cap_old_boundary_local_equality T hP hU hUP hK hA hboundary hpC hpK
  have hpE := hFsrc hpF
  have hE0 : E ((D.oriented k).curve 0) = 0 := by
    apply (coneRadialEquiv (coalescedPointExponent a y ((D.oriented k).curve 0) / 2)
      (div_nonneg (coalescedPointExponent_nonneg a y ((D.oriented k).curve 0)) (by norm_num))).injective
    rw [← hF, hF0, coneRadialEquiv_zero]
  have h0E : (0 : ℂ) ∈ E.target := hE0 ▸ E.mapsTo hpE
  have hinv : E.symm 0 = (D.oriented k).curve 0 := by rw [← hE0, E.left_inv hpE]
  have hpre : E.symm ⁻¹' W ∈ 𝓝 (0 : ℂ) := by
    apply (E.symm.continuousAt h0E).preimage_mem_nhds
    rw [hinv]
    exact hW.mem_nhds hpW
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  let r := min ε δ
  refine ⟨E, F, δ, r, lt_min hε hδ, min_le_right _ _, hball, ?_,
    hpF, hF0, hFsrc, hF, hmetric⟩
  intro z hz
  have hzW : E.symm z ∈ W := hεsub (ball_subset_ball (min_le_left ε δ) hz)
  have hmem : E.symm z ∈ closure U ↔ E.symm z ∈ P := by
    have he := Set.ext_iff.mp hsame (E.symm z)
    simpa only [mem_inter_iff, hzW, true_and] using he
  exact hmem.symm.trans (hinside z (ball_subset_ball (min_le_right ε δ) hz))

/-- When an independently supplied retained interval is expressed in the same
normalized oriented chart, literal membership determines the ENTIRE width and
signed coefficient. No principal-angle or cosine identification is used. The
conversion of a separate arbitrary retained chart to this chart is not claimed. -/
theorem firstReturn_old_normalized_interval_signed_turn
    {P : Set ℂ} (E : OpenPartialHomeomorph ℂ ℂ)
    {r R S θ φ κ ν : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hrS : r ≤ S)
    (hθ : 0 < θ) (hθ2 : θ < 2 * Real.pi)
    (hφ : 0 < φ) (hφ2 : φ < 2 * Real.pi)
    (hcapP : ∀ z ∈ ball (0 : ℂ) r,
      E.symm z ∈ P ↔ z ∈ lineClosedInitialSector R θ)
    (hretained : ∀ z ∈ ball (0 : ℂ) r,
      E.symm z ∈ P ↔ z ∈ lineClosedInitialSector S φ)
    (hν : ν = Real.pi - (1 + κ / 2) * φ) :
    θ = φ ∧ Real.pi - (1 + κ / 2) * θ = ν := by
  have heq := lineClosedInitialSector_width_unique hr hrR hrS hθ hθ2 hφ hφ2
    (fun z hz => (hcapP z hz).symm.trans (hretained z hz))
  exact ⟨heq, by rw [heq, hν]⟩

end RepulsiveCoulomb
