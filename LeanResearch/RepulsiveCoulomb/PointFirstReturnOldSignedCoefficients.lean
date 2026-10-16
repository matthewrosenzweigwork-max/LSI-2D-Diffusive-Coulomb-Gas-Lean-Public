module

public import LeanResearch.RepulsiveCoulomb.PointFullSideRetainedChart
public import LeanResearch.RepulsiveCoulomb.PointRetainedWidthInvariance

@[expose] public section

/-! Successor draft. Equality of cap and old-region SET germs plus genuine
metric charts now derives numerical FULL physical width equality, even when
the two original cone charts differ. Signed old coefficients are not supplied
as cap turns. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem exists_pointMetric_closedBall_subset_open
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {W : Set ℂ} {p : ℂ} (hW : IsOpen W) (hp : p ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ε → z ∈ W := by
  have hWm : W ∈ @nhds ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace p := by
    rw [pointSmoothConformalMetricSpace_topology ha y]
    exact hW.mem_nhds hp
  obtain ⟨δ, hδ, hsub⟩ :=
    (@Metric.nhds_basis_ball ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace p).mem_iff.mp hWm
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro z hz
  apply hsub
  change (pointSmoothConformalEDist a y z p).toReal < δ
  linarith

/-- The actual GB angle at an old vertex has the original signed coefficient.
The original coefficient is defined through an arbitrary genuine retained
chart C; the cap chart and equality of its full width to C are constructed. -/
theorem PointFirstReturnFiniteGBData.old_vertex_turn_eq_signed_boundary
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
    {k : ℕ} (hk : k ≤ n) (hpK : (D.oriented k).curve 0 ∉ K)
    (C : PointRetainedConeNeighborhood a y P ((D.oriented k).curve 0))
    {ν : ℝ} (hν : ν = Real.pi -
      (1 + coalescedPointExponent a y ((D.oriented k).curve 0) / 2) * (C.hi - C.lo)) :
    Real.pi - (1 + coalescedPointExponent a y ((D.oriented k).curve 0) / 2) * D.angle k = ν := by
  obtain ⟨E, F, δ, hδ, _, hinside, _, hpF, hF0, hFsrc, hF, hmetric⟩ :=
    D.vertex_physical_side hU hUc hV hVc hdisj hcompact hcover hfrontU hfrontV hk
  obtain ⟨Ccap, _, hlo, hhi⟩ := exists_retainedConeNeighborhood_of_full_physical_side ha y
    E F hδ (D.angle_range k hk).1 (D.angle_range k hk).2 hinside hpF hF0 hFsrc hF hmetric
  have hpC : (D.oriented k).curve 0 ∈ frontier U := by
    rw [hfrontU, ← D.carrier]
    exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, ⟨0, by norm_num, rfl⟩⟩⟩
  obtain ⟨W, hW, hpW, _, _, hsame⟩ :=
    firstReturn_cap_old_boundary_local_equality T hP hU hUP hK hA hboundary hpC hpK
  obtain ⟨ε, hε, hεsub⟩ := exists_pointMetric_closedBall_subset_open ha y hW hpW
  have hwidth := Ccap.physical_width_eq_of_local_eq C hε (fun z hz => by
    have hzW := hεsub z hz
    have he := Set.ext_iff.mp hsame z
    simpa only [mem_inter_iff, hzW, true_and] using he)
  rw [hlo, hhi, sub_zero] at hwidth
  rw [hwidth, hν]

end RepulsiveCoulomb
