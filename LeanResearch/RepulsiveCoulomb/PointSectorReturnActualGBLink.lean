module

public import LeanResearch.RepulsiveCoulomb.PointFullSideRetainedChart
public import LeanResearch.RepulsiveCoulomb.PointRetainedWidthInvariance

@[expose] public section

/-! Isolated, uncompiled comparison of the actual GB vertex angle with an
independently CONSTRUCTED retained chart of the same actual cap. The raw-return
frontend constructs that chart; this lemma is not a new geometric assumption. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem PointFirstReturnFiniteGBData.physical_angle_eq_actual_cap_chart
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {arcs : ℕ → PointRadialC1PlaneArc ha y} {n k : ℕ} {U V : Set ℂ}
    (H : PointFirstReturnFiniteGBData ha y arcs n U V) (hk : k ≤ n)
    (D : PointRetainedConeNeighborhood a y (closure U) ((H.oriented k).curve 0))
    (hU : IsOpen U) (hUc : IsConnected U) (hV : IsOpen V) (hVc : IsConnected V)
    (hUV : Disjoint U V) (hcompact : IsCompact (closure U))
    (hcover : U ∪ V = (⋃ i ≤ n, (arcs i).curve '' Icc (0 : ℝ) 1)ᶜ)
    (hfrontU : frontier U = ⋃ i ≤ n, (arcs i).curve '' Icc (0 : ℝ) 1)
    (hfrontV : frontier V = ⋃ i ≤ n, (arcs i).curve '' Icc (0 : ℝ) 1) :
    (1 + coalescedPointExponent a y ((H.oriented k).curve 0) / 2) * H.angle k =
      (1 + coalescedPointExponent a y ((H.oriented k).curve 0) / 2) * (D.hi - D.lo) := by
  obtain ⟨E, F, δ, hδ, _, hinside, _, hpF, hF0, hFsrc, hF, hmetric⟩ :=
    H.vertex_physical_side hU hUc hV hVc hUV hcompact hcover hfrontU hfrontV hk
  obtain ⟨G, _, hGlo, hGhi⟩ := exists_retainedConeNeighborhood_of_full_physical_side
    ha y E F hδ (H.angle_range k hk).1 (H.angle_range k hk).2 hinside
    hpF hF0 hFsrc hF hmetric
  have hsame := G.physical_width_eq D
  simpa only [hGlo, hGhi, sub_zero] using hsame

end RepulsiveCoulomb
