module

public import LeanResearch.RepulsiveCoulomb.PointLineCapNatLifts
public import LeanResearch.RepulsiveCoulomb.PointLineCapTurnLimit
public import LeanResearch.RepulsiveCoulomb.PointFiniteMixedGaussBonnetGerms
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Order
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! Records-only, uncompiled. Apply mixed original-germ GB to the actual
natural-indexed cap. Everything except the two ordinary endpoint-representative
noncuspidality conditions is constructed from the retained family. Those two
conditions are explicit residual hypotheses, not a claimed consequence here.
No angle value, orientation, boundary mass, or balance identity is assumed. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators Classical
namespace RepulsiveCoulomb

/-- A bounded consumer adapter for the mixed theorem. Its two displayed
join conditions must still be derived by transporting the actual line tangent
to the first/last radial representatives. The conclusion is full signed GB,
including every coalesced boundary atom, with the actual circle contribution. -/
theorem lineCap_nat_mixed_GB_of_two_join_conditions
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {R : ℝ} (D : LineCapGeometry c R) (hy : ∀ j, 2 * ‖y j‖ ≤ R)
    (es : List (PointRadialC1ArcPiece ha y (lineCapSegment c D.minus D.plus)))
    (f : ℕ → ℝ → ℂ) (hn : 0 < es.length)
    (hpieces : ∀ k (hk : k < es.length), f k = (es.get ⟨k, hk⟩).curve)
    (hcircle : f es.length = pointCircleCapArc R D.alpha D.beta)
    (hf : ∀ k ≤ es.length, ContDiff ℝ 1 (f k))
    (hv : ∀ k < es.length, f k 1 = f (k + 1) 0)
    (hclose : f es.length 1 = f 0 0)
    (hreg : ∀ k ≤ es.length, ∀ t ∈ Icc (0 : ℝ) 1, deriv (f k) t ≠ 0)
    (hinj : ∀ i j, i ≤ es.length → j ≤ es.length → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 → f i s = f j t → i = j ∧ s = t)
    (hcarrier : (⋃ k ≤ es.length, f k '' Icc (0 : ℝ) 1) = D.boundary)
    (hjoin0 : deriv (f 0) 0 / deriv (f es.length) 1 ∈ Complex.slitPlane)
    (hjoinN : deriv (f es.length) 0 / deriv (f (es.length - 1)) 1 ∈ Complex.slitPlane) :
    ∃ θ : ℕ → ℝ, (∀ k ≤ es.length, 0 < θ k ∧ θ k < 2 * Real.pi) ∧
      (∀ k ≤ es.length, Complex.arg (deriv (f k) 0 /
        deriv (f (if k = 0 then es.length else k - 1)) 1) = Real.pi - θ k) ∧
      (∀ k ≤ es.length, 0 < coalescedPointExponent a y (f k 0) →
        Nonempty (PointFiniteRadialCornerAt f es.length k (θ k))) ∧
      pointLineCapCircleTurn a y D +
        (∑ k ∈ Finset.range (es.length + 1), (Real.pi -
          (1 + coalescedPointExponent a y (f k 0) / 2) * θ k)) =
        2 * Real.pi + 2 * Real.pi * (∑ j, if y j ∈ D.inside then a j / 2 else 0) := by
  have he := pointMetricLine_isClosedEmbedding ha y c hd
  have hpq : c D.minus ≠ c D.plus := fun h => D.time_lt.ne (he.injective h)
  have hγ := lineCapSegment_injective he.injective D.time_lt
  have hy' : ∀ j, ‖y j‖ < R := by
    intro j
    have hj := hy j
    have hR := D.radius_pos
    linarith [norm_nonneg (y j)]
  obtain ⟨havoid, hgerms, hinternal⟩ := lineCap_nat_original_germs ha y hγ es f hn hpieces
    D.radius_pos hy' hcircle hv hclose hinj
  have hregularcorner : ∀ k ≤ es.length, coalescedPointExponent a y (f k 0) = 0 →
      deriv (f k) 0 / deriv (f (if k = 0 then es.length else k - 1)) 1 ∈ Complex.slitPlane := by
    intro k hk _
    by_cases hk0 : k = 0
    · simpa [hk0] using hjoin0
    by_cases hkN : k = es.length
    · simpa only [hkN, if_neg (Nat.ne_of_gt hn)] using hjoinN
    · simpa only [if_neg hk0] using hinternal k (by omega) (by omega)
  obtain ⟨τ, ψ, hτ, hψ, hτl, hψl, hzero⟩ := exists_lineCap_nat_tangent_atom_lifts ha y hpq
    (lineCapSegment c D.minus D.plus) (lineCapSegment_zero c D.minus D.plus)
    (lineCapSegment_metric y c hd D.minus D.plus) es f hpieces
    D.radius_pos D.angle_lt hy' hcircle
  have hcover : D.inside ∪ D.outside = (⋃ k ≤ es.length, f k '' Icc (0 : ℝ) 1)ᶜ := by
    rw [hcarrier]
    exact D.cover
  obtain ⟨w, hw, Ξ, hΞ, hΞl, hΞturn⟩ := exists_lineCap_nat_positive_observer_lifts f es.length
    hf hv hclose hinj D.radius_pos D.angle_lt hcircle D.inside_open D.inside_connected
    D.outside_open D.outside_connected D.compact_closure hcover D.inside_ball_and_disjoint.1
  have hvertex (k : ℕ) (hk : k ≤ es.length) : f k 0 ∈ D.boundary := by
    rw [← hcarrier]
    exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, ⟨0, by norm_num, rfl⟩⟩⟩
  have hvertexU (k : ℕ) (hk : k ≤ es.length) : f k 0 ∈ closure D.inside :=
    frontier_subset_closure (D.frontier_inside.symm ▸ hvertex k hk)
  have hvertexV (k : ℕ) (hk : k ≤ es.length) : f k 0 ∈ closure D.outside :=
    frontier_subset_closure (D.frontier_outside.symm ▸ hvertex k hk)
  obtain ⟨θ, hθ, hθturn, hθrad, hGB⟩ := exists_finite_mixed_gauss_bonnet_of_original_germs ha y
    f es.length hn hf hv hclose hreg hinj hregularcorner havoid hgerms
    D.inside_open D.inside_connected D.outside_open D.outside_connected D.disjoint
    D.compact_closure hcover hvertexU hvertexV hw Ξ τ hΞ hτ hΞl hτl hΞturn ψ hψ hψl
  have hQ : pointLineCapCircleTurn a y D =
      (τ es.length 1 - τ es.length 0) +
        ∑ j, (a j / 2) * (ψ j es.length 1 - ψ j es.length 0) := by
    apply pointLineCapCircleTurn_eq_covariant_increment a y D hy (τ es.length) (hτ _ le_rfl)
      (fun t => by simpa only [hcircle] using hτl es.length le_rfl t)
      (fun j => ψ j es.length) (fun j => hψ j es.length le_rfl)
      (fun j hj t ht => by simpa only [hcircle] using hψl j hj es.length le_rfl t ht)
  have hsum : (∑ k ∈ Finset.range (es.length + 1), ((τ k 1 - τ k 0) +
      ∑ j, (a j / 2) * (ψ j k 1 - ψ j k 0))) = pointLineCapCircleTurn a y D := by
    rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun k hk => hzero k (Finset.mem_range.mp hk)),
      zero_add, ← hQ]
  rw [hsum] at hGB
  exact ⟨θ, hθ, hθturn, hθrad, hGB⟩

end RepulsiveCoulomb
