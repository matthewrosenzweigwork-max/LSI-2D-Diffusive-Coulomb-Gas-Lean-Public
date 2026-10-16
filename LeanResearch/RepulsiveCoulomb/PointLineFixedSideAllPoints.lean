module

public import LeanResearch.RepulsiveCoulomb.PointLineCapLocalSide
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Records-only, uncompiled. Recenter the ORIGINAL metric line at each actual
source point before constructing its full cone chart. The fixed global sides
are retained; the local existential labeling may swap. Actual cap side germs
are proved equal inside that SAME metric chart, including all on-line atoms. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem pointMetricLine_recenter_metric
    {m : ℕ} {a : Fin m → ℝ} (y : Fin m → ℂ) (c : ℝ → ℂ)
    (hd : ∀ u v, (pointSmoothConformalEDist a y (c u) (c v)).toReal = dist u v) (s : ℝ) :
    ∀ u v, (pointSmoothConformalEDist a y (c (s + u)) (c (s + v))).toReal = dist u v := by
  intro u v
  simpa only [Real.dist_eq, add_sub_add_left_eq_sub] using hd (s + u) (s + v)

theorem pointMetricLine_recenter_range (c : ℝ → ℂ) (s : ℝ) :
    range (fun t => c (s + t)) = range c := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact mem_range_self (s + t)
  · rintro ⟨t, rfl⟩
    exact ⟨t - s, by congr 1; ring⟩

/-- The full metric chart is constructed at every source point. The same
fixed global pair is used, and both possible local side labels are explicit. -/
theorem exists_pointMetricLine_fixed_side_chart_at
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c : ℝ → ℂ)
    (hd : ∀ u v, (pointSmoothConformalEDist a y (c u) (c v)).toReal = dist u v)
    {A B : Set ℂ} (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hcover : A ∪ B = (range c)ᶜ) (hfA : frontier A = range c) (hfB : frontier B = range c)
    (s : ℝ) :
    ∃ F : OpenPartialHomeomorph ℂ ℂ, ∃ ρ θ : ℝ,
      0 < ρ ∧ 0 < θ ∧ θ < 2 * Real.pi ∧ c s ∈ F.source ∧ F (c s) = 0 ∧
      ball (0 : ℂ) ρ ⊆ F.target ∧
      (∀ u, (pointSmoothConformalEDist a y u (c s)).toReal ≤ ρ →
        ∀ v, (pointSmoothConformalEDist a y v (c s)).toReal ≤ ρ →
          (pointSmoothConformalEDist a y u v).toReal =
            pointClassicalConeDist a y (c s) (F u) (F v)) ∧
      (∀ z ∈ ball (0 : ℂ) ρ,
        F.symm z ∈ range c ↔ z ∈ pointDiskRay ρ 0 ∪ pointDiskRay ρ θ) ∧
      Real.pi ≤ (1 + coalescedPointExponent a y (c s) / 2) * θ ∧
      Real.pi ≤ (1 + coalescedPointExponent a y (c s) / 2) * (2 * Real.pi - θ) ∧
      ((∀ z ∈ ball (0 : ℂ) ρ,
          (F.symm z ∈ closure A ↔ z ∈ (pointDiskRay ρ 0 ∪ pointDiskRay ρ θ) ∪
            pointOpenRadialSector ρ 0 θ) ∧
          (F.symm z ∈ closure B ↔ z ∈ (pointDiskRay ρ 0 ∪ pointDiskRay ρ θ) ∪
            pointOpenRadialSector ρ θ (2 * Real.pi))) ∨
       (∀ z ∈ ball (0 : ℂ) ρ,
          (F.symm z ∈ closure A ↔ z ∈ (pointDiskRay ρ 0 ∪ pointDiskRay ρ θ) ∪
            pointOpenRadialSector ρ θ (2 * Real.pi)) ∧
          (F.symm z ∈ closure B ↔ z ∈ (pointDiskRay ρ 0 ∪ pointDiskRay ρ θ) ∪
            pointOpenRadialSector ρ 0 θ))) := by
  let ℓ : ℝ → ℂ := fun t => c (s + t)
  have hℓ0 : ℓ 0 = c s := by simp [ℓ]
  have hℓrange : range ℓ = range c := pointMetricLine_recenter_range c s
  obtain ⟨F, ρ, θ, hρ, hθ, hθ2, hsF, hF0, _, _, hmetric, htarget, hboundary, hleft, hright⟩ :=
    exists_pointMetricLine_normalized_chart ha y ℓ (pointMetricLine_recenter_metric y c hd s)
  rw [hℓ0] at hsF hF0 hmetric hleft hright
  rw [hℓrange] at hboundary
  refine ⟨F, ρ, θ, hρ, hθ, hθ2, hsF, hF0, htarget, hmetric, hboundary,
    by simpa only [add_comm] using hleft, by simpa only [add_comm] using hright, ?_⟩
  have hpA : c s ∈ closure A := frontier_subset_closure (hfA.symm ▸ mem_range_self s)
  have hpB : c s ∈ closure B := frontier_subset_closure (hfB.symm ▸ mem_range_self s)
  have hpart := pointDiskRay_complement_eq_sectors hρ hθ hθ2
  have hpart' : ball (0 : ℂ) ρ \ (pointDiskRay ρ 0 ∪ pointDiskRay ρ θ) =
      pointOpenRadialSector ρ θ (2 * Real.pi) ∪ pointOpenRadialSector ρ 0 θ := by
    simpa only [union_comm] using hpart
  rcases pointRadialChart_region_side_choice hA hB hAB hcover hpA hpB F hsF hF0
    hρ hθ hθ2 htarget hboundary with ⟨hSA, hTB⟩ | ⟨hSB, hTA⟩
  · left
    intro z hz
    exact ⟨chart_closed_side_membership hAB hcover hfA F hboundary hpart hSA hTB z hz,
      chart_closed_side_membership hAB.symm (by simpa only [union_comm] using hcover)
        hfB F hboundary hpart' hTB hSA z hz⟩
  · right
    intro z hz
    exact ⟨chart_closed_side_membership hAB hcover hfA F hboundary hpart' hTA hSB z hz,
      chart_closed_side_membership hAB.symm (by simpa only [union_comm] using hcover)
        hfB F hboundary hpart hSB hTA z hz⟩

/-- The chart is selected ONCE for a fixed line point. Every cap enclosing
that point has precisely the same full retained closed side locally. Thus
there is no fresh side selection at a boundary atom as the radius changes. -/
theorem exists_pointMetricLine_cap_stable_chart_at
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c : ℝ → ℂ)
    (hd : ∀ u v, (pointSmoothConformalEDist a y (c u) (c v)).toReal = dist u v)
    {A B : Set ℂ} (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hcover : A ∪ B = (range c)ᶜ) (hfA : frontier A = range c) (hfB : frontier B = range c)
    (s : ℝ) :
    ∃ F : OpenPartialHomeomorph ℂ ℂ, ∃ ρ θ : ℝ,
      0 < ρ ∧ 0 < θ ∧ θ < 2 * Real.pi ∧ c s ∈ F.source ∧ F (c s) = 0 ∧
      (∀ u, (pointSmoothConformalEDist a y u (c s)).toReal ≤ ρ →
        ∀ v, (pointSmoothConformalEDist a y v (c s)).toReal ≤ ρ →
          (pointSmoothConformalEDist a y u v).toReal =
            pointClassicalConeDist a y (c s) (F u) (F v)) ∧
      Real.pi ≤ (1 + coalescedPointExponent a y (c s) / 2) * θ ∧
      Real.pi ≤ (1 + coalescedPointExponent a y (c s) / 2) * (2 * Real.pi - θ) ∧
      ∀ {R : ℝ} (D : LineCapGeometry c R), D.inside ⊆ A → ‖c s‖ < R →
        ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧
          ∀ z ∈ ball (0 : ℂ) r,
            F.symm z ∈ closure D.inside ↔ F.symm z ∈ closure A := by
  obtain ⟨F, ρ, θ, hρ, hθ, hθ2, hsF, hF0, htarget, hmetric, hboundary, hleft, hright, _⟩ :=
    exists_pointMetricLine_fixed_side_chart_at ha y c hd hA hB hAB hcover hfA hfB s
  refine ⟨F, ρ, θ, hρ, hθ, hθ2, hsF, hF0, hmetric, hleft, hright, ?_⟩
  intro R D hDA hs
  exact D.local_fixed_side hA hB hAB hcover hfA hfB hDA hs F hsF hF0
    hρ hθ hθ2 htarget hboundary

end RepulsiveCoulomb
