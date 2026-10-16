import LeanResearch.RepulsiveCoulomb.PointConformalGeodesic
import Mathlib.Topology.Compactness.Compact

/-! A compactness construction of metric rays from arbitrarily long segments.
The compact product supplies a single compatible ray; no unproved subsequence or
Arzela--Ascoli hypothesis is used. -/
noncomputable section
open Set Metric
open scoped NNReal
namespace RepulsiveCoulomb
variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem exists_metric_ray_of_finite_segments (x : X)
    (hseg : ∀ R : ℝ≥0, ∃ f : ℝ≥0 → X,
      (∀ t, dist (f t) x ≤ t) ∧
      ∀ s ≤ R, ∀ t ≤ R, dist (f s) (f t) = dist s t) :
    ∃ f : ℝ≥0 → X, Isometry f ∧ f 0 = x := by
  let K : Set (ℝ≥0 → X) := Set.pi Set.univ (fun t ↦ closedBall x (t : ℝ))
  have hK : IsCompact K := isCompact_univ_pi (fun t ↦ isCompact_closedBall x (t : ℝ))
  let C : (ℝ≥0 × ℝ≥0) → Set (ℝ≥0 → X) :=
    fun i ↦ {f | dist (f i.1) (f i.2) = dist i.1 i.2}
  have hC : ∀ i, IsClosed (C i) := fun i ↦
    isClosed_eq ((continuous_apply i.1).dist (continuous_apply i.2)) continuous_const
  have hfin : ∀ u : Finset (ℝ≥0 × ℝ≥0), (K ∩ ⋂ i ∈ u, C i).Nonempty := by
    intro u
    let R : ℝ≥0 := u.sup (fun i ↦ max i.1 i.2)
    obtain ⟨f, hf, hd⟩ := hseg R
    refine ⟨f, ?_, ?_⟩
    · exact fun t _ ↦ hf t
    · simp only [mem_iInter]
      intro i hi
      have hb : max i.1 i.2 ≤ R := Finset.le_sup (f := fun i : ℝ≥0 × ℝ≥0 ↦ max i.1 i.2) hi
      exact hd i.1 ((le_max_left _ _).trans hb) i.2 ((le_max_right _ _).trans hb)
  obtain ⟨f, hfK, hfC⟩ := hK.inter_iInter_nonempty C hC hfin
  refine ⟨f, ?_, ?_⟩
  · apply isometry_iff_dist_eq.mpr
    intro s t
    exact (mem_iInter.mp hfC) (s, t)
  · exact dist_le_zero.mp (hfK 0 (mem_univ _))

omit [ProperSpace X] in
/-- Truncate a sufficiently long normalized geodesic to obtain a competitor in
all compact product balls, exact up to the requested radius. -/
theorem exists_truncated_metric_segment (x : X)
    (hfar : ∀ R : ℝ, ∃ z : X, R < dist x z)
    (hgeo : ∀ z : X, ∃ γ : Icc (0 : ℝ) 1 → X,
      γ ⟨0, by norm_num⟩ = x ∧
      ∀ s t, dist (γ s) (γ t) = |t.1 - s.1| * dist x z)
    (R : ℝ≥0) :
    ∃ f : ℝ≥0 → X, (∀ t, dist (f t) x ≤ t) ∧
      ∀ s ≤ R, ∀ t ≤ R, dist (f s) (f t) = dist s t := by
  obtain ⟨z, hz⟩ := hfar R
  have hD : 0 < dist x z := lt_of_le_of_lt R.coe_nonneg hz
  obtain ⟨γ, h0, hd⟩ := hgeo z
  let τ : ℝ≥0 → Icc (0 : ℝ) 1 := fun t ↦
    ⟨min ((t : ℝ) / dist x z) 1, le_min (div_nonneg t.coe_nonneg hD.le) zero_le_one, min_le_right _ _⟩
  let f : ℝ≥0 → X := γ ∘ τ
  have htau (t : ℝ≥0) (ht : t ≤ R) : (τ t).1 = (t : ℝ) / dist x z := by
    apply min_eq_left
    apply (div_le_one hD).mpr
    exact (show (t : ℝ) ≤ R from ht).trans hz.le
  refine ⟨f, ?_, ?_⟩
  · intro t
    change dist (γ (τ t)) x ≤ (t : ℝ)
    rw [← h0, hd]
    change |0 - (τ t).1| * dist x z ≤ t
    rw [zero_sub, abs_neg, abs_of_nonneg (τ t).2.1]
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hD.le).trans_eq (div_mul_cancel₀ _ hD.ne')
  · intro s hs t ht
    change dist (γ (τ s)) (γ (τ t)) = dist s t
    rw [hd, htau s hs, htau t ht, ← sub_div, abs_div, abs_of_pos hD, div_mul_cancel₀ _ hD.ne']
    exact abs_sub_comm _ _

theorem exists_metric_ray_of_unbounded_geodesics (x : X)
    (hfar : ∀ R : ℝ, ∃ z : X, R < dist x z)
    (hgeo : ∀ z : X, ∃ γ : Icc (0 : ℝ) 1 → X,
      γ ⟨0, by norm_num⟩ = x ∧
      ∀ s t, dist (γ s) (γ t) = |t.1 - s.1| * dist x z) :
    ∃ f : ℝ≥0 → X, Isometry f ∧ f 0 = x :=
  exists_metric_ray_of_finite_segments x (exists_truncated_metric_segment x hfar hgeo)

end RepulsiveCoulomb
