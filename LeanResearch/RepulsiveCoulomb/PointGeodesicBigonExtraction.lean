module

public import LeanResearch.RepulsiveCoulomb.PointConformalGeodesicArc
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-! An unconditional topological reduction of a hypothetical failure of actual
point-metric geodesic uniqueness to a simple geodesic bigon. In particular,
endpoint-only intersection is a conclusion, never a hidden assumption. No
Gauss--Bonnet theorem or global uniqueness statement is asserted here. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- The exact metric parameter identity already implies Euclidean continuity;
the user-facing uniqueness theorem need not add a continuity hypothesis. -/
theorem pointConformal_geodesic_continuous {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {x z : ℂ}
    (γ : Icc (0 : ℝ) 1 → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y x z).toReal) :
    Continuous γ := by
  have hc : @Continuous (Icc (0 : ℝ) 1) ℂ _
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace γ := by
    let K : NNReal := ⟨(pointSmoothConformalEDist a y x z).toReal, ENNReal.toReal_nonneg⟩
    have hdist : ∀ s t : Icc (0 : ℝ) 1,
        @dist ℂ (pointSmoothConformalMetricSpace ha y).toDist (γ s) (γ t) ≤
          (K : ℝ) * dist s t := by
      intro s t
      change (pointSmoothConformalEDist a y (γ s) (γ t)).toReal ≤
        (pointSmoothConformalEDist a y x z).toReal * dist (s.1 : ℝ) t.1
      rw [hd, Real.dist_eq, abs_sub_comm, mul_comm]
    have hl := @LipschitzWith.of_dist_le_mul (Icc (0 : ℝ) 1) ℂ inferInstance
      (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace K γ hdist
    exact @LipschitzWith.continuous (Icc (0 : ℝ) 1) ℂ inferInstance
      (pointSmoothConformalMetricSpace ha y).toPseudoEMetricSpace K γ hl
  rwa [pointSmoothConformalMetricSpace_topology ha y] at hc

/-- Degenerate endpoints force the entire exact metric segment to be constant. -/
theorem pointConformal_geodesic_constant {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x : ℂ)
    (γ : Icc (0 : ℝ) 1 → ℂ) (h0 : γ ⟨0, by norm_num⟩ = x)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y x x).toReal) :
    γ = fun _ => x := by
  funext t
  letI := pointSmoothConformalMetricSpace ha y
  apply dist_eq_zero.mp
  change (pointSmoothConformalEDist a y (γ t) x).toReal = 0
  have h := hd t ⟨0, by norm_num⟩
  simpa only [h0, pointSmoothConformalEDist_self, ENNReal.toReal_zero, mul_zero] using h

/-- Every intersection of two equally parameterized geodesics from the same
start is synchronized. No intersection-finiteness assumption is needed. -/
theorem pointConformal_geodesic_intersection_parameter_eq {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {x z : ℂ} (hxz : x ≠ z)
    (γ₁ γ₂ : Icc (0 : ℝ) 1 → ℂ)
    (h10 : γ₁ ⟨0, by norm_num⟩ = x) (h20 : γ₂ ⟨0, by norm_num⟩ = x)
    (hd₁ : ∀ s t, (pointSmoothConformalEDist a y (γ₁ s) (γ₁ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y x z).toReal)
    (hd₂ : ∀ s t, (pointSmoothConformalEDist a y (γ₂ s) (γ₂ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y x z).toReal)
    {s t : Icc (0 : ℝ) 1} (he : γ₁ s = γ₂ t) : s = t := by
  have hD : 0 < (pointSmoothConformalEDist a y x z).toReal := by
    apply ENNReal.toReal_pos
    · exact (pointSmoothConformalEDist_eq_zero_iff ha y x z).not.mpr hxz
    · exact (pointSmoothConformalEDist_lt_top ha y x z).ne
  have hs := hd₁ ⟨0, by norm_num⟩ s
  have ht := hd₂ ⟨0, by norm_num⟩ t
  rw [h10, sub_zero, abs_of_nonneg s.2.1, he] at hs
  rw [h20, sub_zero, abs_of_nonneg t.2.1] at ht
  apply Subtype.ext
  nlinarith

/-- Any two unequal continuous interval curves agreeing at the endpoints have
an interval of disagreement with agreement at its two distinct endpoints. -/
theorem exists_interval_of_curve_disagreement {X : Type*}
    [TopologicalSpace X] [T2Space X]
    (γ₁ γ₂ : Icc (0 : ℝ) 1 → X) (hc₁ : Continuous γ₁) (hc₂ : Continuous γ₂)
    (h0 : γ₁ ⟨0, by norm_num⟩ = γ₂ ⟨0, by norm_num⟩)
    (h1 : γ₁ ⟨1, by norm_num⟩ = γ₂ ⟨1, by norm_num⟩) (hne : γ₁ ≠ γ₂) :
    ∃ s t : Icc (0 : ℝ) 1, s < t ∧ γ₁ s = γ₂ s ∧ γ₁ t = γ₂ t ∧
      ∀ u ∈ Ioo s t, γ₁ u ≠ γ₂ u := by
  classical
  obtain ⟨q, hq⟩ : ∃ q, γ₁ q ≠ γ₂ q :=
    not_forall.mp (fun h => hne (funext h))
  let C : Set (Icc (0 : ℝ) 1) := {u | γ₁ u = γ₂ u}
  have hC : IsClosed C := isClosed_eq hc₁ hc₂
  have hleft : (C ∩ Iic q).Nonempty := by
    refine ⟨⟨0, by norm_num⟩, h0, ?_⟩
    exact q.2.1
  have hright : (C ∩ Ici q).Nonempty := by
    refine ⟨⟨1, by norm_num⟩, h1, ?_⟩
    exact q.2.2
  obtain ⟨s, hs⟩ := (hC.inter isClosed_Iic).isCompact.exists_isGreatest hleft
  obtain ⟨t, ht⟩ := (hC.inter isClosed_Ici).isCompact.exists_isLeast hright
  have hsq : s < q := by
    apply lt_of_le_of_ne hs.1.2
    intro he
    apply hq
    simpa only [C, mem_setOf_eq, he] using hs.1.1
  have hqt : q < t := by
    apply lt_of_le_of_ne ht.1.2
    intro he
    apply hq
    simpa only [C, mem_setOf_eq, ← he] using ht.1.1
  refine ⟨s, t, hsq.trans hqt, hs.1.1, ht.1.1, ?_⟩
  intro u hu he
  by_cases huq : u ≤ q
  · exact (not_le_of_gt hu.1) (hs.2 ⟨he, huq⟩)
  · exact (not_le_of_gt hu.2) (ht.2 ⟨he, (lt_of_not_ge huq).le⟩)

/-- A hypothetical distinct pair of actual minimizing geodesics always contains
two simple subarcs whose images meet at precisely their two common endpoints. -/
theorem exists_pointConformal_geodesic_simple_bigon_interval {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {x z : ℂ} (hxz : x ≠ z)
    (γ₁ γ₂ : Icc (0 : ℝ) 1 → ℂ)
    (h10 : γ₁ ⟨0, by norm_num⟩ = x) (h11 : γ₁ ⟨1, by norm_num⟩ = z)
    (h20 : γ₂ ⟨0, by norm_num⟩ = x) (h21 : γ₂ ⟨1, by norm_num⟩ = z)
    (hd₁ : ∀ s t, (pointSmoothConformalEDist a y (γ₁ s) (γ₁ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y x z).toReal)
    (hd₂ : ∀ s t, (pointSmoothConformalEDist a y (γ₂ s) (γ₂ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y x z).toReal)
    (hne : γ₁ ≠ γ₂) :
    ∃ s t : Icc (0 : ℝ) 1, s < t ∧ γ₁ s = γ₂ s ∧ γ₁ t = γ₂ t ∧
      γ₁ s ≠ γ₁ t ∧
      (∀ u ∈ Ioo s t, γ₁ u ≠ γ₂ u) ∧
      γ₁ '' Icc s t ∩ γ₂ '' Icc s t = {γ₁ s, γ₁ t} := by
  obtain ⟨s, t, hst, hs, ht, hgap⟩ := exists_interval_of_curve_disagreement γ₁ γ₂
    (pointConformal_geodesic_continuous ha y γ₁ hd₁)
    (pointConformal_geodesic_continuous ha y γ₂ hd₂)
    (h10.trans h20.symm) (h11.trans h21.symm) hne
  have hinj := pointConformal_geodesic_injective ha y hxz γ₁ hd₁
  refine ⟨s, t, hst, hs, ht, (fun h => hst.ne (hinj h)), hgap, ?_⟩
  ext p
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, ⟨v, hv, he⟩⟩
    have huv := pointConformal_geodesic_intersection_parameter_eq ha y hxz
      γ₁ γ₂ h10 h20 hd₁ hd₂ he.symm
    subst v
    by_cases hus : u = s
    · simp only [hus, mem_insert_iff, mem_singleton_iff, true_or]
    by_cases hut : u = t
    · simp only [hut, mem_insert_iff, mem_singleton_iff, or_true]
    have hui : u ∈ Ioo s t :=
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hus), lt_of_le_of_ne hu.2 hut⟩
    exact False.elim (hgap u hui he.symm)
  · intro hp
    rcases mem_insert_iff.mp hp with hp | hp
    · subst p
      exact ⟨⟨s, ⟨le_rfl, hst.le⟩, rfl⟩, ⟨s, ⟨le_rfl, hst.le⟩, hs.symm⟩⟩
    · have hp' : p = γ₁ t := mem_singleton_iff.mp hp
      subst p
      exact ⟨⟨t, ⟨hst.le, le_rfl⟩, rfl⟩, ⟨t, ⟨hst.le, le_rfl⟩, ht.symm⟩⟩

end RepulsiveCoulomb
