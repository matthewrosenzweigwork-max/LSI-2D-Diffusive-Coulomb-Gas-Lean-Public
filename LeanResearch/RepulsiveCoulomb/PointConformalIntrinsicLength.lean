module

public import LeanResearch.RepulsiveCoulomb.PointConformalPathTransport
public import Mathlib.Topology.EMetricSpace.BoundedVariation

@[expose] public section

/-! Intrinsic metric length for the constructed conformal distance. This uses
Mathlib's partition variation, not an assumed all-rectifiable physical integral
identity. No external length-space package is imported. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

def pointConformalMetricLength {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (γ : ℝ → ℂ) (s t : ℝ) : ℝ≥0∞ :=
  @eVariationOn ℝ _ ℂ (pointSmoothConformalEMetricSpace ha y).toUniformSpace.toTopologicalSpace
    (@PseudoEMetricSpace.toWeakPseudoEMetricSpace ℂ
      (pointSmoothConformalEMetricSpace ha y).toPseudoEMetricSpace) γ (Icc s t)

theorem pointConformalPathELength_add {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (γ : ℝ → ℂ) {s t u : ℝ} (hst : s ≤ t) (htu : t ≤ u) :
    pointConformalPathELength a y γ s t + pointConformalPathELength a y γ t u =
      pointConformalPathELength a y γ s u := by
  let := pointConformalTangentENorm a y
  simp only [pointConformalPathELength_eq_manifold]
  exact Manifold.pathELength_add hst htu

theorem pointConformalMetricLength_endpoint_le {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (γ : ℝ → ℂ) {s t : ℝ} (hst : s ≤ t) :
    pointSmoothConformalEDist a y (γ s) (γ t) ≤ pointConformalMetricLength ha y γ s t := by
  exact @eVariationOn.edist_le ℝ _ ℂ (pointSmoothConformalEMetricSpace ha y).toUniformSpace.toTopologicalSpace
    (@PseudoEMetricSpace.toWeakPseudoEMetricSpace ℂ
      (pointSmoothConformalEMetricSpace ha y).toPseudoEMetricSpace) γ (Icc s t) s t
      ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩

theorem pointConformalMetricLength_le_physical {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {γ : ℝ → ℂ} {s t : ℝ}
    (hγ : ContDiffOn ℝ 1 γ (Icc s t)) :
    pointConformalMetricLength ha y γ s t ≤ pointConformalPathELength a y γ s t := by
  unfold pointConformalMetricLength eVariationOn
  apply iSup_le
  rintro ⟨n, u, hu, hmem⟩
  have hsum : ∀ k : ℕ,
      (∑ i ∈ Finset.range k, pointSmoothConformalEDist a y (γ (u (i + 1))) (γ (u i))) ≤
        pointConformalPathELength a y γ (u 0) (u k) := by
    intro k
    induction k with
    | zero => simp [pointConformalPathELength]
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hsub : Icc (u k) (u (k + 1)) ⊆ Icc s t :=
        Icc_subset_Icc (hmem k).1 (hmem (k + 1)).2
      have hd := pointSmoothConformalEDist_le_path a y (hγ.mono hsub) (hu (Nat.le_succ k))
      rw [pointSmoothConformalEDist_comm] at hd
      exact (add_le_add ih hd).trans_eq
        (pointConformalPathELength_add a y γ (hu (Nat.zero_le k)) (hu (Nat.le_succ k)))
  exact (hsum n).trans (pointConformalPathELength_mono a y γ (hmem 0).1 (hmem n).2)

/-- The constructed metric is intrinsic for continuous curves and metric variation.
This does not yet identify metric variation with the physical weighted integral
for arbitrary Euclidean-rectifiable curves. -/
theorem pointSmoothConformalEDist_eq_inf_metricLength {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x z : ℂ) :
    pointSmoothConformalEDist a y x z =
      ⨅ γ : {γ : ℝ → ℂ // γ 0 = x ∧ γ 1 = z ∧ ContinuousOn γ (Icc (0 : ℝ) 1)},
        pointConformalMetricLength ha y γ.1 0 1 := by
  apply le_antisymm
  · apply le_iInf
    intro γ
    simpa only [γ.2.1, γ.2.2.1] using
      pointConformalMetricLength_endpoint_le ha y γ.1 (by norm_num : (0 : ℝ) ≤ 1)
  · apply le_of_forall_gt
    intro r hr
    obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_smooth_path_lt_pointConformalEDist a y hr
    exact (iInf_le _ ⟨γ, h0, h1, hγ.continuous.continuousOn⟩).trans_lt
      ((pointConformalMetricLength_le_physical ha y hγ.contDiffOn).trans_lt hlen)

end RepulsiveCoulomb
