module

public import LeanResearch.RepulsiveCoulomb.ConePowerGeodesic
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.EMetricSpace.BoundedVariation

@[expose] public section

/-! Euclidean rectifiability of an analytic image of a power-parametrized radial
segment. The exponent may be arbitrarily small and positive. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem unitInterval_rpow_variation {p : ℝ} (hp : 0 < p) :
    eVariationOn (fun t : ℝ => t ^ p) (Icc (0 : ℝ) 1) = 1 := by
  have hm : MonotoneOn (fun t : ℝ => t ^ p) (Icc (0 : ℝ) 1) :=
    fun _ hx _ _ hxy => Real.rpow_le_rpow hx.1 hxy hp.le
  simpa only [inter_self, Real.one_rpow, Real.zero_rpow hp.ne', sub_zero, ENNReal.ofReal_one] using
    hm.eVariationOn_eq (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)

theorem analytic_radial_power_rectifiable {p : ℝ} (hp : 0 < p) (F : ℂ → ℂ) (w : ℂ)
    (hF : ∀ s ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ F (s • w)) :
    BoundedVariationOn (fun t : ℝ => F (t ^ p • w)) (Icc (0 : ℝ) 1) := by
  have hA : AnalyticOnNhd ℝ (fun s : ℝ => F (s • w)) (Icc (0 : ℝ) 1) := by
    intro s hs
    have h : AnalyticAt ℝ F (s • w) := (hF s hs).restrictScalars
    have hl : AnalyticAt ℝ (fun r : ℝ => r • w) s :=
      analyticAt_id.smul analyticAt_const
    exact h.comp (f := fun r : ℝ => r • w) hl
  obtain ⟨C, hC⟩ := (hA.contDiffOn_of_completeSpace (n := 1)).exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc
  have hm : MapsTo (fun t : ℝ => t ^ p) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact ⟨Real.rpow_nonneg ht.1 p, Real.rpow_le_one ht.1 ht.2 hp.le⟩
  have hb : BoundedVariationOn (fun t : ℝ => t ^ p) (Icc (0 : ℝ) 1) := by
    change eVariationOn _ _ ≠ ⊤
    rw [unitInterval_rpow_variation hp]
    exact ENNReal.one_ne_top
  exact hC.comp_boundedVariationOn hm hb

end RepulsiveCoulomb
