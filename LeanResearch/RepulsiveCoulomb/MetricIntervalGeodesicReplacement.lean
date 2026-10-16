import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Linarith

/-! Literal finite gluing of Lipschitz interval curves and replacement of one
geodesic subsegment. Zero-length outer pieces are allowed. A sharp endpoint
distance forces the constructed whole curve to be a constant-speed geodesic;
no uniqueness of either original or replacement geodesic is assumed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def metricIntervalGlue {X : Type*} (s : unitInterval) (f g : unitInterval → X) :
    unitInterval → X := fun u ↦ if u ≤ s then f u else g u

theorem metricIntervalGlue_le {X : Type*} (s : unitInterval) (f g : unitInterval → X)
    (u : unitInterval) (hu : u ≤ s) : metricIntervalGlue s f g u = f u := if_pos hu

theorem metricIntervalGlue_ge {X : Type*} (s : unitInterval) (f g : unitInterval → X)
    (hjoin : f s = g s) (u : unitInterval) (hu : s ≤ u) :
    metricIntervalGlue s f g u = g u := by
  by_cases hus : u ≤ s
  · have he : u = s := le_antisymm hus hu
    subst u
    rw [metricIntervalGlue_le _ _ _ _ le_rfl, hjoin]
  · exact if_neg hus

/-- One literal gluing preserves the sharp ordered Lipschitz bound. -/
theorem metricIntervalGlue_dist_le {X : Type*} [PseudoMetricSpace X]
    (c : ℝ) (s : unitInterval) (f g : unitInterval → X)
    (hf : ∀ u v, u ≤ v → dist (f u) (f v) ≤ c * (v.1 - u.1))
    (hg : ∀ u v, u ≤ v → dist (g u) (g v) ≤ c * (v.1 - u.1))
    (hjoin : f s = g s) :
    ∀ u v, u ≤ v → dist (metricIntervalGlue s f g u) (metricIntervalGlue s f g v) ≤
      c * (v.1 - u.1) := by
  intro u v huv
  by_cases hvs : v ≤ s
  · rw [metricIntervalGlue_le _ _ _ _ (huv.trans hvs), metricIntervalGlue_le _ _ _ _ hvs]
    exact hf u v huv
  · have hsv : s ≤ v := (lt_of_not_ge hvs).le
    by_cases hus : u ≤ s
    · rw [metricIntervalGlue_le _ _ _ _ hus, metricIntervalGlue_ge _ _ _ hjoin _ hsv]
      have h₁ := hf u s hus
      have h₂ := hg s v hsv
      have htri := dist_triangle (f u) (f s) (g v)
      rw [hjoin] at htri h₁
      linarith
    · rw [metricIntervalGlue_ge _ _ _ hjoin _ (lt_of_not_ge hus).le,
        metricIntervalGlue_ge _ _ _ hjoin _ hsv]
      exact hg u v huv

/-- A Lipschitz curve attaining its full endpoint bound is minimizing between
every two parameters. -/
theorem metricInterval_distance_of_endpoint_eq {X : Type*} [PseudoMetricSpace X]
    (c : ℝ) (γ : unitInterval → X)
    (hγ : ∀ u v, u ≤ v → dist (γ u) (γ v) ≤ c * (v.1 - u.1))
    (hfull : dist (γ 0) (γ 1) = c) :
    ∀ u v, dist (γ u) (γ v) = c * |v.1 - u.1| := by
  have hordered : ∀ u v : unitInterval, u ≤ v → dist (γ u) (γ v) = c * (v.1 - u.1) := by
    intro u v huv
    apply le_antisymm (hγ u v huv)
    have hleft := hγ 0 u bot_le
    have hright := hγ v 1 le_top
    have htri₁ := dist_triangle (γ 0) (γ u) (γ 1)
    have htri₂ := dist_triangle (γ u) (γ v) (γ 1)
    rw [hfull] at htri₁
    change dist (γ 0) (γ u) ≤ c * (u.1 - 0) at hleft
    change dist (γ v) (γ 1) ≤ c * (1 - v.1) at hright
    linarith
  intro u v
  rcases le_total u v with huv | hvu
  · rw [hordered u v huv, abs_of_nonneg (sub_nonneg.mpr (show u.1 ≤ v.1 from huv))]
  · rw [dist_comm, hordered v u hvu,
      abs_of_nonpos (sub_nonpos.mpr (show v.1 ≤ u.1 from hvu)), neg_sub]

/-- Construct the replacement curve, retaining both outer pieces literally.
The replacement is needed only on [s,t], but its global Lipschitz extension
makes finite gluing especially simple and is supplied explicitly. -/
theorem exists_metricInterval_geodesic_replacement {X : Type*} [PseudoMetricSpace X]
    (c : ℝ) (γ δ : unitInterval → X)
    (hγ : ∀ u v, dist (γ u) (γ v) = c * |v.1 - u.1|)
    (hδ : ∀ u v, u ≤ v → dist (δ u) (δ v) ≤ c * (v.1 - u.1))
    (s t : unitInterval) (hst : s < t) (hs : γ s = δ s) (ht : δ t = γ t) :
    ∃ η : unitInterval → X,
      η 0 = γ 0 ∧ η 1 = γ 1 ∧
      (∀ u, u ≤ s → η u = γ u) ∧
      (∀ u, t ≤ u → η u = γ u) ∧
      (∀ u, s ≤ u → u ≤ t → η u = δ u) ∧
      ∀ u v, dist (η u) (η v) = c * |v.1 - u.1| := by
  have hγle : ∀ u v : unitInterval, u ≤ v → dist (γ u) (γ v) ≤ c * (v.1 - u.1) := by
    intro u v huv
    rw [hγ, abs_of_nonneg (sub_nonneg.mpr (show u.1 ≤ v.1 from huv))]
  let ζ := metricIntervalGlue s γ δ
  let η := metricIntervalGlue t ζ γ
  have hζle := metricIntervalGlue_dist_le c s γ δ hγle hδ hs
  have hζt : ζ t = γ t := (metricIntervalGlue_ge s γ δ hs t hst.le).trans ht
  have hηle := metricIntervalGlue_dist_le c t ζ γ hζle hγle hζt
  have hleft : ∀ u, u ≤ s → η u = γ u := by
    intro u hu
    exact (metricIntervalGlue_le t ζ γ u (hu.trans hst.le)).trans
      (metricIntervalGlue_le s γ δ u hu)
  have hright : ∀ u, t ≤ u → η u = γ u :=
    fun u hu ↦ metricIntervalGlue_ge t ζ γ hζt u hu
  have hmiddle : ∀ u, s ≤ u → u ≤ t → η u = δ u := by
    intro u hsu hut
    exact (metricIntervalGlue_le t ζ γ u hut).trans
      (metricIntervalGlue_ge s γ δ hs u hsu)
  have hη0 : η 0 = γ 0 := hleft 0 bot_le
  have hη1 : η 1 = γ 1 := hright 1 le_top
  have hfull : dist (η 0) (η 1) = c := by
    rw [hη0, hη1, hγ]
    norm_num
  exact ⟨η, hη0, hη1, hleft, hright, hmiddle,
    metricInterval_distance_of_endpoint_eq c η hηle hfull⟩

end RepulsiveCoulomb
