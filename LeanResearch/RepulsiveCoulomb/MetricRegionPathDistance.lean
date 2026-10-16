import LeanResearch.RepulsiveCoulomb.MetricRegionLengthPath
import Mathlib.Topology.Connected.Clopen

/-! The genuine constrained path-length infimum, before any ambient-convexity
conclusion. Local radial competitors imply finite reachability by connectedness. -/
noncomputable section
open Set Metric Topology
open scoped ENNReal
namespace RepulsiveCoulomb
variable {X : Type*} [MetricSpace X]

def metricRegionPathEDist (P : Set X) (x z : X) : ℝ≥0∞ :=
  ⨅ γ : MetricRegionLengthPath P x z, γ.length

theorem metricRegionPathEDist_le_length {P : Set X} {x z : X}
    (γ : MetricRegionLengthPath P x z) : metricRegionPathEDist P x z ≤ γ.length :=
  iInf_le _ γ

theorem edist_le_metricRegionPathEDist (P : Set X) (x z : X) :
    edist x z ≤ metricRegionPathEDist P x z :=
  le_iInf fun γ ↦ γ.endpoint_le_length

theorem metricRegionPathEDist_self {P : Set X} {x : X} (hx : x ∈ P) :
    metricRegionPathEDist P x x = 0 := by
  apply le_antisymm _ bot_le
  exact (metricRegionPathEDist_le_length (MetricRegionLengthPath.const hx)).trans_eq
    (MetricRegionLengthPath.length_const hx)

theorem metricRegionPathEDist_comm (P : Set X) (x z : X) :
    metricRegionPathEDist P x z = metricRegionPathEDist P z x := by
  have h (x z : X) : metricRegionPathEDist P x z ≤ metricRegionPathEDist P z x := by
    apply le_iInf
    intro γ
    exact (metricRegionPathEDist_le_length γ.reverse).trans_eq γ.length_reverse
  exact le_antisymm (h x z) (h z x)

theorem metricRegionPathEDist_triangle (P : Set X) (x y z : X) :
    metricRegionPathEDist P x z ≤ metricRegionPathEDist P x y + metricRegionPathEDist P y z := by
  apply ENNReal.le_iInf_add_iInf
  intro γ η
  exact (metricRegionPathEDist_le_length (γ.trans η)).trans (γ.length_trans_le η)

/-- The local geometric input says only that actual radial competitors from
the chart center stay in the actual retained subset. It asserts no pairwise
convexity or already-constructed intrinsic metric. -/
def MetricRegionRadialPaths (P : Set X) : Prop :=
  ∀ x ∈ P, ∃ r : ℝ, 0 < r ∧ ∀ z ∈ P, dist z x < r →
    ∃ γ : MetricRegionLengthPath P x z, γ.length = edist x z

theorem metricRegionPathEDist_center_eq {P : Set X} (hP : MetricRegionRadialPaths P)
    {x : X} (hx : x ∈ P) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ P, dist z x < r → metricRegionPathEDist P x z = edist x z := by
  obtain ⟨r, hr, hpaths⟩ := hP x hx
  refine ⟨r, hr, fun z hz hd ↦ ?_⟩
  obtain ⟨γ, hγ⟩ := hpaths z hz hd
  exact le_antisymm ((metricRegionPathEDist_le_length γ).trans_eq hγ)
    (edist_le_metricRegionPathEDist P x z)

theorem metricRegionPathEDist_lt_top_of_connected {P : Set X}
    (hconn : IsPreconnected P) (hlocal : MetricRegionRadialPaths P)
    {x z : X} (hx : x ∈ P) (hz : z ∈ P) : metricRegionPathEDist P x z < ⊤ := by
  letI : PreconnectedSpace P := isPreconnected_iff_preconnectedSpace.mp hconn
  let R : Set P := {u | metricRegionPathEDist P x u.1 < ⊤}
  have hRo : IsOpen R := by
    apply Metric.isOpen_iff.mpr
    intro u hu
    obtain ⟨r, hr, hpaths⟩ := hlocal u.1 u.2
    refine ⟨r, hr, ?_⟩
    intro v hv
    obtain ⟨γ, hγ⟩ := hpaths v.1 v.2 hv
    have hfin : metricRegionPathEDist P u.1 v.1 < ⊤ :=
      (metricRegionPathEDist_le_length γ).trans_lt (by rw [hγ]; exact edist_lt_top _ _)
    exact (metricRegionPathEDist_triangle P x u.1 v.1).trans_lt (ENNReal.add_lt_top.mpr ⟨hu, hfin⟩)
  have hRco : IsOpen Rᶜ := by
    apply Metric.isOpen_iff.mpr
    intro u hu
    obtain ⟨r, hr, hpaths⟩ := hlocal u.1 u.2
    refine ⟨r, hr, ?_⟩
    intro v hv hvR
    obtain ⟨γ, hγ⟩ := hpaths v.1 v.2 hv
    have hfin : metricRegionPathEDist P v.1 u.1 < ⊤ := by
      rw [metricRegionPathEDist_comm P v.1 u.1]
      exact (metricRegionPathEDist_le_length γ).trans_lt (by rw [hγ]; exact edist_lt_top _ _)
    exact hu ((metricRegionPathEDist_triangle P x v.1 u.1).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hvR, hfin⟩))
  have hRclosed : IsClosed R := by
    simpa only [compl_compl] using hRco.isClosed_compl
  have hReq : R = univ := (show IsClopen R from ⟨hRclosed, hRo⟩).eq_univ
    ⟨⟨x, hx⟩, by change metricRegionPathEDist P x x < ⊤; rw [metricRegionPathEDist_self hx]; simp⟩
  have hzR : (⟨z, hz⟩ : P) ∈ R := by rw [hReq]; trivial
  exact hzR

/-- The extended metric is built from the actual path infimum. -/
@[instance_reducible] def metricRegionIntrinsicEMetricSpace (P : Set X) : EMetricSpace P where
  edist x z := metricRegionPathEDist P x.1 z.1
  edist_self x := metricRegionPathEDist_self x.2
  edist_comm x z := metricRegionPathEDist_comm P x.1 z.1
  edist_triangle x y z := metricRegionPathEDist_triangle P x.1 y.1 z.1
  eq_of_edist_eq_zero := by
    intro x z he
    apply Subtype.ext
    exact edist_eq_zero.mp (le_antisymm ((edist_le_metricRegionPathEDist P x.1 z.1).trans_eq he) bot_le)

/-- Finiteness is proved before passing from extended distance to a metric. -/
@[instance_reducible] def metricRegionIntrinsicMetricSpace (P : Set X)
    (hconn : IsPreconnected P) (hlocal : MetricRegionRadialPaths P) : MetricSpace P :=
  letI := metricRegionIntrinsicEMetricSpace P
  EMetricSpace.toMetricSpace (fun x z ↦
    (metricRegionPathEDist_lt_top_of_connected hconn hlocal x.2 z.2).ne)

theorem metricRegionIntrinsicMetricSpace_edist (P : Set X)
    (hconn : IsPreconnected P) (hlocal : MetricRegionRadialPaths P) (x z : P) :
    @edist P (metricRegionIntrinsicMetricSpace P hconn hlocal).toEDist x z =
      metricRegionPathEDist P x.1 z.1 := rfl

theorem metricRegionIntrinsicMetricSpace_dist (P : Set X)
    (hconn : IsPreconnected P) (hlocal : MetricRegionRadialPaths P) (x z : P) :
    @dist P (metricRegionIntrinsicMetricSpace P hconn hlocal).toDist x z =
      (metricRegionPathEDist P x.1 z.1).toReal := rfl

end RepulsiveCoulomb
