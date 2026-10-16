import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! SOURCE-ONLY, UNCOMPILED. Point-centered local metric bounds globalize
along genuine minimizing segments. The proof is continuous induction on the
parameter interval: the closed set of parameters reachable with the sharp
bound has no maximal point before the endpoint. No subdivision at seams,
number of seam crossings, global distance inequality, or global isometry is
an input. In particular, no epsilon loss is needed. -/
noncomputable section
open Set Filter
open scoped Topology NNReal
namespace RepulsiveCoulomb

/-- A point-centered bound is enough for continuity; a common neighborhood
on which all pairs satisfy the bound is not required. -/
theorem continuous_of_centered_local_dist_bound
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {c : ℝ} {F : X → Y}
    (hlocal : ∀ x, ∀ᶠ y in 𝓝 x, dist (F x) (F y) ≤ c * dist x y) :
    Continuous F := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hsmall : ∀ᶠ y in 𝓝 x, c * dist x y < ε := by
    apply (isOpen_lt (continuous_const.mul (continuous_const.dist continuous_id))
      continuous_const).mem_nhds
    simpa using hε
  filter_upwards [hlocal x, hsmall] with y hy hsmall
  simpa only [dist_comm] using hy.trans_lt hsmall

/-- Continuous induction, retaining the exact centered-local constant.
Only rightward estimates are used in the induction, although the hypothesis
is conveniently symmetric and hence can be pulled back from a metric space. -/
theorem interval_endpoint_dist_le_of_centered_local_bound
    {Y : Type*} [PseudoMetricSpace Y] {a b c : ℝ} {γ : ℝ → Y}
    (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    (hlocal : ∀ t ∈ Icc a b, ∀ᶠ s in 𝓝[Icc a b] t,
      dist (γ t) (γ s) ≤ c * |s - t|) :
    dist (γ a) (γ b) ≤ c * (b - a) := by
  let S : Set ℝ := {t | dist (γ a) (γ t) ≤ c * (t - a)}
  have hclosed : IsClosed (S ∩ Icc a b) := by
    have hd : ContinuousOn (fun t ↦ dist (γ a) (γ t)) (Icc a b) :=
      continuousOn_iff_continuous_restrict.mpr
        (continuous_const.dist (continuousOn_iff_continuous_restrict.mp hγ))
    have hl : ContinuousOn (fun t : ℝ ↦ c * (t - a)) (Icc a b) :=
      (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn
    convert isClosed_Icc.isClosed_le hd hl using 1
    ext t
    simp only [S, mem_inter_iff, mem_setOf_eq, and_comm]
  have ha : a ∈ S := by simp [S]
  change b ∈ S
  apply hclosed.mem_of_ge_of_forall_exists_gt ha hab
  intro t ht
  have hnear : ∀ᶠ s in 𝓝[>] t, dist (γ t) (γ s) ≤ c * |s - t| :=
    nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem ht.2)
      (hlocal t (Ico_subset_Icc_self ht.2))
  obtain ⟨s, hs, hts⟩ := (hnear.and (Ioc_mem_nhdsGT ht.2.2)).exists
  refine ⟨s, ?_, hts⟩
  change dist (γ a) (γ s) ≤ c * (s - a)
  have htbound : dist (γ a) (γ t) ≤ c * (t - a) := ht.1
  rw [abs_of_pos (sub_pos.mpr hts.1)] at hs
  have htri := dist_triangle (γ a) (γ t) (γ s)
  nlinarith

/-- The unit-interval subtype version used by the actual minimizing paths.
Projection to the interval is only a parameter extension, not a change to
the geometric path or to the metric. -/
theorem unitInterval_dist_le_of_centered_local_bound
    {Y : Type*} [PseudoMetricSpace Y] {c : ℝ}
    {γ : Icc (0 : ℝ) 1 → Y} (hγ : Continuous γ)
    (hlocal : ∀ t, ∀ᶠ s in 𝓝 t,
      dist (γ t) (γ s) ≤ c * |s.1 - t.1|) :
    dist (γ ⟨0, by norm_num⟩) (γ ⟨1, by norm_num⟩) ≤ c := by
  let p : ℝ → Icc (0 : ℝ) 1 := projIcc 0 1 (by norm_num)
  let G : ℝ → Y := γ ∘ p
  have hp : Continuous p := continuous_projIcc
  have hG : Continuous G := hγ.comp hp
  have hlocal' : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] t,
      dist (G t) (G s) ≤ c * |s - t| := by
    intro t ht
    have hpt : Tendsto p (𝓝[Icc (0 : ℝ) 1] t) (𝓝 (p t)) :=
      (hp.tendsto t).mono_left nhdsWithin_le_nhds
    have h := hpt.eventually (hlocal (p t))
    filter_upwards [h, self_mem_nhdsWithin] with s hs hsi
    simpa only [G, Function.comp_apply, p, projIcc_of_mem (by norm_num) ht,
      projIcc_of_mem (by norm_num) hsi] using hs
  have h := interval_endpoint_dist_le_of_centered_local_bound
    (by norm_num : (0 : ℝ) ≤ 1) hG.continuousOn hlocal'
  simpa [G, p, projIcc] using h

/-- On a source with actual minimizing parameterized segments, centered
local estimates give the global sharp estimate. Segment existence is a
geometric source hypothesis, independent of the map being estimated. -/
theorem lipschitzWith_of_centered_local_dist_bound_of_segments
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {K : ℝ≥0} {F : X → Y}
    (hsegment : ∀ x z : X, ∃ γ : Icc (0 : ℝ) 1 → X,
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = z ∧ Continuous γ ∧
      ∀ s t, dist (γ s) (γ t) = |t.1 - s.1| * dist x z)
    (hlocal : ∀ x, ∀ᶠ y in 𝓝 x, dist (F x) (F y) ≤ K * dist x y) :
    LipschitzWith K F := by
  have hF : Continuous F := continuous_of_centered_local_dist_bound hlocal
  apply LipschitzWith.of_dist_le_mul
  intro x z
  obtain ⟨γ, h0, h1, hγ, hd⟩ := hsegment x z
  have hcomp : ∀ t, ∀ᶠ s in 𝓝 t,
      dist (F (γ t)) (F (γ s)) ≤ ((K : ℝ) * dist x z) * |s.1 - t.1| := by
    intro t
    filter_upwards [hγ.continuousAt.eventually (hlocal (γ t))] with s hs
    rw [hd] at hs
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hs
  have h := unitInterval_dist_le_of_centered_local_bound (hF.comp hγ) hcomp
  simpa only [Function.comp_apply, h0, h1] using h

/-- An actual segment inside a convex set. This supplies the preceding
geometric hypothesis for Euclidean chart disks and their convex subdomains. -/
theorem exists_minimizing_segment_of_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : Convex ℝ U) {x z : E} (hx : x ∈ U) (hz : z ∈ U) :
    ∃ γ : Icc (0 : ℝ) 1 → E,
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = z ∧ Continuous γ ∧
      (∀ t, γ t ∈ U) ∧
      ∀ s t, dist (γ s) (γ t) = |t.1 - s.1| * dist x z := by
  refine ⟨fun t ↦ AffineMap.lineMap x z t.1, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · exact (lipschitzWith_lineMap x z).continuous.comp continuous_subtype_val
  · intro t
    exact hU.lineMap_mem hx hz t.2
  · intro s t
    rw [dist_lineMap_lineMap]
    rw [Real.dist_eq, abs_sub_comm]

end RepulsiveCoulomb
