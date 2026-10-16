import LeanResearch.RepulsiveCoulomb.PointWeightLocalGraph
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-! Closability of the actual weighted physical gradient on the full
point-punctured smooth core. The local Haar result is passed to the whole
punctured plane by a countable open cover, then across the finite null set.
No configuration separation or unproved global lower-density bound enters.
-/
noncomputable section
open MeasureTheory Set Filter TopologicalSpace Metric
open scoped ENNReal Topology
namespace RepulsiveCoulomb

/-- Local almost-everywhere statements on a planar open set can be glued
using a countable subcover. -/
theorem ae_restrict_of_small_balls (U : Opens ℂ) (P : ℂ → Prop)
    (hlocal : ∀ z ∈ U, ∃ r > 0, ∀ᵐ x ∂volume.restrict (ball z r), P x) :
    ∀ᵐ x ∂volume.restrict U, P x := by
  classical
  choose δ hδ hP using fun z : U ↦ hlocal z z.property
  have hcover : (U : Set ℂ) ⊆ ⋃ z : U, ball (z : ℂ) (δ z) := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hδ ⟨z, hz⟩)⟩
  obtain ⟨S, hS, hcoverS⟩ :=
    (HereditarilyLindelofSpace.isLindelof (U : Set ℂ)).elim_countable_subcover
      (fun z : U ↦ ball (z : ℂ) (δ z)) (fun _ ↦ isOpen_ball) hcover
  have hall : ∀ᵐ x ∂volume.restrict (⋃ z ∈ S, ball (z : ℂ) (δ z)), P x :=
    (ae_restrict_biUnion_iff _ hS P).mpr (fun z _ ↦ hP z)
  exact hall.filter_mono (ae_mono (Measure.restrict_mono_set _ hcoverS))

theorem pointDomain_ae {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) :
    ∀ᵐ z : ℂ, z ∈ pointDomain a y := by
  have h : ∀ᵐ z : ℂ, ∀ j, z ≠ y j := ae_all_iff.mpr (fun j ↦ volume.ae_ne (y j))
  filter_upwards [h] with z hz
  change z ∉ pointPunctures a y
  rintro ⟨j, _, hj⟩
  exact hz j hj

theorem pointCoreGraph_zero_gradient {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {J : PointJetL2 γ a y} (hJ : J ∈ pointCoreGraph hγ ha y)
    (hv : ∀ᵐ z ∂pointMeasure γ a y, WithLp.fst (J z) = 0) :
    ∀ᵐ z ∂pointMeasure γ a y, WithLp.snd (J z) = 0 := by
  have hlocal : ∀ᵐ z ∂volume.restrict (pointDomain a y), WithLp.snd (J z) = 0 := by
    apply ae_restrict_of_small_balls
    intro z hz
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (pointDomain a y).isOpen z hz
    have hhalf : 0 < ε / 2 := half_pos hε
    have hcompact : closedBall z (ε / 2) ⊆ (pointPunctures a y)ᶜ :=
      (closedBall_subset_ball (half_lt_self hε)).trans hball
    refine ⟨ε / 2, hhalf, ?_⟩
    exact pointCoreGraph_zero_gradient_local hγ ha y (isCompact_closedBall z (ε / 2))
      hcompact ⟨ball z (ε / 2), isOpen_ball⟩ ball_subset_closedBall hJ hv
  apply (pointMeasure_ae_iff hγ ha y).mpr
  have hwithin := (ae_restrict_iff' (pointDomain a y).isOpen.measurableSet).mp hlocal
  filter_upwards [pointDomain_ae a y, hwithin] with z hz hzero
  exact hzero hz

/-- The zero-value fibre of the closed smooth-core graph is trivial. This is
the closed-graph formulation of closability, for the literal weighted measure. -/
theorem pointCoreGraph_zero_of_value_zero {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {J : PointJetL2 γ a y} (hJ : J ∈ pointCoreGraph hγ ha y)
    (hv : pointJetValueL γ a y J = 0) : J = 0 := by
  have hv' : ∀ᵐ z ∂pointMeasure γ a y, WithLp.fst (J z) = 0 := by
    have h := pointJetValueL_coe γ a y J
    rw [hv] at h
    filter_upwards [h, (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := pointMeasure γ a y))]
      with z hz hzero
    exact hz.symm.trans hzero
  have hg := pointCoreGraph_zero_gradient hγ ha y hJ hv'
  have hg' : pointJetGradientL γ a y J = 0 := by
    apply Lp.ext
    filter_upwards [pointJetGradientL_coe γ a y J, hg,
      (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := pointMeasure γ a y))] with z hz hgz hzero
    exact hz.trans (hgz.trans hzero.symm)
  have hnorm := pointJet_norm_sq γ a y J
  simp only [hv, hg', norm_zero] at hnorm
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg J])

end RepulsiveCoulomb
