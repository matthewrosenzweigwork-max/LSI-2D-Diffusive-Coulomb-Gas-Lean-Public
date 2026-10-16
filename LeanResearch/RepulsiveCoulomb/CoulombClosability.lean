import LeanResearch.RepulsiveCoulomb.CoulombLocalGraph
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-! Closability of the full labeled physical gradient, obtained from local
Haar graph uniqueness and the proved full-measure collision complement. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace Metric
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem ae_restrict_of_small_balls_finiteDim {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (U : Opens E) (P : E → Prop)
    (hlocal : ∀ z ∈ U, ∃ r > 0, ∀ᵐ x ∂volume.restrict (ball z r), P x) :
    ∀ᵐ x ∂volume.restrict U, P x := by
  classical
  choose δ hδ hP using fun z : U => hlocal z z.property
  have hcover : (U : Set E) ⊆ ⋃ z : U, ball (z : E) (δ z) := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hδ ⟨z, hz⟩)⟩
  obtain ⟨S, hS, hcoverS⟩ :=
    (HereditarilyLindelofSpace.isLindelof (U : Set E)).elim_countable_subcover
      (fun z : U => ball (z : E) (δ z)) (fun _ => isOpen_ball) hcover
  have hall : ∀ᵐ x ∂volume.restrict (⋃ z ∈ S, ball (z : E) (δ z)), P x :=
    (ae_restrict_biUnion_iff _ hS P).mpr (fun z _ => hP z)
  exact hall.filter_mono (ae_mono (Measure.restrict_mono_set _ hcoverS))

theorem coulombCoreGraph_zero_gradient {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {J : CoulombJetL2 N β} (hJ : J ∈ coulombCoreGraph N hβ)
    (hv : ∀ᵐ z ∂coulombMeasure N β, WithLp.fst (J z) = 0) :
    ∀ᵐ z ∂coulombMeasure N β, WithLp.snd (J z) = 0 := by
  have hlocal : ∀ᵐ z ∂volume.restrict (coulombDomain N), WithLp.snd (J z) = 0 := by
    apply ae_restrict_of_small_balls_finiteDim
    intro z hz
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (coulombDomain N).isOpen z hz
    have hhalf : 0 < ε / 2 := half_pos hε
    have hcompact : closedBall z (ε / 2) ⊆ coulombDomain N :=
      (closedBall_subset_ball (half_lt_self hε)).trans hball
    refine ⟨ε / 2, hhalf, ?_⟩
    exact coulombCoreGraph_zero_gradient_local hβ (isCompact_closedBall z (ε / 2))
      hcompact ⟨ball z (ε / 2), isOpen_ball⟩ ball_subset_closedBall hJ hv
  apply (coulombMeasure_ae_iff hβ).mpr
  have hwithin := (ae_restrict_iff' (coulombDomain N).isOpen.measurableSet).mp hlocal
  filter_upwards [coulombDomain_ae N, hwithin] with z hz hzero
  exact hzero hz

theorem coulombCoreGraph_zero_of_value_zero {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {J : CoulombJetL2 N β} (hJ : J ∈ coulombCoreGraph N hβ)
    (hv : coulombJetValueL N β J = 0) : J = 0 := by
  have hv' : ∀ᵐ z ∂coulombMeasure N β, WithLp.fst (J z) = 0 := by
    have h := coulombJetValueL_coe N β J
    rw [hv] at h
    filter_upwards [h, (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := coulombMeasure N β))] with z hz hzero
    exact hz.symm.trans hzero
  have hg := coulombCoreGraph_zero_gradient hβ hJ hv'
  have hg' : coulombJetGradientL N β J = 0 := by
    apply Lp.ext
    filter_upwards [coulombJetGradientL_coe N β J, hg,
      (Lp.coeFn_zero (E := CoulombConfig N) (p := 2) (μ := coulombMeasure N β))] with z hz hgz hzero
    exact hz.trans (hgz.trans hzero.symm)
  have hnorm := coulombJet_norm_sq N β J
  simp only [hv, hg', norm_zero] at hnorm
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg J])

end RepulsiveCoulomb
