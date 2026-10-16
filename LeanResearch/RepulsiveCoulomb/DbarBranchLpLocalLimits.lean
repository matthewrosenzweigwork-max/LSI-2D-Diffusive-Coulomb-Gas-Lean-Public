module

public import LeanResearch.RepulsiveCoulomb.DbarBranchHolomorphicL2Uniform
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-! Identify a locally uniform function limit with the actual L2 limit by a
proved almost-everywhere convergent subsequence. This step preserves the original
L2 class; local regularity never replaces the data by a new unrelated function. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem dbarLp_uniform_limit_ae {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℂ} {g : X → ℂ} {s : Set X} (hs : MeasurableSet s)
    (fL : ℕ → Lp ℂ 2 μ) (v : Lp ℂ 2 μ)
    (hrep : ∀ n, fL n =ᵐ[μ] f n) (hL : Tendsto fL atTop (𝓝 v))
    (hu : TendstoUniformlyOn f g atTop s) : v =ᵐ[μ.restrict s] g := by
  obtain ⟨ns, hns, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hL).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ n, fL n x = f n x := ae_all_iff.mpr hrep
  filter_upwards [ae_restrict_of_ae hlim, ae_restrict_of_ae hall, ae_restrict_mem hs]
    with x hxl hxrep hxs
  have hxl' : Tendsto (fun i => f (ns i) x) atTop (𝓝 (v x)) :=
    hxl.congr' (Eventually.of_forall fun i => hxrep (ns i))
  exact tendsto_nhds_unique hxl' ((hu.tendsto_at hxs).comp hns.tendsto_atTop)

theorem coulomb_holomorphic_L2_local_limit {N : ℕ}
    {f : ℕ → CoulombConfig N → ℂ}
    (fL : ℕ → Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (v : Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (hrep : ∀ n, fL n =ᵐ[volume] f n) {c : CoulombConfig N} {r : ℝ} (hr : 0 < r)
    (hc : ∀ n, Continuous (f n)) (hf : ∀ n, DifferentiableOn ℂ (f n) (ball c (3 * r)))
    (hL : Tendsto fL atTop (𝓝 v)) :
    ∃ g : CoulombConfig N → ℂ, DifferentiableOn ℂ g (ball c r) ∧
      v =ᵐ[volume.restrict (ball c r)] g := by
  have huc : UniformCauchySeqOn f atTop (ball c (2 * r)) :=
    coulomb_holomorphic_L2_uniformCauchy fL hrep hr (by linarith) hc hf hL.cauchySeq
  obtain ⟨g, hg⟩ := dbarUniformCauchy_exists_limit huc
  have h2R : 2 * r ≤ 3 * r := by linarith
  refine ⟨g, dbarHolomorphic_uniform_limit_on_inner_ball (by linarith : r < 2 * r)
    (fun n => (hf n).mono (ball_subset_ball h2R)) hg, ?_⟩
  exact dbarLp_uniform_limit_ae measurableSet_ball fL v hrep hL
    (hg.mono (ball_subset_ball (by linarith)))

end RepulsiveCoulomb
