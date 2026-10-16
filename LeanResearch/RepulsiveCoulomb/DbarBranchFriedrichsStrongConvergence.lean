import LeanResearch.RepulsiveCoulomb.DbarBranchFriedrichsCoreCancellation

/-! Strong convergence of the actual first-order Friedrichs kernel on every
Lebesgue-L2 input. It follows from proved compact-core cancellation, actual
core density and the scale-independent kernel estimate, all in one space. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology
namespace RepulsiveCoulomb

theorem dbarVolumeFriedrichsKernel_sub {N : ℕ} {A B : CoulombConfig N → ℂ}
    (hA : MemLp A ⊤ (volume : Measure (CoulombConfig N)))
    (hB : MemLp B ⊤ (volume : Measure (CoulombConfig N)))
    (ψ : ContDiffBump (0 : CoulombConfig N)) (v : CoulombConfig N)
    (f g : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    dbarVolumeFriedrichsKernel hA hB ψ v (f - g) =
      dbarVolumeFriedrichsKernel hA hB ψ v f - dbarVolumeFriedrichsKernel hA hB ψ v g := by
  simp only [dbarVolumeFriedrichsKernel_split, map_sub, dbarVolumeKernelLp_sub, dbarVolumeLpMollify_sub]
  abel

theorem dbarVolumeFriedrichsKernel_strong_tendsto {N : ℕ} {ι : Type*} {l : Filter ι}
    (A : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (ψ : ContDiffBump (0 : CoulombConfig N)) (v : CoulombConfig N)
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) (hε0 : Tendsto ε l (𝓝 0))
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    Tendsto (fun i => dbarVolumeFriedrichsKernel (A.memLp_top (μ := volume))
      ((dbarVolumeCoreDerivative v A).memLp_top (μ := volume))
      (dbarScaledBump ψ (hε i)) v f) l (𝓝 0) := by
  let B := dbarVolumeCoreDerivative v A
  let K : ι → Lp ℂ 2 (volume : Measure (CoulombConfig N)) → Lp ℂ 2 (volume : Measure (CoulombConfig N)) :=
    fun i g => dbarVolumeFriedrichsKernel (A.memLp_top (μ := volume))
      (B.memLp_top (μ := volume)) (dbarScaledBump ψ (hε i)) v g
  obtain ⟨C, hLip⟩ := dbarVolumeCore_lipschitz A
  obtain ⟨M₀, hM₀⟩ := B.continuous.bounded_above_of_compact_support B.hasCompactSupport
  let M := max M₀ 0
  have hM : ∀ᵐ x ∂volume, ‖B x‖ ≤ M := Eventually.of_forall fun x => (hM₀ x).trans (le_max_left _ _)
  let L : ℝ := (C : ℝ) * dbarBumpDerivativeMoment ψ v + M
  have hL : 0 ≤ L := by
    have hm : 0 ≤ dbarBumpDerivativeMoment ψ v := integral_nonneg fun t => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    exact add_nonneg (mul_nonneg C.coe_nonneg hm) (le_max_right _ _)
  have hbound (i : ι) (g : Lp ℂ 2 (volume : Measure (CoulombConfig N))) : ‖K i g‖ ≤ L * ‖g‖ :=
    dbarScaledBump_friedrichs_uniform_bound (A.memLp_top (μ := volume))
      (B.memLp_top (μ := volume)) hLip hM ψ v (hε i) g
  have hout : Tendsto (fun i => (dbarScaledBump ψ (hε i)).rOut) l (𝓝 0) := by
    simpa only [dbarScaledBump, zero_mul] using hε0.mul_const ψ.rOut
  have hcore (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤) :
      Tendsto (fun i => K i (dbarVolumeCoreValue φ)) l (𝓝 0) :=
    dbarVolumeFriedrichsKernel_core_tendsto A φ (fun i => dbarScaledBump ψ (hε i)) hout v
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hden : 0 < 2 * (L + 1) := by positivity
  obtain ⟨φ, hφ⟩ := (dbarVolumeCoreValue_denseRange N).exists_dist_lt f (div_pos hδ hden)
  have hsmall : L * ‖f - dbarVolumeCoreValue φ‖ < δ / 2 := by
    rw [dist_eq_norm] at hφ
    have h := (lt_div_iff₀ hden).mp hφ
    have hn := norm_nonneg (f - dbarVolumeCoreValue φ)
    nlinarith
  have hφlim := (Metric.tendsto_nhds.mp (hcore φ)) (δ / 2) (half_pos hδ)
  filter_upwards [hφlim] with i hi
  rw [dist_zero_right] at hi ⊢
  calc
    ‖K i f‖ ≤ ‖K i f - K i (dbarVolumeCoreValue φ)‖ + ‖K i (dbarVolumeCoreValue φ)‖ := norm_le_norm_sub_add _ _
    _ = ‖K i (f - dbarVolumeCoreValue φ)‖ + ‖K i (dbarVolumeCoreValue φ)‖ := by
      simp only [K, dbarVolumeFriedrichsKernel_sub]
    _ ≤ L * ‖f - dbarVolumeCoreValue φ‖ + ‖K i (dbarVolumeCoreValue φ)‖ :=
      add_le_add (hbound i _) le_rfl
    _ < δ / 2 + δ / 2 := add_lt_add hsmall hi
    _ = δ := by ring

end RepulsiveCoulomb
