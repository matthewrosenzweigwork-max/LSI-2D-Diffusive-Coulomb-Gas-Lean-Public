import LeanResearch.RepulsiveCoulomb.CoulombGroundStateCoreBounds
import LeanResearch.RepulsiveCoulomb.CoulombGroundStateCoreL2
import LeanResearch.RepulsiveCoulomb.SmoothMomentCompactness

/-! Actual global compactness of normalized ground states of a bounded
original-core form family. The Gaussian moment estimate and physical gradient
bound discharge the genuine Frechet-Kolmogorov hypotheses. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
namespace RepulsiveCoulomb

theorem coulombGroundStateCore_compact {N : ℕ} {β : ℝ} (hβ : 0 < β) (R : ℝ) :
    IsCompact (closure ((coulombGroundStateCoreLp hβ) ''
      {φ : TestFunction (coulombDomain N) ℝ ⊤ | ‖coulombFormCore hβ φ‖ ≤ R})) := by
  let I := {φ : TestFunction (coulombDomain N) ℝ ⊤ // ‖coulombFormCore hβ φ‖ ≤ R}
  let f : I → CoulombConfig N → ℝ := fun i => coulombGroundStateCore hβ i.val
  let A := coulombGroundStateBallBound N β R
  have hA : 0 < A := coulombGroundStateBallBound_pos N hβ R
  have hLp (i : I) : MemLp (f i) 2 volume :=
    (coulombGroundStateCore hβ i.val).continuous.memLp_of_hasCompactSupport
      (coulombGroundStateCore hβ i.val).hasCompactSupport
  have hbounds (i : I) := coulombGroundState_core_three_bounds hβ R i.val i.property
  have hv (i : I) : eLpNorm (f i) 2 volume ≤ ENNReal.ofReal (Real.sqrt A) := by
    rw [repulsive_eLpNorm_two_eq_sqrt (hLp i)]
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hbounds i).1)
  have hd (i : I) : eLpNorm (fderiv ℝ (f i)) 2 volume ≤ ENNReal.ofReal (Real.sqrt A) := by
    let ψ := coulombGroundStateCore hβ i.val
    have hg : MemLp (gradient (ψ : CoulombConfig N → ℝ)) 2 volume :=
      (TauCeti.continuous_gradient_testFunction ψ).memLp_of_hasCompactSupport
        (TauCeti.hasCompactSupport_gradient_testFunction ψ)
    have he : eLpNorm (fderiv ℝ (f i)) 2 volume =
        eLpNorm (fun z => ‖gradient (ψ : CoulombConfig N → ℝ) z‖) 2 volume := by
      apply eLpNorm_congr_norm_ae
      · exact ((ψ.contDiff.continuous_fderiv (by simp)).aestronglyMeasurable)
      · exact hg.aestronglyMeasurable.norm
      · exact Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          exact (TauCeti.norm_gradient_eq_norm_fderiv (ψ : CoulombConfig N → ℝ) z).symm
    rw [he, repulsive_eLpNorm_two_eq_sqrt hg.norm]
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hbounds i).2.1)
  have hm (i : I) : Integrable (fun z => ‖z‖ ^ 2 * f i z ^ 2) :=
    coulombCore_quadratic_moment_integrable (coulombGroundStateCore hβ i.val)
  have hc := repulsive_smooth_moment_compactness (μ := (volume : Measure (CoulombConfig N)))
    f (fun i => (coulombGroundStateCore hβ i.val).contDiff.of_le (by simp)) hLp
    (Real.sqrt_nonneg A) (show 0 ≤ 4 * A / β ^ 2 by positivity)
    hv hd hm (fun i => (hbounds i).2.2)
  have heq : range (fun i : I => (hLp i).toLp (f i)) =
      (coulombGroundStateCoreLp hβ) ''
        {φ : TestFunction (coulombDomain N) ℝ ⊤ | ‖coulombFormCore hβ φ‖ ≤ R} := by
    ext u
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.property, rfl⟩
    · rintro ⟨φ, hφ, rfl⟩
      exact ⟨⟨φ, hφ⟩, rfl⟩
  rwa [heq] at hc

end RepulsiveCoulomb
