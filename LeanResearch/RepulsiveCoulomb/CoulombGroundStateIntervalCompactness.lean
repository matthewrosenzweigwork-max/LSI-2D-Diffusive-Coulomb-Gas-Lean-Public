import LeanResearch.RepulsiveCoulomb.CoulombGroundStateIntervalBounds
import LeanResearch.RepulsiveCoulomb.CoulombGroundStateCoreL2
import LeanResearch.RepulsiveCoulomb.SmoothMomentCompactness

/-! RECORDS-ONLY UNCHECKED DRAFT. Compactness of the actual union of
bounded core ground states over a positive compact temperature interval. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
namespace RepulsiveCoulomb

abbrev CoulombIntervalCore (N : ℕ) (a b R : ℝ) (ha : 0 < a) :=
  (t : Set.Icc a b) × {φ : TestFunction (coulombDomain N) ℝ ⊤ //
    ‖coulombFormCore (ha.trans_le t.2.1) φ‖ ≤ R}

def coulombIntervalGroundStateLp (N : ℕ) (a b R : ℝ) (ha : 0 < a)
    (i : CoulombIntervalCore N a b R ha) : Lp ℝ 2 (volume : Measure (CoulombConfig N)) :=
  coulombGroundStateCoreLp (ha.trans_le i.1.2.1) i.2.1

theorem coulombIntervalGroundState_compact (N : ℕ) (a b R : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    IsCompact (closure (range (coulombIntervalGroundStateLp N a b R ha))) := by
  let I := CoulombIntervalCore N a b R ha
  let f : I → CoulombConfig N → ℝ := fun i =>
    coulombGroundStateCore (ha.trans_le i.1.2.1) i.2.1
  let A := coulombGroundStateBallBound N b R
  have hA : 0 < A := coulombGroundStateBallBound_pos N (ha.trans_le hab) R
  have hLp (i : I) : MemLp (f i) 2 volume :=
    (coulombGroundStateCore (ha.trans_le i.1.2.1) i.2.1).continuous.memLp_of_hasCompactSupport
      (coulombGroundStateCore (ha.trans_le i.1.2.1) i.2.1).hasCompactSupport
  have hbounds (i : I) := coulombGroundState_core_interval_bounds
    ha i.1.2.1 i.1.2.2 R i.2.1 i.2.2
  have hv (i : I) : eLpNorm (f i) 2 volume ≤ ENNReal.ofReal (Real.sqrt A) := by
    rw [repulsive_eLpNorm_two_eq_sqrt (hLp i)]
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hbounds i).1)
  have hd (i : I) : eLpNorm (fderiv ℝ (f i)) 2 volume ≤ ENNReal.ofReal (Real.sqrt A) := by
    let ψ := coulombGroundStateCore (ha.trans_le i.1.2.1) i.2.1
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
    coulombCore_quadratic_moment_integrable (coulombGroundStateCore (ha.trans_le i.1.2.1) i.2.1)
  have hc := repulsive_smooth_moment_compactness (μ := (volume : Measure (CoulombConfig N)))
    f (fun i => (coulombGroundStateCore (ha.trans_le i.1.2.1) i.2.1).contDiff.of_le (by simp)) hLp
    (Real.sqrt_nonneg A) (show 0 ≤ 4 * A / a ^ 2 by positivity)
    hv hd hm (fun i => (hbounds i).2.2)
  exact hc

end RepulsiveCoulomb
