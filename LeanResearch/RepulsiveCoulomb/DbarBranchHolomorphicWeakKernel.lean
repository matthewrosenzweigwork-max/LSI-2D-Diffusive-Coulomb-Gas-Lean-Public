module

public import LeanResearch.RepulsiveCoulomb.DbarBranchCoreCompatibility
public import LeanResearch.RepulsiveCoulomb.PoleBranchDerivativeBounds
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

@[expose] public section

/-! Every genuine holomorphic weighted-L2 representative belongs to the
actual weak kernel. Local derivative integrability follows from measurability
and the actual Schwarz bound, without an extra C1 or analytic hypothesis. -/
noncomputable section
open Set MeasureTheory Filter Metric InnerProductSpace
open scoped Topology Distributions
namespace RepulsiveCoulomb

theorem coulombHolomorphic_real_fderiv_locallyIntegrable {N : ℕ}
    {h : CoulombConfig N → ℂ} (hh : DifferentiableOn ℂ h (coulombDomain N)) :
    LocallyIntegrableOn (fderiv ℝ h) (coulombDomain N) volume := by
  intro z hz
  obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.mp (coulombDomain N).isOpen z hz
  let r : ℝ := R / 2
  have hr : 0 < r := half_pos hR
  have hKrΩ : closedBall z r ⊆ coulombDomain N :=
    (closedBall_subset_ball (by dsimp [r]; linarith)).trans hRΩ
  have hBrΩ : ball z r ⊆ coulombDomain N := ball_subset_closedBall.trans hKrΩ
  obtain ⟨M, hM⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn
    (hh.continuousOn.mono hKrΩ)
  have hb : ∀ x ∈ ball z (r / 2), ‖fderiv ℝ h x‖ ≤ 2 * M / (r - r / 2) := by
    intro x hx
    have hxr : x ∈ ball z r := ball_subset_ball (half_lt_self hr).le hx
    have hCx := ((hh.mono hBrΩ) x hxr).differentiableAt (isOpen_ball.mem_nhds hxr)
    rw [hCx.fderiv_restrictScalars ℝ, ContinuousLinearMap.norm_restrictScalars]
    exact poleBranch_fderiv_norm_le_inner_ball (half_lt_self hr) hx (hh.mono hBrΩ)
      (fun y hy => hM y (ball_subset_closedBall hy))
  have hfin : volume (ball z (r / 2)) < ⊤ :=
    (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall z (r / 2)).measure_lt_top
  have hint : IntegrableOn (fderiv ℝ h) (ball z (r / 2)) volume :=
    Measure.integrableOn_of_bounded hfin.ne (measurable_fderiv ℝ h).aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact hb x hx)
  exact ⟨ball z (r / 2), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z (half_pos hr)), hint⟩

theorem coulombHolomorphic_hasWeakFDeriv {N : ℕ} {h : CoulombConfig N → ℂ}
    (hh : DifferentiableOn ℂ h (coulombDomain N)) :
    TauCeti.HasWeakFDerivOn volume (coulombDomain N) h (fderiv ℝ h) :=
  TauCeti.hasWeakFDerivOn_of_differentiableOn
    (hh.continuousOn.locallyIntegrableOn (coulombDomain N).isOpen.measurableSet)
    (coulombHolomorphic_real_fderiv_locallyIntegrable hh)
    (fun z hz => ((hh z hz).differentiableAt ((coulombDomain N).isOpen.mem_nhds hz)).restrictScalars ℝ)

theorem coulombHolomorphic_weak_dbar_pairing {N : ℕ} {h : CoulombConfig N → ℂ}
    (hh : DifferentiableOn ℂ h (coulombDomain N)) (i : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    (∫ z, (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ
      (coulombCoordinateInjection N i 1) φ) z • h z) +
      Complex.I * (∫ z, (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ
        (coulombCoordinateInjection N i Complex.I) φ) z • h z) = 0 := by
  let vx := coulombCoordinateInjection N i 1
  let vy := coulombCoordinateInjection N i Complex.I
  have hw := coulombHolomorphic_hasWeakFDeriv hh
  have hx := (hw.hasWeakLineDerivOn vx).integral_lineDeriv_smul_eq_neg_integral_smul φ
  have hy := (hw.hasWeakLineDerivOn vy).integral_lineDeriv_smul_eq_neg_integral_smul φ
  have hxi : Integrable (fun z => φ z • fderiv ℝ h z vx) volume :=
    φ.integrable_smul (hw.hasWeakLineDerivOn vx).locallyIntegrableOn_deriv
  have hyi : Integrable (fun z => φ z • fderiv ℝ h z vy) volume :=
    φ.integrable_smul (hw.hasWeakLineDerivOn vy).locallyIntegrableOn_deriv
  have hs : (∫ z, φ z • fderiv ℝ h z vx) + Complex.I * (∫ z, φ z • fderiv ℝ h z vy) = 0 := by
    rw [← integral_const_mul, ← integral_add hxi (hyi.const_mul Complex.I)]
    apply integral_eq_zero_of_ae
    filter_upwards [coulombDomain_ae N] with z hz
    have hd := coulombDbarCoordinate_of_complex_differentiable
      ((hh z hz).differentiableAt ((coulombDomain N).isOpen.mem_nhds hz)) i
    change (fderiv ℝ h z vx + Complex.I * fderiv ℝ h z vy) / 2 = 0 at hd
    have hsum := (div_eq_zero_iff.mp hd).resolve_right (by norm_num)
    simp only [Complex.real_smul, Pi.zero_apply]
    linear_combination (φ z : ℂ) * hsum
  have hx' : (∫ z, (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ vx φ) z • h z) =
      -(∫ z, φ z • fderiv ℝ h z vx) := by
    simpa only [TestFunction.lineDerivCLM_apply, top_add, le_refl, ite_true] using hx
  have hy' : (∫ z, (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ vy φ) z • h z) =
      -(∫ z, φ z • fderiv ℝ h z vy) := by
    simpa only [TestFunction.lineDerivCLM_apply, top_add, le_refl, ite_true] using hy
  change (∫ z, (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ vx φ) z • h z) +
    Complex.I * (∫ z, (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ vy φ) z • h z) = 0
  rw [hx', hy']
  linear_combination -hs

theorem coulombHolomorphic_representative_mem_weakKernel {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (f : Lp ℂ 2 (coulombMeasure N β)) {h : CoulombConfig N → ℂ}
    (hh : DifferentiableOn ℂ h (coulombDomain N)) (hrep : f =ᵐ[coulombMeasure N β] h) :
    (f, 0) ∈ coulombMaxDbarGraph hβ := by
  have hzero : coulombL2Distribution hβ (0 : Lp ℂ 2 (coulombMeasure N β)) = 0 :=
    map_zero (coulombL2DistributionLinear hβ ℂ)
  have heval (φ : TestFunction (coulombDomain N) ℝ ⊤) :
      coulombL2Distribution hβ f φ = ∫ z, φ z • h z := by
    rw [coulombL2Distribution_apply]
    apply integral_congr_ae
    filter_upwards [(coulombMeasure_ae_iff hβ).mp hrep] with z hz
    rw [hz]
  intro i φ
  rw [coulombWeakDbarConstraintL_apply, map_zero, hzero]
  simp only [zero_apply, zero_add]
  rw [heval, heval, coulombHolomorphic_weak_dbar_pairing hh i φ, smul_zero]

end RepulsiveCoulomb
