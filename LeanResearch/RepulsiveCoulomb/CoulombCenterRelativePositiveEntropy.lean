import LeanResearch.RepulsiveCoulomb.CoulombCenterOptimalOrder

/-! A genuine normalized compact relative-core test with positive finite
entropy. This supplies finite upper bounds for the actual relative optimal
rate, rather than assuming finiteness or taking real sSup of an unbounded set. -/
noncomputable section
open Set MeasureTheory Filter InformationTheory
open PeriodicAttractiveLogGas
open scoped Topology ENNReal
namespace RepulsiveCoulomb

variable {n : ℕ}

theorem coulombCenterRelativeProjection_insert (e : CoulombCenterRotation n)
    (c : ℂ) (r : CoulombConfig n) :
    coulombCenterRelativeProjection e (coulombCenterInsert e c r) = r := by
  rw [coulombCenterRelativeProjection_eq_chart, coulombCenterChart_insert]

theorem coulombCenterRelativeProjection_surjective (e : CoulombCenterRotation n) :
    Function.Surjective (coulombCenterRelativeProjection e) :=
  fun r => ⟨coulombCenterInsert e 0 r, coulombCenterRelativeProjection_insert e 0 r⟩

theorem coulombCenterRelativeMeasure_isOpenPos (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) :
    Measure.IsOpenPosMeasure (coulombCenterRelativeMeasure e β) := by
  letI := poleBranch_coulomb_isOpenPosMeasure (N := n + 1) hβ
  have hp := coulombCenterRelativeProjection_measurePreserving e he hβ
  constructor
  intro U hU hne hzero
  have hpre : (coulombCenterRelativeProjection e ⁻¹' U).Nonempty := by
    obtain ⟨r, hr⟩ := hne
    obtain ⟨z, rfl⟩ := coulombCenterRelativeProjection_surjective e r
    exact ⟨z, hr⟩
  have hmass : coulombMeasure (n + 1) β (coulombCenterRelativeProjection e ⁻¹' U) = 0 := by
    rw [← hp.map_eq, Measure.map_apply hp.measurable hU.measurableSet] at hzero
    exact hzero
  exact (hU.preimage (coulombCenterRelativeProjection e).continuous).measure_ne_zero
    (coulombMeasure (n + 1) β) hpre hmass

theorem coulombCenterRelativeDomain_nonempty (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) : (coulombCenterRelativeDomain e : Set (CoulombConfig n)).Nonempty := by
  obtain ⟨z, hz⟩ := coulombDomain_nonempty (n + 1)
  let p := coulombCenterChart e z
  have hz' : coulombCenterInsert e p.1 p.2 ∈ coulombDomain (n + 1) := by
    rw [← coulombCenterChart_symm_apply]
    change (coulombCenterChart e).symm (coulombCenterChart e z) ∈ coulombDomain (n + 1)
    rw [MeasurableEquiv.symm_apply_apply]
    exact hz
  exact ⟨p.2, (coulombCenterInsert_mem_domain_iff e he p.1 p.2).mp hz'⟩

theorem coulombCenterRelativeCore_zero (m : ℕ) (e : CoulombCenterRotation (m + 1))
    (ψ : TestFunction (coulombCenterRelativeDomain e) ℝ ⊤) : ψ 0 = 0 := by
  have hnot : (0 : CoulombConfig (m + 1)) ∉ coulombCenterRelativeDomain e := by
    intro hz
    change e.symm (coulombCenterRelativeInjection (m + 1) 0) ∈ coulombDomain (m + 2) at hz
    simp only [map_zero] at hz
    have h := (coulombVandermonde_ne_zero_iff (0 : CoulombConfig (m + 2))).mp hz
      0 (Fin.succ 0) (by simp)
    exact h rfl
  exact image_eq_zero_of_notMem_tsupport (fun h => hnot (ψ.tsupport_subset h))

theorem coulombCenterRelative_exists_core_positive_entropy (m : ℕ)
    (e : CoulombCenterRotation (m + 1)) (he : CoulombCenterAxis e)
    {β : ℝ} (hβ : 0 < β) :
    ∃ ψ : TestFunction (coulombCenterRelativeDomain e) ℝ ⊤, ∃ H : ℝ,
      0 < H ∧ (∫ r, ψ r ^ 2 ∂coulombCenterRelativeMeasure e β) = 1 ∧
        entropy (coulombCenterRelativeMeasure e β) (fun r => ψ r ^ 2) = (H : EReal) := by
  let μ := coulombCenterRelativeMeasure e β
  letI : IsProbabilityMeasure μ := coulombCenterRelativeMeasure_isProbability e he hβ
  letI : Measure.IsOpenPosMeasure μ := coulombCenterRelativeMeasure_isOpenPos e he hβ
  have hi (ψ : TestFunction (coulombCenterRelativeDomain e) ℝ ⊤) :
      Integrable (fun r => ψ r ^ 2) μ :=
    (ψ.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport : MemLp (ψ : CoulombConfig (m + 1) → ℝ) 2 μ).integrable_sq
  have hl (ψ : TestFunction (coulombCenterRelativeDomain e) ℝ ⊤) :
      Integrable (fun r => ψ r ^ 2 * Real.log (ψ r ^ 2)) μ := by
    have hs : HasCompactSupport (fun r : CoulombConfig (m + 1) => ψ r ^ 2) :=
      ψ.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact (Real.continuous_mul_log.comp (ψ.continuous.pow 2)).integrable_of_hasCompactSupport
      (hs.comp_left (g := fun t : ℝ => t * Real.log t) (by simp))
  obtain ⟨z, hz⟩ := coulombCenterRelativeDomain_nonempty e he
  obtain ⟨f, hsupp, hcomp, hsmooth, hvalues, hfz⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) ((coulombCenterRelativeDomain e).isOpen.mem_nhds hz)
  let φ : TestFunction (coulombCenterRelativeDomain e) ℝ ⊤ := ⟨f, hsmooth, hcomp, hsupp⟩
  let mass : ℝ := ∫ r, φ r ^ 2 ∂μ
  have hm : 0 < mass := integral_pos_of_integrable_nonneg_nonzero (x := z)
    (φ.continuous.pow 2) (hi φ) (fun r => sq_nonneg _)
    (by change f z ^ 2 ≠ 0; rw [hfz]; norm_num)
  let ψ : TestFunction (coulombCenterRelativeDomain e) ℝ ⊤ := (Real.sqrt mass)⁻¹ • φ
  have hψ (r : CoulombConfig (m + 1)) : ψ r = (Real.sqrt mass)⁻¹ * φ r := rfl
  have hmass : (∫ r, ψ r ^ 2 ∂μ) = 1 := by
    simp_rw [hψ, mul_pow]
    rw [integral_const_mul]
    change (Real.sqrt mass)⁻¹ ^ 2 * mass = 1
    rw [inv_pow, Real.sq_sqrt hm.le, inv_mul_cancel₀ hm.ne']
  have hlog := hl ψ
  have hplus : Integrable (fun r => ψ r ^ 2 * Real.log (ψ r ^ 2) + 1) μ :=
    hlog.add (integrable_const 1)
  have hkl : Integrable (fun r => klFun (ψ r ^ 2)) μ :=
    (hlog.add (integrable_const 1)).sub (hi ψ)
  have hpos : 0 < ∫ r, klFun (ψ r ^ 2) ∂μ :=
    integral_pos_of_integrable_nonneg_nonzero (x := (0 : CoulombConfig (m + 1)))
      (continuous_klFun.comp (ψ.continuous.pow 2)) hkl (fun r => klFun_nonneg (sq_nonneg _))
      (by rw [coulombCenterRelativeCore_zero m e ψ, zero_pow (by decide : 2 ≠ 0), klFun_zero]; norm_num)
  refine ⟨ψ, ∫ r, klFun (ψ r ^ 2) ∂μ, hpos, hmass, ?_⟩
  rw [entropy_eq_integral (Eventually.of_forall (fun r => sq_nonneg (ψ r))) hlog,
    hmass, Real.log_one, mul_zero, sub_zero]
  congr 1
  simp only [klFun]
  rw [integral_sub hplus (hi ψ), integral_add hlog (integrable_const 1), hmass]
  simp

/-- A single actual positive-entropy relative-core test bounds EVERY rate on
the native closed relative domain. -/
theorem coulombCenterRelativeRates_bddAbove (m : ℕ)
    (e : CoulombCenterRotation (m + 1)) (he : CoulombCenterAxis e)
    {β : ℝ} (hβ : 0 < β) : BddAbove (coulombCenterRelativeRates e he hβ) := by
  obtain ⟨ψ, H, hH, hmass, hent⟩ := coulombCenterRelative_exists_core_positive_entropy m e he hβ
  let E := ∫ r, ‖gradient (ψ : CoulombConfig (m + 1) → ℝ) r‖ ^ 2 ∂coulombCenterRelativeMeasure e β
  have hE : 0 ≤ E := integral_nonneg (fun _ => sq_nonneg _)
  refine ⟨2 * E / H, ?_⟩
  intro ρ hρ
  rcases hρ with rfl | ⟨hρ, hfull⟩
  · exact div_nonneg (mul_nonneg (by norm_num) hE) hH.le
  · have hc := (coulombCenterRelative_full_iff_core e he hβ).mp hfull ψ
    rw [hent] at hc
    have hr : H ≤ (2 / ρ) * E := EReal.coe_le_coe_iff.mp hc
    have hd : H ≤ (2 * E) / ρ := by convert hr using 1 <;> ring
    have hm := (le_div_iff₀ hρ).mp hd
    apply (le_div_iff₀ hH).mpr
    nlinarith

end RepulsiveCoulomb
