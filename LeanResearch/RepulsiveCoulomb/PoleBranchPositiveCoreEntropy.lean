import LeanResearch.RepulsiveCoulomb.CoulombFormIntegrals
import LeanResearch.PeriodicAttractiveLogGas.Entropy
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.OpenPos

/-! RECORDS-ONLY UNCOMPILED. A genuine finite positive entropy test from the
original compact smooth collision-free core. Positivity uses open-set Gibbs
mass, transferred from volume by the checked a.e. equivalence; it does not
assert positive Gibbs density at a collision point. -/
noncomputable section
open Set MeasureTheory Filter InformationTheory
open PeriodicAttractiveLogGas
open scoped Topology
namespace RepulsiveCoulomb

theorem poleBranch_coulomb_isOpenPosMeasure {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    Measure.IsOpenPosMeasure (coulombMeasure N β) := by
  constructor
  intro U hU hne hzero
  have hset : {z : CoulombConfig N | z ∈ U} = U := by ext z; rfl
  have hae : ∀ᵐ z ∂coulombMeasure N β, z ∉ U := by
    simpa only [ae_iff, not_not, hset] using hzero
  have hv := (coulombMeasure_ae_iff hβ).mp hae
  have hnull : volume U = 0 := by simpa only [ae_iff, not_not, hset] using hv
  exact hU.measure_ne_zero volume hne hnull

theorem poleBranch_real_core_square_integrable {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    Integrable (fun z => φ z ^ 2) (coulombMeasure N β) := by
  letI := coulombMeasure_isProbability (N := N) hβ
  exact (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport :
    MemLp (φ : CoulombConfig N → ℝ) 2 (coulombMeasure N β)).integrable_sq

theorem poleBranch_real_core_square_log_integrable {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    Integrable (fun z => φ z ^ 2 * Real.log (φ z ^ 2)) (coulombMeasure N β) := by
  letI := coulombMeasure_isProbability (N := N) hβ
  have hs : HasCompactSupport (fun z : CoulombConfig N => φ z ^ 2) :=
    φ.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hl : HasCompactSupport (fun z : CoulombConfig N => φ z ^ 2 * Real.log (φ z ^ 2)) :=
    hs.comp_left (g := fun t : ℝ => t * Real.log t) (by simp)
  exact (Real.continuous_mul_log.comp (φ.continuous.pow 2)).integrable_of_hasCompactSupport hl

theorem poleBranch_real_core_zero_at_full_collision (N : ℕ)
    (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤) : φ 0 = 0 := by
  have hnot : (0 : CoulombConfig (N + 2)) ∉ coulombDomain (N + 2) := by
    intro hz
    have h := (coulombVandermonde_ne_zero_iff (0 : CoulombConfig (N + 2))).mp hz
      0 (Fin.succ 0) (by simp)
    exact h rfl
  exact image_eq_zero_of_notMem_tsupport (fun h => hnot (φ.tsupport_subset h))

theorem poleBranch_exists_core_positive_entropy (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∃ φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤, ∃ H : ℝ,
      0 < H ∧ (∫ z, φ z ^ 2 ∂coulombMeasure (N + 2) β) = 1 ∧
      entropy (coulombMeasure (N + 2) β) (fun z => φ z ^ 2) = (H : EReal) := by
  letI := coulombMeasure_isProbability (N := N + 2) hβ
  letI := poleBranch_coulomb_isOpenPosMeasure (N := N + 2) hβ
  obtain ⟨z, hz⟩ := coulombDomain_nonempty (N + 2)
  obtain ⟨f, hsupport, hcompact, hsmooth, hvalues, hfz⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) ((coulombDomain (N + 2)).isOpen.mem_nhds hz)
  let φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤ := ⟨f, hsmooth, hcompact, hsupport⟩
  let m : ℝ := ∫ x, φ x ^ 2 ∂coulombMeasure (N + 2) β
  have hm : 0 < m := integral_pos_of_integrable_nonneg_nonzero (x := z) (φ.continuous.pow 2)
    (poleBranch_real_core_square_integrable hβ φ) (fun x => sq_nonneg _)
    (by change f z ^ 2 ≠ 0; rw [hfz]; norm_num)
  let ψ : TestFunction (coulombDomain (N + 2)) ℝ ⊤ := (Real.sqrt m)⁻¹ • φ
  have hψ (x : CoulombConfig (N + 2)) : ψ x = (Real.sqrt m)⁻¹ * φ x := rfl
  have hmass : (∫ x, ψ x ^ 2 ∂coulombMeasure (N + 2) β) = 1 := by
    simp_rw [hψ, mul_pow]
    rw [integral_const_mul]
    change (Real.sqrt m)⁻¹ ^ 2 * m = 1
    rw [inv_pow, Real.sq_sqrt hm.le, inv_mul_cancel₀ hm.ne']
  have hi := poleBranch_real_core_square_integrable hβ ψ
  have hlog := poleBranch_real_core_square_log_integrable hβ ψ
  have hplus : Integrable (fun x => ψ x ^ 2 * Real.log (ψ x ^ 2) + 1)
      (coulombMeasure (N + 2) β) := hlog.add (integrable_const 1)
  have hkl : Integrable (fun x => klFun (ψ x ^ 2)) (coulombMeasure (N + 2) β) :=
    (hlog.add (integrable_const 1)).sub hi
  have hklpos : 0 < ∫ x, klFun (ψ x ^ 2) ∂coulombMeasure (N + 2) β :=
    integral_pos_of_integrable_nonneg_nonzero (x := (0 : CoulombConfig (N + 2)))
      (continuous_klFun.comp (ψ.continuous.pow 2)) hkl (fun x => klFun_nonneg (sq_nonneg _))
      (by rw [poleBranch_real_core_zero_at_full_collision N ψ, zero_pow (by decide : 2 ≠ 0), klFun_zero]; norm_num)
  refine ⟨ψ, ∫ x, klFun (ψ x ^ 2) ∂coulombMeasure (N + 2) β, hklpos, hmass, ?_⟩
  rw [entropy_eq_integral (Eventually.of_forall (fun x => sq_nonneg (ψ x))) hlog,
    hmass, Real.log_one, mul_zero, sub_zero]
  congr 1
  simp only [klFun]
  rw [integral_sub hplus hi,
    integral_add hlog (integrable_const 1), hmass]
  simp

theorem poleBranch_exists_form_positive_entropy (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∃ u : CoulombFormDomain (N + 2) hβ, ∃ H : ℝ, 0 < H ∧
      entropy (coulombMeasure (N + 2) β)
        (fun z => (coulombFormValueL (N + 2) hβ u z) ^ 2) = (H : EReal) := by
  obtain ⟨φ, H, hH, hmass, hent⟩ := poleBranch_exists_core_positive_entropy N hβ
  refine ⟨coulombFormCore hβ φ, H, hH, ?_⟩
  have hsq : (fun z => (coulombFormValueL (N + 2) hβ (coulombFormCore hβ φ) z) ^ 2)
      =ᵐ[coulombMeasure (N + 2) β] (fun z => φ z ^ 2) := by
    filter_upwards [coulombFormCore_value hβ φ] with z hz
    rw [hz]
  exact (entropy_congr_ae hsq).trans hent

end RepulsiveCoulomb
