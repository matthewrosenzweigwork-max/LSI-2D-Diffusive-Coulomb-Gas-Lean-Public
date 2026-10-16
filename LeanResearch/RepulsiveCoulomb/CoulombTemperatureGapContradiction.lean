module

public import LeanResearch.RepulsiveCoulomb.CoulombTemperatureCoreSequence
public import LeanResearch.RepulsiveCoulomb.CoulombTemperatureCompactSubsequence
public import LeanResearch.RepulsiveCoulomb.CoulombGroundStateIntervalDrift
public import LeanResearch.RepulsiveCoulomb.CoulombTemperatureEnergyLimit
public import LeanResearch.RepulsiveCoulomb.CoulombGroundStateClosedLimit
public import LeanResearch.RepulsiveCoulomb.CoulombGroundStateSequenceIdentities
public import LeanResearch.RepulsiveCoulomb.CoulombFixedParticlePoincare

@[expose] public section

/-! RECORDS-ONLY UNCHECKED DRAFT. The actual normalized-sequence contradiction
for a fixed particle number and a positive compact temperature interval. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombTemperature_no_unit_meanZero_smallGradient {N : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (β : ℕ → ℝ) (hb : ∀ n, β n ∈ Set.Icc a b)
    (u : (n : ℕ) → CoulombFormDomain N (ha.trans_le (hb n).1))
    (hu : ∀ n, ‖u n‖ = 1)
    (hm : ∀ n, poleBranchRealMean N (ha.trans_le (hb n).1)
      (coulombFormValueL N (ha.trans_le (hb n).1) (u n)) = 0)
    (hg : ∀ n, ‖coulombFormGradientL N (ha.trans_le (hb n).1) (u n)‖ ≤
      1 / ((n : ℝ) + 1)) : False := by
  let hβ : ∀ n, 0 < β n := fun n => ha.trans_le (hb n).1
  obtain ⟨φ, herr, hnorm, hgrad, hmean⟩ :=
    coulombTemperature_core_sequence β hβ u hu hm hg
  obtain ⟨hmass, henergy⟩ := coulombTemperature_core_mass_energy β hβ φ hnorm hgrad
  have hbound (n : ℕ) : ‖coulombFormCore (hβ n) (φ n)‖ ≤ 2 := by
    have ht := norm_add_le (coulombFormCore (hβ n) (φ n) - u n) (u n)
    rw [sub_add_cancel, hu n] at ht
    have he : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
    linarith [herr n]
  obtain ⟨βstar, hstar, ψ, σ, hσ, ht, hv⟩ :=
    coulombTemperature_groundState_subsequence ha hab β hb 2 φ hbound
  have hp : 0 < βstar := ha.trans_le hstar.1
  let γ : ℕ → ℝ := β ∘ σ
  let hγ : ∀ n, 0 < γ n := fun n => hβ (σ n)
  let φs : ℕ → TestFunction (coulombDomain N) ℝ ⊤ := φ ∘ σ
  let Ψ : ℕ → TestFunction (coulombDomain N) ℝ ⊤ :=
    fun n => coulombGroundStateCore (hγ n) (φs n)
  let K := 4 * (1 + (N : ℝ) * b) * (|2| + 1) ^ 2 / a ^ 2
  let M := coulombGroundStateBallBound N b 2
  have hS (n : ℕ) : (∫ z : CoulombConfig N,
      ‖gradient (coulombPotential (1 : ℝ)) z‖ ^ 2 * Ψ n z ^ 2) ≤ K :=
    coulombGroundState_core_interval_drift ha (hb (σ n)).1 (hb (σ n)).2 2
      (φ (σ n)) (hbound (σ n))
  have hM (n : ℕ) : (∫ z : CoulombConfig N, Ψ n z ^ 2) ≤ M :=
    (coulombGroundState_core_interval_bounds ha (hb (σ n)).1 (hb (σ n)).2 2
      (φ (σ n)) (hbound (σ n))).1
  have hE : Tendsto (fun n => ∫ z,
      ‖gradient (coulombInverseGroundStateCore (hγ n) (Ψ n) : CoulombConfig N → ℝ) z‖ ^ 2
      ∂coulombMeasure N (γ n)) atTop (𝓝 0) := by
    simpa only [Ψ, φs, γ, Function.comp_def, coulombInverseGroundState_core] using
      henergy.comp hσ.tendsto_atTop
  have hEstar := coulombInverseGroundState_energy_tendsto_zero hp γ hγ Ψ ht K M hS hM hE
  let v : ℕ → CoulombFormDomain N hp := fun n =>
    coulombFormCore hp (coulombInverseGroundStateCore hp (Ψ n))
  have hvG : Tendsto (fun n => coulombGroundStateL2 hp (coulombFormValueL N hp (v n)))
      atTop (𝓝 ψ) := by
    simpa only [v, Ψ, coulombGroundStateL2_core, coulombGroundStateCoreLp_inverse_temperature,
      φs, γ, Function.comp_def] using hv
  have hvE : Tendsto (fun n => ‖coulombFormGradientL N hp (v n)‖ ^ 2) atTop (𝓝 0) := by
    have heq (n : ℕ) : ‖coulombFormGradientL N hp (v n)‖ ^ 2 =
        ∫ z, ‖gradient (coulombInverseGroundStateCore hp (Ψ n) : CoulombConfig N → ℝ) z‖ ^ 2
          ∂coulombMeasure N βstar :=
      coulombFormCore_energy_eq_integral hp (coulombInverseGroundStateCore hp (Ψ n))
    simpa only [heq] using hEstar
  have hvgrad : Tendsto (fun n => coulombFormGradientL N hp (v n)) atTop (𝓝 0) := by
    have hs := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hvE
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Function.comp_def, sub_zero, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs
  obtain ⟨w, hw, hwgrad, _hwlim⟩ :=
    coulombGroundState_closed_zero_gradient_limit hp v ψ hvG hvgrad
  have hpairzero : inner ℝ ψ (coulombSqrtDensityLp N βstar) = 0 :=
    coulombGroundStateCoreLp_limit_mean_zero hp γ hγ φs ψ ht hv
      (hmean.comp hσ.tendsto_atTop)
  have hwmean : poleBranchRealMean N hp (coulombFormValueL N hp w) = 0 := by
    rw [← hw, coulombGroundStateL2_mean_pairing] at hpairzero
    simpa only [poleBranchRealMean_eq_integral] using hpairzero
  have hwzero := coulombForm_meanZero_zeroGradient_eq_zero hp w hwmean hwgrad
  have hψzero : ψ = 0 := by
    rw [hwzero, map_zero, map_zero] at hw
    exact hw.symm
  have hψnorm : ‖ψ‖ ^ 2 = 1 := by
    have hlim1 : Tendsto (fun n => ‖coulombGroundStateCoreLp (hβ (σ n)) (φ (σ n))‖ ^ 2)
        atTop (𝓝 1) := by
      simpa only [coulombGroundStateCoreLp_norm_sq, Function.comp_def] using
        hmass.comp hσ.tendsto_atTop
    exact tendsto_nhds_unique (hv.norm.pow 2) hlim1
  rw [hψzero, norm_zero] at hψnorm
  norm_num at hψnorm

end RepulsiveCoulomb
