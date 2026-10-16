module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchSignedGaussian
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchFrullani

@[expose] public section

/-! Genuine repulsivity of the literal planar logarithmic kernel on its
finite absolute-energy zero-mass domain. The proof uses the actual Gaussian
mixture and a justified Fubini identity; positivity is a conclusion. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

/-- Off-diagonal nullity for any non-atomic sigma-finite planar reference. -/
private theorem equilibrium_ae_off_diagonal (μ : Measure ℂ) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ p : ℂ × ℂ ∂μ.prod μ, p.1 ≠ p.2 := by
  apply (Measure.ae_prod_iff_ae_ae (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
  exact Eventually.of_forall (fun x => (μ.ae_ne x).mono (fun _ h => h.symm))

/-- The actual finite-energy signed Coulomb form is nonnegative. The hypotheses
are the natural L1, zero-mass and absolute-energy domain conditions, not an
assumed analytic inequality. -/
theorem equilibriumLogKernel_zeroMass_nonneg {μ : Measure ℂ} [SFinite μ] [NullSingletonClass μ]
    {f : ℂ → ℝ} (hfm : Measurable f) (hf : Integrable f μ) (hf0 : (∫ x, f x ∂μ) = 0)
    (hfg : Integrable (fun p : ℂ × ℂ => f p.1 * f p.2 * equilibriumLogKernel (p.1 - p.2))
      (μ.prod μ)) :
    0 ≤ ∫ p : ℂ × ℂ, f p.1 * f p.2 * equilibriumLogKernel (p.1 - p.2) ∂μ.prod μ := by
  let ν : Measure ℝ := volume.restrict (Ioi 0)
  let G : (ℂ × ℂ) × ℝ → ℝ := fun q => (f q.1.1 * f q.1.2) *
    equilibriumFrullaniIntegrand (‖q.1.1 - q.1.2‖ ^ 2) 1 q.2 / 2
  have hGm : Measurable G := by
    dsimp [G, equilibriumFrullaniIntegrand]
    fun_prop
  have hGs : ∀ᵐ p : ℂ × ℂ ∂μ.prod μ, Integrable (fun t : ℝ => G (p, t)) ν := by
    filter_upwards [equilibrium_ae_off_diagonal μ] with p hp
    exact ((equilibriumFrullani_integrable
      (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hp))) zero_lt_one).const_mul
        (f p.1 * f p.2)).div_const 2
  have hGn : (fun p : ℂ × ℂ => ∫ t, ‖G (p, t)‖ ∂ν) =ᵐ[μ.prod μ]
      (fun p : ℂ × ℂ => ‖f p.1 * f p.2 * equilibriumLogKernel (p.1 - p.2)‖) := by
    filter_upwards [equilibrium_ae_off_diagonal μ] with p hp
    have hd : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hp
    have hr : 0 < ‖p.1 - p.2‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hd)
    have hlog : Real.log (1 / ‖p.1 - p.2‖ ^ 2) =
        2 * equilibriumLogKernel (p.1 - p.2) := by
      rw [one_div, Real.log_inv, Real.log_pow]
      unfold equilibriumLogKernel
      ring
    have he : (fun t : ℝ => ‖G (p, t)‖) =
        (fun t : ℝ => (|f p.1 * f p.2| / 2) *
          |equilibriumFrullaniIntegrand (‖p.1 - p.2‖ ^ 2) 1 t|) := by
      funext t
      dsimp only [G]
      rw [Real.norm_eq_abs, abs_div, abs_mul, Nat.abs_ofNat]
      ring
    rw [he, integral_const_mul, integral_abs_equilibriumFrullani hr zero_lt_one, hlog]
    simp only [Real.norm_eq_abs, abs_mul, Nat.abs_ofNat]
    ring
  have hG : Integrable G ((μ.prod μ).prod ν) :=
    (integrable_prod_iff hGm.aestronglyMeasurable).mpr
      ⟨hGs, hfg.norm.congr hGn.symm⟩
  have hswap := integral_integral_swap (μ := μ.prod μ) (ν := ν)
    (f := fun (p : ℂ × ℂ) (t : ℝ) => G (p, t)) hG
  have hleft : (∫ p : ℂ × ℂ, (∫ t, G (p, t) ∂ν) ∂μ.prod μ) =
      ∫ p : ℂ × ℂ, f p.1 * f p.2 * equilibriumLogKernel (p.1 - p.2) ∂μ.prod μ := by
    apply integral_congr_ae
    filter_upwards [equilibrium_ae_off_diagonal μ] with p hp
    dsimp only [G]
    rw [integral_div, integral_const_mul, equilibriumLogKernel_eq_frullani (sub_ne_zero.mpr hp)]
    ring
  have hright : 0 ≤ ∫ t, (∫ p : ℂ × ℂ, G (p, t) ∂μ.prod μ) ∂ν := by
    apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hk := equilibriumSignedGaussian_integrable ht0 hfm hf
    have hc := hf.mul_prod hf
    have he : (fun p : ℂ × ℂ => G (p, t)) =
        (fun p : ℂ × ℂ => (t⁻¹ / 2) *
          (f p.1 * f p.2 * Real.exp (-t * ‖p.1 - p.2‖ ^ 2)) -
          ((t⁻¹ / 2) * Real.exp (-t)) * (f p.1 * f p.2)) := by
      funext p
      dsimp only [G, equilibriumFrullaniIntegrand]
      rw [show -(‖p.1 - p.2‖ ^ 2) * t = -t * ‖p.1 - p.2‖ ^ 2 by ring]
      simp only [neg_one_mul]
      ring
    rw [he, integral_sub (hk.const_mul _) (hc.const_mul _), integral_const_mul,
      integral_const_mul, integral_prod_mul, hf0, zero_mul, mul_zero, sub_zero]
    exact mul_nonneg (by positivity) (equilibriumSignedGaussian_nonneg ht0 hfm hf)
  rw [hleft] at hswap
  rw [hswap]
  exact hright

end RepulsiveCoulomb
