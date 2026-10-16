import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDensityMeasure
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchEntropyMixture
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchEntropyTiltDerivative

/-! Actual entropy of a bounded multiplicative density variation. The base
entropy is absolutely integrable and the varying logarithm has a uniform
positive argument near zero. The identities include zero values of the base
density, and the parameter derivative is a genuine HasDerivAt statement. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- The physical entropy variation is integrable and equals the finite linear
base-entropy term plus the entropy of the bounded positive tilt factor. -/
theorem equilibrium_density_tilt_entropy_identity {ρ φ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x)))
    (hφm : Measurable φ) {M t : ℝ} (hM : 0 ≤ M) (hφM : ∀ x, |φ x| ≤ M)
    (ht : t ∈ Ioo (-(1 / (2 * (M + 1)))) (1 / (2 * (M + 1)))) :
    Integrable (fun x : ℂ => ((1 + t * φ x) * ρ x) *
      Real.log ((1 + t * φ x) * ρ x)) ∧
    (∫ x : ℂ, ((1 + t * φ x) * ρ x) * Real.log ((1 + t * φ x) * ρ x)) =
      (∫ x : ℂ, ρ x * Real.log (ρ x)) +
        t * (∫ x : ℂ, (ρ x * Real.log (ρ x)) * φ x) +
        ∫ x : ℂ, (1 + t * φ x) * Real.log (1 + t * φ x) ∂equilibriumDensityMeasure ρ := by
  letI := equilibriumDensityMeasure_probability hρ0 hρi hρmass
  let T : ℂ → ℝ := fun x => (1 + t * φ x) * Real.log (1 + t * φ x)
  have hTm : Measurable T := by dsimp only [T]; fun_prop
  have hTb : ∀ x, ‖T x‖ ≤ (3 / 2 : ℝ) := by
    intro x
    have hb := equilibrium_tilt_factor_bounds hM (hφM x) ht
    have hl := equilibrium_log_near_one_bound hb
    have hpos : 0 ≤ 1 + t * φ x := by linarith [hb.1]
    dsimp only [T]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos]
    have hh := mul_le_mul_of_nonneg_left hl hpos
    simpa only [mul_one] using hh.trans (by simpa only [mul_one] using hb.2)
  have hTi : Integrable T (equilibriumDensityMeasure ρ) :=
    Integrable.of_bound hTm.aestronglyMeasurable (3 / 2) (Eventually.of_forall hTb)
  have hTρ := (equilibriumDensityMeasure_integrable_iff hρm hρ0 T).mp hTi
  have hφH : Integrable (fun x : ℂ => (ρ x * Real.log (ρ x)) * φ x) :=
    hρH.mul_bdd hφm.aestronglyMeasurable (Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using hφM x))
  have he : (fun x : ℂ => ((1 + t * φ x) * ρ x) * Real.log ((1 + t * φ x) * ρ x)) =
      (fun x : ℂ => (ρ x * Real.log (ρ x) + t * ((ρ x * Real.log (ρ x)) * φ x)) + T x * ρ x) := by
    funext x
    have hb := equilibrium_tilt_factor_bounds hM (hφM x) ht
    rw [equilibrium_mul_log_scale (show 0 < 1 + t * φ x by linarith [hb.1]) (hρ0 x)]
    dsimp only [T]
    ring
  have hi := (hρH.add (hφH.const_mul t)).add hTρ
  refine ⟨?_, ?_⟩
  · rw [he]
    exact hi
  · rw [he]
    have h₁ := integral_add hρH (hφH.const_mul t)
    have h₂ := integral_add (hρH.add (hφH.const_mul t)) hTρ
    dsimp only [Pi.add_apply] at h₁ h₂
    rw [h₂, h₁, integral_const_mul]
    congr 1
    rw [integral_equilibriumDensityMeasure hρm hρ0]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by dsimp only [T]; ring)

/-- Differentiation of the actual physical entropy at the unperturbed density.
No boundedness or strict positivity of rho is used here. -/
theorem equilibrium_hasDerivAt_density_tilt_entropy {ρ φ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x)))
    (hφm : Measurable φ) {M : ℝ} (hM : 0 ≤ M) (hφM : ∀ x, |φ x| ≤ M) :
    HasDerivAt (fun t : ℝ => ∫ x : ℂ, ((1 + t * φ x) * ρ x) *
      Real.log ((1 + t * φ x) * ρ x))
      ((∫ x : ℂ, (ρ x * Real.log (ρ x)) * φ x) +
        ∫ x : ℂ, φ x ∂equilibriumDensityMeasure ρ) 0 := by
  letI := equilibriumDensityMeasure_probability hρ0 hρi hρmass
  have hlinear : HasDerivAt (fun t : ℝ => (∫ x : ℂ, ρ x * Real.log (ρ x)) +
      t * (∫ x : ℂ, (ρ x * Real.log (ρ x)) * φ x))
      (∫ x : ℂ, (ρ x * Real.log (ρ x)) * φ x) 0 := by
    exact (hasDerivAt_mul_const (x := (0 : ℝ))
      (∫ x : ℂ, (ρ x * Real.log (ρ x)) * φ x)).const_add (∫ x : ℂ, ρ x * Real.log (ρ x))
  have htilt := equilibrium_hasDerivAt_tilt_entropy (equilibriumDensityMeasure ρ) hφm hM hφM
  apply (hlinear.add htilt).congr_of_eventuallyEq
  have hδ : 0 < 1 / (2 * (M + 1)) := by positivity
  filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hδ) hδ] with t ht
  exact (equilibrium_density_tilt_entropy_identity hρm hρ0 hρi hρmass hρH hφm hM hφM ht).2

/-- The mass-preserving specialization needed by the Euler--Lagrange proof. -/
theorem equilibrium_hasDerivAt_zeroMass_density_tilt_entropy {ρ φ : ℂ → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x)))
    (hφm : Measurable φ) {M : ℝ} (hM : 0 ≤ M) (hφM : ∀ x, |φ x| ≤ M)
    (hφzero : (∫ x : ℂ, φ x ∂equilibriumDensityMeasure ρ) = 0) :
    HasDerivAt (fun t : ℝ => ∫ x : ℂ, ((1 + t * φ x) * ρ x) *
      Real.log ((1 + t * φ x) * ρ x))
      (∫ x : ℂ, (ρ x * Real.log (ρ x)) * φ x) 0 := by
  simpa only [hφzero, add_zero] using
    equilibrium_hasDerivAt_density_tilt_entropy hρm hρ0 hρi hρmass hρH hφm hM hφM

end RepulsiveCoulomb
