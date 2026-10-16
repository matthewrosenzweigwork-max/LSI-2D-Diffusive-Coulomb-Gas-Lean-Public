import LeanResearch.RepulsiveCoulomb.CoulombGaussianFisher
import LeanResearch.RepulsiveCoulomb.CoulombGaussianSharpness
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Elementary end-point comparison and removal of positive regularization.
These are proof steps, not an assertion of Gaussian LSI: the positive Fisher
bound must be filled by the genuine entropy-interpolation calculation before
the final Gaussian theorem can use the core conclusion. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open PeriodicAttractiveLogGas
open scoped Topology ENNReal
namespace RepulsiveCoulomb

/-- The exact coefficient 1/(2β) comes from comparison with the quadratic
primitive, including both endpoints of the compact interpolation interval. -/
theorem coulombGaussian_entropy_interpolation_bound {β C : ℝ} (hβ : 0 < β)
    {H H' : ℝ → ℝ} (hc : ContinuousOn H (Icc 0 1))
    (hd : ∀ s ∈ Ioo 0 1, HasDerivAt H (H' s) s)
    (hb : ∀ s ∈ Ioo 0 1, H' s ≤ s * C / β) :
    H 1 - H 0 ≤ C / (2 * β) := by
  let K : ℝ → ℝ := fun s => H s - C / (2 * β) * s ^ 2
  have hK : ContinuousOn K (Icc 0 1) :=
    hc.sub ((continuous_const.mul (continuous_id.pow 2)).continuousOn)
  have hkd (s : ℝ) (hs : s ∈ Ioo 0 1) :
      HasDerivAt K (H' s - s * C / β) s := by
    have hp : HasDerivAt (fun t : ℝ => C / (2 * β) * t ^ 2) (s * C / β) s := by
      convert ((hasDerivAt_id s).pow 2).const_mul (C / (2 * β)) using 1 <;>
        simp only [Pi.pow_apply, id_eq] <;> ring
    exact (hd s hs).sub hp
  have hanti : AntitoneOn K (Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1) hK
      (f' := fun s => H' s - s * C / β)
    · intro s hs
      exact (hkd s (by simpa only [interior_Icc] using hs)).hasDerivWithinAt
    · intro s hs
      exact sub_nonpos.mpr (hb s (by simpa only [interior_Icc] using hs))
  have h := hanti (show (0 : ℝ) ∈ Icc 0 1 by simp)
    (show (1 : ℝ) ∈ Icc 0 1 by simp) (by norm_num : (0 : ℝ) ≤ 1)
  dsimp only [K] at h
  norm_num at h
  linarith

/-- The Fisher contraction has precisely the derivative bound required by
quadratic comparison, with no lost factor or endpoint assumption. -/
theorem coulombGaussian_entropy_interpolation_fisher_bound {β C : ℝ} (hβ : 0 < β)
    {H J : ℝ → ℝ} (hc : ContinuousOn H (Icc 0 1))
    (hd : ∀ s ∈ Ioo 0 1, HasDerivAt H ((1 / (β * s)) * J s) s)
    (hJ : ∀ s ∈ Ioo 0 1, J s ≤ s ^ 2 * C) :
    H 1 - H 0 ≤ C / (2 * β) := by
  apply coulombGaussian_entropy_interpolation_bound hβ hc hd
  intro s hs
  have hmul := mul_le_mul_of_nonneg_left (hJ s hs)
    (one_div_nonneg.mpr (mul_nonneg hβ.le hs.1.le))
  convert hmul using 1
  field_simp [hβ.ne', hs.1.ne'] <;> ring

/-- A compact smooth planar test has an actual global C¹ bound. -/
theorem coulombGaussian_test_c1_bound (φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) :
    ∃ B : ℝ, 0 < B ∧ ∀ z, ‖φ z‖ ≤ B ∧ ‖fderiv ℝ (φ : ℂ → ℝ) z‖ ≤ B := by
  let f : ℂ → ℝ := fun z => ‖φ z‖ + ‖fderiv ℝ (φ : ℂ → ℝ) z‖
  have hc : Continuous f := φ.continuous.norm.add
    (φ.contDiff.continuous_fderiv (by simp)).norm
  have hs : HasCompactSupport f := φ.hasCompactSupport.norm.add (φ.hasCompactSupport.fderiv ℝ).norm
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro z
  have hf0 : 0 ≤ f z := by dsimp only [f]; positivity
  have hb : f z ≤ |B| + 1 := by
    by_cases hz : z ∈ tsupport f
    · have h := hB z hz
      rw [Real.norm_eq_abs, abs_of_nonneg hf0] at h
      linarith [le_abs_self B]
    · rw [image_eq_zero_of_notMem_tsupport hz]
      positivity
  dsimp only [f] at hb
  constructor <;> linarith [norm_nonneg (φ z), norm_nonneg (fderiv ℝ (φ : ℂ → ℝ) z)]

def coulombGaussianRegularizedSquare (φ : ℂ → ℝ) (ε : ℝ) (z : ℂ) : ℝ := φ z ^ 2 + ε

theorem coulombGaussianRegularizedSquare_fderiv {φ : ℂ → ℝ} (hφ : Differentiable ℝ φ)
    (ε : ℝ) (z : ℂ) :
    fderiv ℝ (coulombGaussianRegularizedSquare φ ε) z = (2 * φ z) • fderiv ℝ φ z := by
  have h := ((hφ z).hasFDerivAt.pow 2).add_const ε
  change fderiv ℝ (fun x => φ x ^ 2 + ε) z = (2 * φ z) • fderiv ℝ φ z
  simpa only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, nsmul_eq_mul] using h.fderiv

theorem coulombGaussianRegularizedSquare_fisher_le {φ : ℂ → ℝ} (hφ : Differentiable ℝ φ)
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    coulombGaussianFisherDensity (coulombGaussianRegularizedSquare φ ε) z ≤
      4 * ‖gradient φ z‖ ^ 2 := by
  have hp : 0 < φ z ^ 2 + ε := by positivity
  rw [coulombGaussianFisherDensity, coulombGaussianRegularizedSquare_fderiv hφ,
    coulombGaussianRegularizedSquare, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    TauCeti.norm_gradient_eq_norm_fderiv]
  apply (div_le_iff₀ hp).mpr
  nlinarith [mul_nonneg hε.le (sq_nonneg ‖fderiv ℝ φ z‖)]

/-- Removal of ε from an already proved positive Fisher bound. The premise
is intentionally visible: this theorem alone is not the sharp Gaussian LSI. -/
theorem coulombGaussian_core_lsi_of_positive_fisher {β : ℝ} (hβ : 0 < β)
    (hpositive : ∀ (g : ℂ → ℝ), ContDiff ℝ 1 g → ∀ (M D m : ℝ),
      (∀ z, ‖g z‖ ≤ M) → (∀ z, ‖fderiv ℝ g z‖ ≤ D) →
      0 < m → (∀ z, m ≤ g z) →
      entropy (coulombCenterGaussian β) g ≤
        (((1 / (2 * β)) * ∫ z, coulombGaussianFisherDensity g z
          ∂coulombCenterGaussian β : ℝ) : EReal))
    (φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) :
    entropy (coulombCenterGaussian β) (fun z => φ z ^ 2) ≤
      (((2 / β) * ∫ z, ‖gradient (φ : ℂ → ℝ) z‖ ^ 2 ∂coulombCenterGaussian β : ℝ) : EReal) := by
  letI := coulombCenterGaussian_isProbability hβ
  obtain ⟨B, hB, hb⟩ := coulombGaussian_test_c1_bound φ
  have hφd := φ.contDiff.differentiable (by simp)
  have hφ2 : Integrable (fun z => φ z ^ 2) (coulombCenterGaussian β) := by
    apply (integrable_const (B ^ 2)).mono' (φ.continuous.pow 2).aestronglyMeasurable
    filter_upwards [] with z
    simpa only [Pi.pow_apply, norm_pow] using pow_le_pow_left₀ (norm_nonneg _) (hb z).1 2
  have hE : Integrable (fun z => ‖gradient (φ : ℂ → ℝ) z‖ ^ 2) (coulombCenterGaussian β) := by
    have hc : Continuous (gradient (φ : ℂ → ℝ)) :=
      (φ.contDiff.gradient_right (m := 0) (by simp)).continuous
    apply (integrable_const (B ^ 2)).mono' (hc.norm.pow 2).aestronglyMeasurable
    filter_upwards [] with z
    dsimp only [Pi.pow_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), TauCeti.norm_gradient_eq_norm_fderiv]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb z).2 2
  have heps {ε : ℝ} (hε : 0 < ε) :
      entropy (coulombCenterGaussian β) (coulombGaussianRegularizedSquare (φ : ℂ → ℝ) ε) ≤
        (((2 / β) * ∫ z, ‖gradient (φ : ℂ → ℝ) z‖ ^ 2
          ∂coulombCenterGaussian β : ℝ) : EReal) := by
    let g := coulombGaussianRegularizedSquare (φ : ℂ → ℝ) ε
    have hg : ContDiff ℝ 1 g := ((φ.contDiff.pow 2).add contDiff_const).of_le (by simp)
    have hgm (z : ℂ) : ε ≤ g z := by
      dsimp only [g, coulombGaussianRegularizedSquare]
      nlinarith [sq_nonneg (φ z)]
    have hpos (z : ℂ) : 0 < g z := hε.trans_le (hgm z)
    have hM (z : ℂ) : ‖g z‖ ≤ B ^ 2 + ε := by
      rw [Real.norm_eq_abs, abs_of_pos (hpos z)]
      have h := pow_le_pow_left₀ (norm_nonneg _) (hb z).1 2
      rw [Real.norm_eq_abs, sq_abs] at h
      dsimp only [g, coulombGaussianRegularizedSquare]
      linarith
    have hD (z : ℂ) : ‖fderiv ℝ g z‖ ≤ 2 * B ^ 2 := by
      rw [show g = coulombGaussianRegularizedSquare (φ : ℂ → ℝ) ε from rfl,
        coulombGaussianRegularizedSquare_fderiv hφd, norm_smul, norm_mul,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        _ ≤ (2 * B) * B := by gcongr; exacts [(hb z).1, (hb z).2]
        _ = _ := by ring
    have hqcont := coulombGaussianFisherDensity_continuous hg hpos
    have hqi : Integrable (coulombGaussianFisherDensity g) (coulombCenterGaussian β) := by
      apply (hE.const_mul 4).mono' hqcont.aestronglyMeasurable
      filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (coulombGaussianFisherDensity_nonneg hpos z)]
      exact coulombGaussianRegularizedSquare_fisher_le hφd hε z
    have hqbound := integral_mono hqi (hE.const_mul 4)
      (fun z => coulombGaussianRegularizedSquare_fisher_le hφd hε z)
    rw [integral_const_mul] at hqbound
    have hbnd := mul_le_mul_of_nonneg_left hqbound (show 0 ≤ 1 / (2 * β) by positivity)
    have hreal : (1 / (2 * β)) * (∫ z, coulombGaussianFisherDensity g z ∂coulombCenterGaussian β) ≤
        (2 / β) * (∫ z, ‖gradient (φ : ℂ → ℝ) z‖ ^ 2 ∂coulombCenterGaussian β) := by
      convert hbnd using 1 <;> ring
    exact (hpositive g hg (B ^ 2 + ε) (2 * B ^ 2) ε hM hD hε hgm).trans
      (EReal.coe_le_coe_iff.mpr hreal)
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  apply entropy_le_of_ae_tendsto
    (F := fun n => coulombGaussianRegularizedSquare (φ : ℂ → ℝ) (ε n))
    (b := fun _ => (2 / β) * ∫ z, ‖gradient (φ : ℂ → ℝ) z‖ ^ 2 ∂coulombCenterGaussian β)
  · intro n
    exact ((φ.continuous.pow 2).add continuous_const).measurable.aemeasurable
  · filter_upwards [] with z
    simpa only [coulombGaussianRegularizedSquare, add_zero] using
      tendsto_const_nhds.add hεlim
  · have hmass (n : ℕ) :
        (∫ z, coulombGaussianRegularizedSquare (φ : ℂ → ℝ) (ε n) z ∂coulombCenterGaussian β) =
          (∫ z, φ z ^ 2 ∂coulombCenterGaussian β) + ε n := by
      change (∫ z, φ z ^ 2 + ε n ∂coulombCenterGaussian β) = _
      rw [integral_add hφ2 (integrable_const _)]
      simp
    simp_rw [hmass]
    simpa only [add_zero] using tendsto_const_nhds.add hεlim
  · exact tendsto_const_nhds
  · exact fun n => heps (hε n)

end RepulsiveCoulomb
