import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! Additive original-paper calculus. Genuine real trace, actual
right-isometry chain rule, and compact-C2 IBP. No distributional identity or
Dirac conclusion is an input. No project import is needed. -/
noncomputable section
open MeasureTheory InnerProductSpace Set
open scoped ContDiff BigOperators
namespace RepulsiveCoulomb.PaperRoute.CollisionCalculus

section Calculus
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem laplacian_comp_linearIsometryEquiv (e : E ≃ₗᵢ[ℝ] F)
    {f : F → ℝ} (hf : ContDiff ℝ 2 f) :
    Laplacian.laplacian (f ∘ e) = (Laplacian.laplacian f) ∘ e := by
  let b := stdOrthonormalBasis ℝ E
  funext x
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ e) b,
    laplacian_eq_iteratedFDeriv_orthonormalBasis f (b.map e)]
  change (∑ i, iteratedFDeriv ℝ 2 (f ∘ e) x ![b i,b i]) =
    ∑ i, iteratedFDeriv ℝ 2 f (e x) ![e (b i),e (b i)]
  have hchain := e.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right hf x
    (i := 2) (by norm_num)
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv] at hchain
  apply Finset.sum_congr rfl
  intro i hi
  rw [hchain]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  ext j
  fin_cases j <;> rfl

omit [FiniteDimensional ℝ E] in
theorem second_fderiv_apply_eq_iterated {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w =
      iteratedFDeriv ℝ 2 f x ![w,v] := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num) x) (differentiableAt_const v)]
  simp [iteratedFDeriv_two_apply]

theorem laplacian_eq_second_fderiv_basis {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    Laplacian.laplacian f = fun x =>
      ∑ i, fderiv ℝ (fun y => fderiv ℝ f y (b i)) x (b i) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f b]
  funext x
  apply Finset.sum_congr rfl
  intro i hi
  exact (second_fderiv_apply_eq_iterated hf x (b i) (b i)).symm

omit [FiniteDimensional ℝ E] in
theorem continuous_second_fderiv_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (v w : E) : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ f y v) x w) := by
  have hd : ContDiff ℝ 1 (fun y => fderiv ℝ f y v) :=
    (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  exact (hd.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem continuous_laplacian {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (Laplacian.laplacian f) := by
  rw [laplacian_eq_second_fderiv_basis hf (stdOrthonormalBasis ℝ E)]
  exact continuous_finsetSum _ (fun i _ => continuous_second_fderiv_apply hf _ _)

theorem hasCompactSupport_laplacian {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) : HasCompactSupport (Laplacian.laplacian f) := by
  rw [laplacian_eq_second_fderiv_basis hf (stdOrthonormalBasis ℝ E)]
  have he : (fun x => ∑ i, fderiv ℝ (fun y => fderiv ℝ f y ((stdOrthonormalBasis ℝ E) i))
      x ((stdOrthonormalBasis ℝ E) i)) =
      ∑ i, (fun x => fderiv ℝ (fun y => fderiv ℝ f y ((stdOrthonormalBasis ℝ E) i))
        x ((stdOrthonormalBasis ℝ E) i)) := by
    funext x
    rw [Finset.sum_apply]
  rw [he]
  exact HasCompactSupport.finset_sum (fun i _ =>
    (hfc.fderiv_apply ℝ ((stdOrthonormalBasis ℝ E) i)).fderiv_apply ℝ ((stdOrthonormalBasis ℝ E) i))

end Calculus

section Integration
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] in
theorem integrable_second_fderiv_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (v w : E) :
    Integrable (fun x => fderiv ℝ (fun y => fderiv ℝ f y v) x w) μ :=
  (continuous_second_fderiv_apply hf v w).integrable_of_hasCompactSupport
    ((hfc.fderiv_apply ℝ v).fderiv_apply ℝ w)

theorem integral_second_fderiv_eq_zero {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (v w : E) :
    (∫ x, fderiv ℝ (fun y => fderiv ℝ f y v) x w ∂μ) = 0 := by
  let g : E → ℝ := fun x => fderiv ℝ f x v
  have hg : ContDiff ℝ 1 g := (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hgi : Integrable g μ := hg.continuous.integrable_of_hasCompactSupport (hfc.fderiv_apply ℝ v)
  have hDgi := integrable_second_fderiv_apply (μ := μ) hf hfc v w
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun _ : E => (1 : ℝ)) (g := g) (v := w)
    (by simp only [fderiv_const_apply, zero_apply, zero_mul]; exact integrable_zero E ℝ μ)
    (by simpa only [one_mul] using hDgi)
    (by simpa only [one_mul] using hgi)
    (fun _ _ => differentiableAt_const _)
    (fun x _ => hg.differentiable (by norm_num) x)
  simpa only [one_mul, fderiv_const_apply, zero_apply,
    zero_mul, integral_zero, neg_zero, g] using h

theorem integrable_laplacian {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) : Integrable (Laplacian.laplacian f) μ :=
  (continuous_laplacian hf).integrable_of_hasCompactSupport (hasCompactSupport_laplacian hf hfc)

theorem integral_laplacian_eq_zero {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) : (∫ x, Laplacian.laplacian f x ∂μ) = 0 := by
  let b := stdOrthonormalBasis ℝ E
  rw [laplacian_eq_second_fderiv_basis hf b,
    integral_finsetSum Finset.univ (fun i _ => integrable_second_fderiv_apply hf hfc (b i) (b i))]
  simp only [integral_second_fderiv_eq_zero hf hfc, Finset.sum_const_zero]

/-- Two compact-support integrations by parts, without any decay assumption. -/
theorem integral_mul_second_fderiv_eq {f φ : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (v : E) :
    (∫ x, f x*fderiv ℝ (fun y => fderiv ℝ φ y v) x v ∂μ) =
      ∫ x, fderiv ℝ (fun y => fderiv ℝ f y v) x v*φ x ∂μ := by
  have hdf : ContDiff ℝ 1 (fun x => fderiv ℝ f x v) :=
    (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hdφ : ContDiff ℝ 1 (fun x => fderiv ℝ φ x v) :=
    (hφ.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hc1 := hφc.fderiv_apply ℝ v
  have hc2 := hc1.fderiv_apply ℝ v
  have hi1 := (hdf.continuous.mul hdφ.continuous).integrable_of_hasCompactSupport (μ := μ) hc1.mul_left
  have hi2 := (hf.continuous.mul (continuous_second_fderiv_apply hφ v v)).integrable_of_hasCompactSupport (μ := μ) hc2.mul_left
  have hi3 := (hf.continuous.mul hdφ.continuous).integrable_of_hasCompactSupport (μ := μ) hc1.mul_left
  have hi4 := ((continuous_second_fderiv_apply hf v v).mul hφ.continuous).integrable_of_hasCompactSupport (μ := μ) hφc.mul_left
  have hi5 := (hdf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport (μ := μ) hφc.mul_left
  have hfirst := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi1 hi2 hi3
    (fun x _ => hf.differentiable (by norm_num) x)
    (fun x _ => hdφ.differentiable (by norm_num) x)
  have hsecond := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi4 hi1 hi5
    (fun x _ => hdf.differentiable (by norm_num) x)
    (fun x _ => hφ.differentiable (by norm_num) x)
  rw [hfirst, hsecond, neg_neg]

end Integration
end RepulsiveCoulomb.PaperRoute.CollisionCalculus
