module

public import LeanResearch.RepulsiveCoulomb.DbarBranchMetricCutoffL2
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

@[expose] public section

/-! Coordinate convergence recovers the genuine Euclidean-fiber L2 norm.
The finite product of component L2 spaces is used only for convergence;
no Hilbert structure is inferred on its ordinary maximum norm. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem dbarEuclideanLp_norm_sq {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {μ : Measure X} (f : Lp (EuclideanSpace ℂ ι) 2 μ) :
    ‖f‖ ^ 2 = ∑ i, ‖(EuclideanSpace.proj (𝕜 := ℂ) i).compLpL 2 μ f‖ ^ 2 := by
  have hi (i : ι) : Integrable (fun x => ‖f x i‖ ^ 2) μ :=
    ((Lp.memLp f).eval_piLp i).integrable_norm_pow (by norm_num)
  calc
    _ = ∫ x, ‖f x‖ ^ 2 ∂μ := dbarRealHilbertLp_norm_sq f
    _ = ∫ x, ∑ i, ‖f x i‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => EuclideanSpace.norm_sq_eq (f x)
    _ = ∑ i, ∫ x, ‖f x i‖ ^ 2 ∂μ := integral_finsetSum Finset.univ (fun i _ => hi i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [dbarRealHilbertLp_norm_sq]
      apply integral_congr_ae
      filter_upwards [(EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL (p := 2) (μ := μ) f] with x hx
      rw [hx]
      rfl

theorem dbarEuclideanLp_tendsto_of_coordinates {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {μ : Measure X} {f : ℕ → Lp (EuclideanSpace ℂ ι) 2 μ} {g : Lp (EuclideanSpace ℂ ι) 2 μ}
    (hf : ∀ i, Tendsto (fun n => (EuclideanSpace.proj (𝕜 := ℂ) i).compLpL 2 μ (f n)) atTop
      (𝓝 ((EuclideanSpace.proj (𝕜 := ℂ) i).compLpL 2 μ g))) : Tendsto f atTop (𝓝 g) := by
  have hi (i : ι) : Tendsto
      (fun n => ‖(EuclideanSpace.proj (𝕜 := ℂ) i).compLpL 2 μ (f n - g)‖ ^ 2) atTop (𝓝 0) := by
    have h := ((hf i).sub_const ((EuclideanSpace.proj (𝕜 := ℂ) i).compLpL 2 μ g)).norm.pow 2
    simpa only [map_sub, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using h
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hi i)
  have hsq : Tendsto (fun n => ‖f n - g‖ ^ 2) atTop (𝓝 0) := by
    simpa only [dbarEuclideanLp_norm_sq, Finset.sum_const_zero] using hsum
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

end RepulsiveCoulomb
