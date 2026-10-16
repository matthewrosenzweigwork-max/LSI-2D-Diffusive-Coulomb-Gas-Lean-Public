import LeanResearch.RepulsiveCoulomb.ScaledGridDoubleOscillation
import Mathlib.Data.Int.Interval

/-! Actual finite nodal samples of a compactly supported function, with exact
values at every lattice node. No finite-support sampling hypothesis is assumed. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem compact_grid_samples_finite {f : ℂ → ℝ} (hf : HasCompactSupport f)
    {h : ℝ} (hh : 0 < h) :
    (Function.support (fun p : ℤ × ℤ => f (h • complexLatticePoint p))).Finite := by
  classical
  obtain ⟨K,hK⟩ := hf.isCompact.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨N,hN⟩ := exists_nat_gt (K/h)
  have hKN : K < h * (N : ℝ) := by
    have h := (div_lt_iff₀ hh).mp hN
    nlinarith
  let s := (Finset.Icc (-(N : ℤ)) (N : ℤ)).product (Finset.Icc (-(N : ℤ)) (N : ℤ))
  apply s.finite_toSet.subset
  intro p hp
  have hz : h • complexLatticePoint p ∈ tsupport f := subset_tsupport f hp
  have hn : ‖h • complexLatticePoint p‖ ≤ K := by
    simpa only [mem_closedBall,dist_zero_right] using hK hz
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hh] at hn
  have hx0 := Complex.abs_re_le_norm (complexLatticePoint p)
  have hy0 := Complex.abs_im_le_norm (complexLatticePoint p)
  have hx : |(p.1 : ℝ)| < N := by
    change |(p.1 : ℝ)| ≤ ‖complexLatticePoint p‖ at hx0
    nlinarith [mul_le_mul_of_nonneg_left hx0 hh.le]
  have hy : |(p.2 : ℝ)| < N := by
    change |(p.2 : ℝ)| ≤ ‖complexLatticePoint p‖ at hy0
    nlinarith [mul_le_mul_of_nonneg_left hy0 hh.le]
  have hxlo : -(N : ℤ) < p.1 := by exact_mod_cast (abs_lt.mp hx).1
  have hxhi : p.1 < (N : ℤ) := by exact_mod_cast (abs_lt.mp hx).2
  have hylo : -(N : ℤ) < p.2 := by exact_mod_cast (abs_lt.mp hy).1
  have hyhi : p.2 < (N : ℤ) := by exact_mod_cast (abs_lt.mp hy).2
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hxlo.le,hxhi.le⟩,
    Finset.mem_Icc.mpr ⟨hylo.le,hyhi.le⟩⟩

def compactGridSamples (f : ℂ → ℝ) (hf : HasCompactSupport f) (h : ℝ) (hh : 0 < h) :
    (ℤ × ℤ) →₀ ℝ :=
  Finsupp.ofSupportFinite (fun p => f (h • complexLatticePoint p)) (compact_grid_samples_finite hf hh)

theorem compactGridSamples_apply (f : ℂ → ℝ) (hf : HasCompactSupport f)
    (h : ℝ) (hh : 0 < h) (p : ℤ × ℤ) :
    compactGridSamples f hf h hh p = f (h • complexLatticePoint p) := rfl

def sampledGridApproximation (f : ℂ → ℝ) (hf : HasCompactSupport f) (h : ℝ) (hh : 0 < h) : ℂ → ℝ :=
  scaledTriangularGridInterpolant h (compactGridSamples f hf h hh)

theorem sampledGridApproximation_nodal (f : ℂ → ℝ) (hf : HasCompactSupport f)
    (h : ℝ) (hh : 0 < h) (p : ℤ × ℤ) :
    sampledGridApproximation f hf h hh (h • complexLatticePoint p) = f (h • complexLatticePoint p) := by
  unfold sampledGridApproximation scaledTriangularGridInterpolant
  rw [smul_smul,inv_mul_cancel₀ hh.ne',one_smul,triangularGridInterpolant_nodal,compactGridSamples_apply]

end RepulsiveCoulomb
