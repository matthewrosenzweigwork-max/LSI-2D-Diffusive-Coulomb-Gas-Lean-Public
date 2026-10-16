import LeanResearch.RepulsiveCoulomb.PointDilationBranchMeasure
import LeanResearch.RepulsiveCoulomb.PointWeightRegularity
import LeanResearch.RepulsiveCoulomb.RawPointGradientScaling
import Mathlib.Analysis.Distribution.TestFunction

/-! Dilation of the literal original puncture-avoiding smooth core, with the
exact physical-gradient factor. No form-domain equivalence is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace RepulsiveCoulomb

def pointDilationBranchLinear (h : ℝ) (hh : 0 < h) : ℂ ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 h hh.ne')

theorem pointDilationBranch_domain_smul {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    {h : ℝ} (hh : 0 < h) (z : ℂ) :
    h • z ∈ pointDomain a (fun j => h • y j) ↔ z ∈ pointDomain a y := by
  change ¬ (∃ j, 0 < a j ∧ h • z = h • y j) ↔ ¬ (∃ j, 0 < a j ∧ z = y j)
  simp only [smul_right_inj hh.ne']

theorem pointDilationBranch_domain_inv_smul {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    {h : ℝ} (hh : 0 < h) (z : ℂ) :
    h⁻¹ • z ∈ pointDomain a y ↔ z ∈ pointDomain a (fun j => h • y j) := by
  have H := pointDilationBranch_domain_smul a y hh (h⁻¹ • z)
  simpa only [smul_smul, mul_inv_cancel₀ hh.ne', one_smul] using H.symm

def pointDilationBranchCore {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (h : ℝ) (hh : 0 < h) (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    TestFunction (pointDomain a (fun j => h • y j)) ℝ ⊤ :=
  ⟨fun z => φ (h⁻¹ • z),
    φ.contDiff.comp (pointDilationBranchLinear h⁻¹ (inv_pos.mpr hh)).contDiff,
    φ.hasCompactSupport.comp_isClosedEmbedding
      (pointDilationBranchLinear h⁻¹ (inv_pos.mpr hh)).toHomeomorph.isClosedEmbedding,
    fun z hz => (pointDilationBranch_domain_inv_smul a y hh z).mp
      (φ.tsupport_subset (tsupport_comp_subset_preimage (φ : ℂ → ℝ)
        (continuous_const_smul h⁻¹) hz))⟩

theorem pointDilationBranchCore_apply {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (h : ℝ) (hh : 0 < h) (φ : TestFunction (pointDomain a y) ℝ ⊤) (z : ℂ) :
    pointDilationBranchCore a y h hh φ z = φ (h⁻¹ • z) := rfl

theorem pointDilationBranchCore_gradient {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (h : ℝ) (hh : 0 < h) (φ : TestFunction (pointDomain a y) ℝ ⊤) (z : ℂ) :
    gradient (pointDilationBranchCore a y h hh φ : ℂ → ℝ) z =
      h⁻¹ • gradient (φ : ℂ → ℝ) (h⁻¹ • z) :=
  complex_gradient_comp_smul (φ : ℂ → ℝ) h⁻¹ z

theorem pointDilationBranchCore_gradient_norm {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (h : ℝ) (hh : 0 < h) (φ : TestFunction (pointDomain a y) ℝ ⊤) (z : ℂ) :
    ‖gradient (pointDilationBranchCore a y h hh φ : ℂ → ℝ) z‖ =
      h⁻¹ * ‖gradient (φ : ℂ → ℝ) (h⁻¹ • z)‖ :=
  complex_gradient_comp_pos_smul_norm (φ : ℂ → ℝ) (inv_pos.mpr hh) z

end RepulsiveCoulomb
