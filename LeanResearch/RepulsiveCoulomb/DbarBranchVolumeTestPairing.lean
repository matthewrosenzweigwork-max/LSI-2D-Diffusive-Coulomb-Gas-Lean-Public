import LeanResearch.RepulsiveCoulomb.DbarBranchLpMollifier
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.MeasureTheory.Function.L2Space

/-! Genuine continuous test pairings for global Lebesgue L2, used to identify
Bochner L2 mollification with scalar convolution without evaluating L2 classes
at individual points. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace TopologicalSpace
open scoped Topology Distributions
namespace RepulsiveCoulomb

def coulombVolumeTestLp {N : ℕ} (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤) :
    Lp ℂ 2 (volume : Measure (CoulombConfig N)) :=
  ((Complex.continuous_ofReal.comp φ.continuous).memLp_of_hasCompactSupport
    (φ.hasCompactSupport.comp_left Complex.ofReal_zero)).toLp (fun z => (φ z : ℂ))

theorem coulombVolumeTestLp_coe {N : ℕ} (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤) :
    coulombVolumeTestLp φ =ᵐ[volume] fun z => (φ z : ℂ) := MemLp.coeFn_toLp _

def coulombVolumeTestPairingL {N : ℕ} (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤) :
    Lp ℂ 2 (volume : Measure (CoulombConfig N)) →L[ℝ] ℂ :=
  (innerSL ℂ (coulombVolumeTestLp φ)).restrictScalars ℝ

theorem coulombVolumeTestPairingL_apply {N : ℕ}
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤)
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    coulombVolumeTestPairingL φ f = ∫ z, φ z • f z := by
  change inner ℂ (coulombVolumeTestLp φ) f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coulombVolumeTestLp_coe φ] with z hz
  simp only [hz, RCLike.inner_apply', Complex.conj_ofReal, Complex.real_smul]

theorem coulombVolumeTestPairingL_translate {N : ℕ}
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤)
    (y : CoulombConfig N) (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    coulombVolumeTestPairingL φ (Measure.translateLp volume 2 y f) = ∫ z, φ z • f (z + y) := by
  rw [coulombVolumeTestPairingL_apply]
  apply integral_congr_ae
  filter_upwards [Measure.coeFn_translateLp (mu := volume) y f] with z hz
  rw [hz]
  rfl

end RepulsiveCoulomb
