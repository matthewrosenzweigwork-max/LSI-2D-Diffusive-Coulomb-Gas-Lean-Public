module

public import LeanResearch.RepulsiveCoulomb.DbarBranchCompactInputMollifier
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! Actual compact smooth approximants for a finite combined first-order
system. The same sequence approximates the whole input and every prescribed
weak output, before localization back to the geometric weighted system. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

def dbarSystemCoreOutput {N : ℕ} {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (B : κ → ι → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (v : δ → CoulombConfig N)
    (φ : ι → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤) (a : κ) :
    TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤ :=
  (∑ b, ∑ d, dbarVolumeCoreProduct (A a b d) (dbarVolumeCoreDerivative (v d) (φ b))) +
    ∑ b, dbarVolumeCoreProduct (B a b) (φ b)

theorem dbarSystemCoreOutput_value {N : ℕ} {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (B : κ → ι → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (v : δ → CoulombConfig N)
    (φ : ι → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤) (a : κ) :
    dbarVolumeCoreValue (dbarSystemCoreOutput A B v φ a) =
      (∑ b, ∑ d, dbarVolumeMulL ((A a b d).memLp_top (μ := volume))
        (dbarVolumeCoreValue (dbarVolumeCoreDerivative (v d) (φ b)))) +
        ∑ b, dbarVolumeMulL ((B a b).memLp_top (μ := volume)) (dbarVolumeCoreValue (φ b)) := by
  change dbarVolumeCoreValueLinear N (_ + _) = _
  simp only [map_add, map_sum]
  change (∑ b, ∑ d, dbarVolumeCoreValue
    (dbarVolumeCoreProduct (A a b d) (dbarVolumeCoreDerivative (v d) (φ b)))) +
    (∑ b, dbarVolumeCoreValue (dbarVolumeCoreProduct (B a b) (φ b))) = _
  simp only [dbarVolumeCoreProduct_value]

theorem dbarSystemCoreOutput_mollifier_value {N : ℕ} {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (B : κ → ι → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (v : δ → CoulombConfig N)
    (f : ι → CoulombConfig N → ℂ) (hf : ∀ b, MemLp (f b) 2 volume)
    (hfc : ∀ b, HasCompactSupport (f b))
    (ψ : ContDiffBump (0 : CoulombConfig N)) (a : κ) :
    dbarVolumeCoreValue (dbarSystemCoreOutput A B v
      (fun b => dbarCompactInputMollifyTest (hf b) (hfc b) ψ) a) =
      dbarSystemMollifiedOutput A B v (fun b => (hf b).toLp (f b)) ψ a := by
  rw [dbarSystemCoreOutput_value]
  simp only [dbarCompactInputMollifyTest_value, dbarCompactInputMollifyTest_derivative_value]
  rfl

theorem dbarSystem_compact_core_joint_approximation {N : ℕ} {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (B : κ → ι → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (v : δ → CoulombConfig N)
    (f : ι → CoulombConfig N → ℂ) (hf : ∀ b, MemLp (f b) 2 volume)
    (hfc : ∀ b, HasCompactSupport (f b))
    (g : κ → Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (hweak : DbarVolumeWeakSystem A B v (fun b => (hf b).toLp (f b)) g)
    (hg : ∀ a, Integrable (g a : CoulombConfig N → ℂ) volume) :
    ∃ φ : ℕ → ι → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤,
      Tendsto (fun n => ((fun b => dbarVolumeCoreValue (φ n b)),
        (fun a => dbarVolumeCoreValue (dbarSystemCoreOutput A B v (φ n) a))))
        atTop (𝓝 ((fun b => (hf b).toLp (f b)), g)) := by
  let ψ : ContDiffBump (0 : CoulombConfig N) := default
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let φ : ℕ → ι → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤ :=
    fun n b => dbarCompactInputMollifyTest (hf b) (hfc b) (dbarScaledBump ψ (hε n))
  refine ⟨φ, ?_⟩
  have h := dbarSystem_joint_mollification_tendsto A B v
    (fun b => (hf b).toLp (f b)) g hweak hg ψ ε hε hε0
  simpa only [φ, dbarCompactInputMollifyTest_value, dbarSystemCoreOutput_mollifier_value] using h

end RepulsiveCoulomb
