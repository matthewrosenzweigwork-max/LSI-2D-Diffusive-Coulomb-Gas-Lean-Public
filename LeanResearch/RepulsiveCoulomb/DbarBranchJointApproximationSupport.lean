module

public import LeanResearch.RepulsiveCoulomb.DbarBranchJointCoreApproximation
public import LeanResearch.RepulsiveCoulomb.DbarBranchCompactMargin

@[expose] public section

/-! One actual joint mollifier sequence with a prescribed common support
margin. This support information permits the fixed-compact Gibbs transfer
and exact identification with the original local coefficients. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace Metric
open scoped Topology BigOperators Pointwise
namespace RepulsiveCoulomb

theorem dbarSystemCoreOutput_tsupport_subset {N : ℕ} {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (B : κ → ι → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (v : δ → CoulombConfig N)
    (φ : ι → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    {L : Set (CoulombConfig N)} (hL : IsClosed L)
    (hφ : ∀ b, tsupport (φ b : CoulombConfig N → ℂ) ⊆ L) (a : κ) :
    tsupport (dbarSystemCoreOutput A B v φ a : CoulombConfig N → ℂ) ⊆ L := by
  apply closure_minimal _ hL
  intro z hz
  by_contra hzL
  have hzφ (b : ι) : z ∉ tsupport (φ b : CoulombConfig N → ℂ) := fun h => hzL (hφ b h)
  have hval (b : ι) : φ b z = 0 := image_eq_zero_of_notMem_tsupport (hzφ b)
  have hder (b : ι) : fderiv ℝ (φ b : CoulombConfig N → ℂ) z = 0 :=
    fderiv_of_notMem_tsupport ℝ (hzφ b)
  apply hz
  change dbarSystemCoreOutput A B v φ a z = 0
  simp only [dbarSystemCoreOutput, _root_.add_apply, _root_.sum_apply]
  change (∑ b, ∑ d, A a b d z * dbarVolumeCoreDerivative (v d) (φ b) z) +
    (∑ b, B a b z * φ b z) = 0
  simp only [dbarVolumeCoreDerivative_apply, hval, hder, ContinuousLinearMap.zero_apply,
    mul_zero, Finset.sum_const_zero, add_zero]

theorem dbarSystem_joint_approximation_with_support {N : ℕ} {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (B : κ → ι → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (v : δ → CoulombConfig N)
    (f : ι → CoulombConfig N → ℂ) (hf : ∀ b, MemLp (f b) 2 volume)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hfs : ∀ b, Function.support (f b) ⊆ K)
    (g : κ → Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (hweak : DbarVolumeWeakSystem A B v (fun b => (hf b).toLp (f b)) g)
    (hg : ∀ a, Integrable (g a : CoulombConfig N → ℂ) volume)
    {r : ℝ} (hr : 0 < r) :
    ∃ φ : ℕ → ι → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤,
      (∀ n b, tsupport (φ n b : CoulombConfig N → ℂ) ⊆ closedBall 0 r + K) ∧
      (∀ n a, tsupport (dbarSystemCoreOutput A B v (φ n) a : CoulombConfig N → ℂ) ⊆
        closedBall 0 r + K) ∧
      Tendsto (fun n => ((fun b => dbarVolumeCoreValue (φ n b)),
        (fun a => dbarVolumeCoreValue (dbarSystemCoreOutput A B v (φ n) a))))
        atTop (𝓝 ((fun b => (hf b).toLp (f b)), g)) := by
  have hfc (b : ι) : HasCompactSupport (f b) :=
    hK.of_isClosed_subset isClosed_closure (closure_minimal (hfs b) hK.isClosed)
  let ψ : ContDiffBump (0 : CoulombConfig N) := default
  have hψ : 0 < ψ.rOut := ψ.rIn_pos.trans ψ.rIn_lt_rOut
  let c : ℝ := r / (ψ.rOut + 1)
  have hc : 0 < c := div_pos hr (by linarith)
  let ε : ℕ → ℝ := fun n => c * (1 / ((n : ℝ) + 1))
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul c
  have hsmall (n : ℕ) : (dbarScaledBump ψ (hε n)).rOut ≤ r := by
    have hn : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr
      (le_add_of_nonneg_left (Nat.cast_nonneg n))
    change (c * (1 / ((n : ℝ) + 1))) * ψ.rOut ≤ r
    calc
      _ ≤ c * ψ.rOut := mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right hc.le hn) hψ.le
      _ ≤ c * (ψ.rOut + 1) := mul_le_mul_of_nonneg_left (by linarith) hc.le
      _ = r := div_mul_cancel₀ r (ne_of_gt (by linarith))
  let φ : ℕ → ι → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤ :=
    fun n b => dbarCompactInputMollifyTest (hf b) (hfc b) (dbarScaledBump ψ (hε n))
  have hs (n : ℕ) (b : ι) : tsupport (φ n b : CoulombConfig N → ℂ) ⊆ closedBall 0 r + K :=
    (dbarCompactInputMollifyTest_support (hf b) (hfc b) (dbarScaledBump ψ (hε n)) hK (hfs b)).trans
      (add_subset_add (closedBall_subset_closedBall (hsmall n)) Subset.rfl)
  refine ⟨φ, hs, ?_, ?_⟩
  · intro n a
    exact dbarSystemCoreOutput_tsupport_subset A B v (φ n)
      ((isCompact_closedBall _ _).add hK).isClosed (hs n) a
  · have h := dbarSystem_joint_mollification_tendsto A B v
      (fun b => (hf b).toLp (f b)) g hweak hg ψ ε hε hε0
    simpa only [φ, dbarCompactInputMollifyTest_value, dbarSystemCoreOutput_mollifier_value] using h

def coulombRestrictGlobalCore {N : ℕ}
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (hφ : tsupport (φ : CoulombConfig N → ℂ) ⊆ coulombDomain N) :
    TestFunction (coulombDomain N) ℂ ⊤ :=
  ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩

end RepulsiveCoulomb
