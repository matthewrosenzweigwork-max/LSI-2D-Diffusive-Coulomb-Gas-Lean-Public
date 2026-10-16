import LeanResearch.RepulsiveCoulomb.PaperRoute.OriginalGaussianWeightedRoute
import LeanResearch.RepulsiveCoulomb.PointDilationBranchNamedLabelTransport

/-! Additive original-paper relative-coordinate route. Constants are selected
only by the new original-input weighted theorem. The historically named
transport helpers have a free coefficient and do not select old witnesses.
Actual declaration dependencies, not ancestor import names, are audited. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace RepulsiveCoulomb.PaperRoute

def paperCrel (β : ℝ) : ℝ := paperCwt β (2 * β)

def paperCrelInterval (a b : ℝ) : ℝ := paperCwt 1 (2 * b) / a

theorem paperCrel_pos {β : ℝ} (hβ : 0 < β) : 0 < paperCrel β :=
  paperCwt_pos hβ (2 * β)

theorem paperCrelInterval_eq (a b : ℝ) :
    paperCrelInterval a b = paperCwt a (2 * b) := by
  simp only [paperCrelInterval, paperCwt, div_one]

theorem paperCrelInterval_pos {a b : ℝ} (ha : 0 < a) :
    0 < paperCrelInterval a b := by
  rw [paperCrelInterval_eq]
  exact paperCwt_pos ha (2 * b)

theorem paper_relative_full {β : ℝ} (hβ : 0 < β)
    (N : ℕ) (p : ℂ × CoulombConfig N)
    (u : PointFormDomain hβ (coulombRelativeExponents_nonneg N hβ.le) (coulombRelativeRoots p.1 p.2)) :
    variance (pointFormValueL hβ (coulombRelativeExponents_nonneg N hβ.le)
      (coulombRelativeRoots p.1 p.2) u : ℂ → ℝ) (coulombRelativeKernel N β hβ p) ≤
      paperCrel β * pointFormEnergy hβ (coulombRelativeExponents_nonneg N hβ.le)
        (coulombRelativeRoots p.1 p.2) u := by
  have h := (paper_weighted_named_inequalities (2 * β) hβ (N + N + 1)
    (coulombRelativeExponents N β) (coulombRelativeExponents_nonneg N hβ.le)
    (coulombRelativeRoots p.1 p.2) (coulombRelative_exponent_sum_lt N hβ).le u).1
  simpa only [coulombRelativeKernel_apply, paperCrel] using h

theorem paper_relative_full_interval {a b β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hlo : a ≤ β) (hhi : β ≤ b)
    (N : ℕ) (p : ℂ × CoulombConfig N)
    (u : PointFormDomain hβ (coulombRelativeExponents_nonneg N hβ.le) (coulombRelativeRoots p.1 p.2)) :
    variance (pointFormValueL hβ (coulombRelativeExponents_nonneg N hβ.le)
      (coulombRelativeRoots p.1 p.2) u : ℂ → ℝ) (coulombRelativeKernel N β hβ p) ≤
      paperCrelInterval a b * pointFormEnergy hβ (coulombRelativeExponents_nonneg N hβ.le)
        (coulombRelativeRoots p.1 p.2) u := by
  have hQ : ∑ j, coulombRelativeExponents N β j ≤ 2 * b :=
    (coulombRelative_exponent_sum_lt N hβ).le.trans (mul_le_mul_of_nonneg_left hhi (by norm_num))
  have h := (paper_weighted_named_full_above (2 * b) ha hβ hlo (N + N + 1)
    (coulombRelativeExponents N β) (coulombRelativeExponents_nonneg N hβ.le)
    (coulombRelativeRoots p.1 p.2) hQ u).1
  simpa only [coulombRelativeKernel_apply, paperCrelInterval_eq] using h

theorem paper_relative_core {β : ℝ} (hβ : 0 < β) :
    ∀ (N : ℕ) (c : ℂ) (y : CoulombConfig N)
      (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤),
      variance (fun w : ℂ => φ (coulombRelativeInsert c w y)) (coulombRelativeKernel N β hβ (c, y)) ≤
        (paperCrel β / 2) * (∫ w, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c w y) 0 -
          gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c w y) (Fin.succ 0)‖ ^ 2
          ∂coulombRelativeKernel N β hβ (c, y)) :=
  pointDilationBranch_relative_core_of_full hβ (paper_relative_full hβ)

theorem paper_relative_core_interval {a b β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hlo : a ≤ β) (hhi : β ≤ b) :
    ∀ (N : ℕ) (c : ℂ) (y : CoulombConfig N)
      (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤),
      variance (fun w : ℂ => φ (coulombRelativeInsert c w y)) (coulombRelativeKernel N β hβ (c, y)) ≤
        (paperCrelInterval a b / 2) *
          (∫ w, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c w y) 0 -
            gradient (φ : CoulombConfig (N + 2) → ℝ) (coulombRelativeInsert c w y) (Fin.succ 0)‖ ^ 2
            ∂coulombRelativeKernel N β hβ (c, y)) :=
  pointDilationBranch_relative_core_of_full hβ
    (paper_relative_full_interval ha hβ hlo hhi)

/-- The paper's literal 1/(2N) random-transposition inequality on Gibbs L2. -/
theorem paper_random_transposition_gap (N : ℕ) (hN : 2 ≤ N) {β : ℝ}
    (hβ : 0 < β) (v : Lp ℝ 2 (coulombMeasure N β)) :
    ‖v - coulombSymmetrizer N hβ v‖ ^ 2 ≤
      (1 / (2 * (N : ℝ))) *
        ∑ p ∈ coulombPairs N, ‖v - coulombValuePermuteL N hβ (Equiv.swap p.1 p.2) v‖ ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hp : (0 : ℝ) < 2 * N := by positivity
  have ht := coulombValue_transposition_gap N hN hβ v
  calc
    _ ≤ (∑ p ∈ coulombPairs N,
        ‖v - coulombValuePermuteL N hβ (Equiv.swap p.1 p.2) v‖ ^ 2) / (2 * (N : ℝ)) :=
      (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using ht)
    _ = _ := by ring

/-- Actual all-pair transposition bound with the new relative coefficient.
The pair-gradient map is grad_i - grad_j, hence 2 Crel here is exactly
4 Crel times the squared normalized relative gradient. -/
theorem paper_relative_form_swap {β : ℝ} (hβ : 0 < β) :
    ∀ (N : ℕ) (i j : Fin (N + 2)), i ≠ j →
      ∀ u : CoulombFormDomain (N + 2) hβ,
      ‖coulombFormSwapDifferenceL (N + 2) hβ i j u‖ ^ 2 ≤
        (2 * paperCrel β) * ‖coulombFormPairGradientL (N + 2) hβ i j u‖ ^ 2 :=
  pointDilationBranch_form_swap_of_core hβ
    (pointDilationBranch_all_pairs_swap_of_first hβ
      (pointDilationBranch_first_swap_of_relative hβ
        (pointDilationBranch_relative_swap_of_core hβ (paper_relative_core hβ))))

/-- Normalized relative-coordinate derivative, with its literal Euclidean factor. -/
def paperRelativeGradient {N : ℕ} (g : CoulombConfig N) (i j : Fin N) : ℂ :=
  (Real.sqrt 2)⁻¹ • (g i - g j)

theorem paperRelativeGradient_norm_sq {N : ℕ} (g : CoulombConfig N) (i j : Fin N) :
    ‖paperRelativeGradient g i j‖ ^ 2 = (1 / 2 : ℝ) * ‖g i - g j‖ ^ 2 := by
  rw [paperRelativeGradient, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg 2)), mul_pow, inv_pow,
    Real.sq_sqrt (by norm_num)]
  norm_num

/-- The manuscript's factor-four transposition estimate in physical coordinates. -/
theorem paper_transposition_core {β : ℝ} (hβ : 0 < β) (N : ℕ)
    (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤)
    (i j : Fin (N + 2)) (hij : i ≠ j) :
    (∫ z, (φ z - φ (coulombPermute (Equiv.swap i j) z)) ^ 2
      ∂coulombMeasure (N + 2) β) ≤
      (4 * paperCrel β) * (∫ z,
        ‖paperRelativeGradient (gradient (φ : CoulombConfig (N + 2) → ℝ) z) i j‖ ^ 2
          ∂coulombMeasure (N + 2) β) := by
  have h := paper_relative_form_swap hβ N i j hij (coulombFormCore hβ φ)
  rw [coulombFormSwapDifferenceL_core_norm, coulombFormPairGradientL_core_norm] at h
  simp_rw [paperRelativeGradient_norm_sq]
  rw [integral_const_mul]
  convert h using 1
  ring

/-- Exact complete-graph identity and the N/2 bound for relative gradients. -/
theorem paper_complete_graph_relative_gradient {N : ℕ} (g : CoulombConfig N) :
    (∑ p ∈ coulombPairs N, ‖paperRelativeGradient g p.1 p.2‖ ^ 2) =
      (1 / 2 : ℝ) * ∑ p ∈ coulombPairs N, ‖g p.1 - g p.2‖ ^ 2 ∧
    (∑ p ∈ coulombPairs N, ‖paperRelativeGradient g p.1 p.2‖ ^ 2) ≤
      ((N : ℝ) / 2) * ‖g‖ ^ 2 := by
  constructor
  · simp only [paperRelativeGradient_norm_sq, ← Finset.mul_sum]
  · simp only [paperRelativeGradient_norm_sq, ← Finset.mul_sum]
    have h := mul_le_mul_of_nonneg_left (coulomb_pair_norm_sq_sum_le g)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    convert h using 1
    ring

/-- The exact random-transposition and complete-graph factors cancel N. -/
theorem paper_label_fluctuation {β : ℝ} (hβ : 0 < β) :
    ∀ (N : ℕ) (u : CoulombFormDomain (N + 2) hβ),
      ‖coulombFormValueL (N + 2) hβ u -
        coulombSymmetrizer (N + 2) hβ (coulombFormValueL (N + 2) hβ u)‖ ^ 2 ≤
          paperCrel β * coulombFormEnergy (N + 2) hβ u :=
  pointDilationBranch_label_of_form_swap hβ (paperCrel_pos hβ)
    (paper_relative_form_swap hβ)

theorem paper_label_fluctuation_interval {a b β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hlo : a ≤ β) (hhi : β ≤ b) :
    ∀ (N : ℕ) (u : CoulombFormDomain (N + 2) hβ),
      ‖coulombFormValueL (N + 2) hβ u -
        coulombSymmetrizer (N + 2) hβ (coulombFormValueL (N + 2) hβ u)‖ ^ 2 ≤
          paperCrelInterval a b * coulombFormEnergy (N + 2) hβ u :=
  pointDilationBranch_label_of_relative_core hβ (paperCrelInterval_pos ha)
    (paper_relative_core_interval ha hβ hlo hhi)

theorem paper_variance_reduction {β : ℝ} (hβ : 0 < β) :
    ∀ (N : ℕ) (u : CoulombFormDomain (N + 2) hβ),
      variance (coulombFormValueL (N + 2) hβ u : CoulombConfig (N + 2) → ℝ)
        (coulombMeasure (N + 2) β) ≤
      variance (coulombFormValueL (N + 2) hβ (coulombFormSymmetrizer (N + 2) hβ u) :
        CoulombConfig (N + 2) → ℝ) (coulombMeasure (N + 2) β) +
        paperCrel β * coulombFormEnergy (N + 2) hβ u :=
  pointDilationBranch_variance_reduction_of_label hβ (paper_label_fluctuation hβ)

theorem paper_variance_reduction_interval {a b β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hlo : a ≤ β) (hhi : β ≤ b) :
    ∀ (N : ℕ) (u : CoulombFormDomain (N + 2) hβ),
      variance (coulombFormValueL (N + 2) hβ u : CoulombConfig (N + 2) → ℝ)
        (coulombMeasure (N + 2) β) ≤
      variance (coulombFormValueL (N + 2) hβ (coulombFormSymmetrizer (N + 2) hβ u) :
        CoulombConfig (N + 2) → ℝ) (coulombMeasure (N + 2) β) +
        paperCrelInterval a b * coulombFormEnergy (N + 2) hβ u :=
  pointDilationBranch_variance_reduction_of_label hβ
    (paper_label_fluctuation_interval ha hβ hlo hhi)

end RepulsiveCoulomb.PaperRoute
