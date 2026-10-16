import LeanResearch.RepulsiveCoulomb.HilbertTranspositionGap
import LeanResearch.RepulsiveCoulomb.CoulombPairGradientSum
import Mathlib.GroupTheory.Perm.Support

/-! Additive original-paper adapter. The finite transition matrix is the actual
uniform ordered-pair transposition walk. It is related to the proved finite
regular representation gap, retaining the literal paper normalization. -/
noncomputable section
open InnerProductSpace
open scoped BigOperators
namespace RepulsiveCoulomb.PaperRoute

abbrev PaperPermutationSpace (N : ℕ) := EuclideanSpace ℝ (Equiv.Perm (Fin N))

def paperTranspositionKernel (N : ℕ) (σ τ : Equiv.Perm (Fin N)) : ℝ :=
  ((N : ℝ) ^ 2)⁻¹ * ∑ i : Fin N, ∑ j : Fin N,
    if σ * Equiv.swap i j = τ then 1 else 0

def paperTranspositionAverage (N : ℕ) (f : Equiv.Perm (Fin N) → ℝ)
    (σ : Equiv.Perm (Fin N)) : ℝ :=
  ((N : ℝ) ^ 2)⁻¹ * ∑ i : Fin N, ∑ j : Fin N, f (σ * Equiv.swap i j)

def paperTranspositionOperator (N : ℕ) : PaperPermutationSpace N →L[ℝ] PaperPermutationSpace N :=
  1 - (2 / (N : ℝ) ^ 2) • transpositionLaplacian finiteRightRepresentation

theorem paperTranspositionKernel_nonneg (N : ℕ) (σ τ : Equiv.Perm (Fin N)) :
    0 ≤ paperTranspositionKernel N σ τ := by
  unfold paperTranspositionKernel
  positivity

theorem paperTranspositionKernel_row_sum {N : ℕ} (hN : 0 < N)
    (σ : Equiv.Perm (Fin N)) : ∑ τ, paperTranspositionKernel N σ τ = 1 := by
  have hnr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [paperTranspositionKernel, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Equiv.Perm (Fin N))))]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [← pow_two, inv_mul_cancel₀ (pow_ne_zero _ hnr)]

theorem paperTranspositionKernel_symmetric (N : ℕ) (σ τ : Equiv.Perm (Fin N)) :
    paperTranspositionKernel N σ τ = paperTranspositionKernel N τ σ := by
  have hself (i j : Fin N) : Equiv.swap i j * Equiv.swap i j = 1 := by
    ext k
    exact congrArg Fin.val (Equiv.swap_apply_self i j k)
  have he (i j : Fin N) : σ * Equiv.swap i j = τ ↔ τ * Equiv.swap i j = σ := by
    constructor <;> intro h
    · have hh := congrArg (fun p : Equiv.Perm (Fin N) => p * Equiv.swap i j) h
      simpa only [mul_assoc, hself, mul_one] using hh.symm
    · have hh := congrArg (fun p : Equiv.Perm (Fin N) => p * Equiv.swap i j) h
      simpa only [mul_assoc, hself, mul_one] using hh.symm
  simp only [paperTranspositionKernel, he]

theorem paperTranspositionKernel_expectation (N : ℕ)
    (f : Equiv.Perm (Fin N) → ℝ) (σ : Equiv.Perm (Fin N)) :
    (∑ τ, paperTranspositionKernel N σ τ * f τ) = paperTranspositionAverage N f σ := by
  simp only [paperTranspositionKernel, paperTranspositionAverage, mul_assoc, ← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  simp

theorem paperTranspositionKernel_identity {N : ℕ} (hN : 0 < N)
    (σ : Equiv.Perm (Fin N)) : paperTranspositionKernel N σ σ = 1 / (N : ℝ) := by
  have hnr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he (i j : Fin N) : σ * Equiv.swap i j = σ ↔ i = j := by
    rw [mul_eq_left]
    exact Equiv.swap_eq_refl_iff
  simp only [paperTranspositionKernel, he]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp [hnr]

theorem paper_swap_eq_swap_iff {N : ℕ} (i j a b : Fin N) (hab : a ≠ b) :
    Equiv.swap i j = Equiv.swap a b ↔
      (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
  constructor
  · intro he
    have hij : i ≠ j := by
      intro hij
      subst j
      have hz : Equiv.swap a b = Equiv.refl _ := by simpa only [Equiv.swap_self] using he.symm
      exact hab (Equiv.swap_eq_refl_iff.mp hz)
    have hs := congrArg Equiv.Perm.support he
    rw [Equiv.Perm.support_swap hij, Equiv.Perm.support_swap hab] at hs
    have hp : ({i,j} : Set (Fin N)) = {a,b} := by
      simpa only [Finset.coe_pair] using congrArg (fun s : Finset (Fin N) => (s : Set (Fin N))) hs
    exact Set.pair_eq_pair_iff.mp hp
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Equiv.swap_comm _ _

theorem paperTranspositionKernel_swap {N : ℕ} (σ : Equiv.Perm (Fin N))
    (a b : Fin N) (hab : a ≠ b) :
    paperTranspositionKernel N σ (σ * Equiv.swap a b) = 2 / (N : ℝ) ^ 2 := by
  have he (i j : Fin N) :
      (if σ * Equiv.swap i j = σ * Equiv.swap a b then (1 : ℝ) else 0) =
      (if i = a then if j = b then 1 else 0 else 0) +
      (if i = b then if j = a then 1 else 0 else 0) := by
    simp only [mul_left_cancel_iff, paper_swap_eq_swap_iff i j a b hab]
    by_cases hia : i = a <;> by_cases hib : i = b <;>
      by_cases hja : j = a <;> by_cases hjb : j = b <;> simp_all
  simp only [paperTranspositionKernel, he, Finset.sum_add_distrib]
  simp
  ring

/-- The operator acts by the literal transition kernel, not a renamed gap witness. -/
theorem paperTranspositionOperator_apply {N : ℕ} (hN : 0 < N)
    (f : PaperPermutationSpace N) (σ : Equiv.Perm (Fin N)) :
    paperTranspositionOperator N f σ = paperTranspositionAverage N f σ := by
  have hnr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs := symmetric_pair_sum_twice
    (fun i j : Fin N => f σ - f (σ * Equiv.swap i j))
    (fun i j => by rw [Equiv.swap_comm i j]) (fun i => by simp only [Equiv.swap_self]; change f σ - f (σ * 1) = 0; rw [mul_one, sub_self])
  have hp : transpositionLaplacian finiteRightRepresentation f σ =
      ∑ p ∈ coulombPairs N, (f σ - f (σ * Equiv.swap p.1 p.2)) := by
    simp only [transpositionLaplacian_apply, unitaryDifference_apply,
      WithLp.ofLp_sum, Finset.sum_apply, PiLp.sub_apply, finiteRightRepresentation_apply]
    rw [← ordered_pair_edge_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [edgeTransposition_pair p.1 p.2 (ne_of_lt (Finset.mem_filter.mp hp).2)]
  simp only [paperTranspositionOperator, sub_apply,
    one_apply_eq_self, smul_apply,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hp, paperTranspositionAverage]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hs ⊢
  field_simp
  nlinarith only [hs]

theorem paperTranspositionOperator_kernel {N : ℕ} (hN : 0 < N)
    (f : PaperPermutationSpace N) (σ : Equiv.Perm (Fin N)) :
    paperTranspositionOperator N f σ = ∑ τ, paperTranspositionKernel N σ τ * f τ :=
  (paperTranspositionOperator_apply hN f σ).trans
    (paperTranspositionKernel_expectation N f σ).symm

theorem paperTranspositionOperator_selfAdjoint (N : ℕ)
    (f g : PaperPermutationSpace N) :
    inner ℝ (paperTranspositionOperator N f) g =
      inner ℝ f (paperTranspositionOperator N g) := by
  simp only [paperTranspositionOperator, sub_apply,
    one_apply_eq_self, smul_apply,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [transpositionLaplacian_selfAdjoint finiteRightRepresentation finiteRightRepresentation_inner]

/-- The Dirichlet form is I-P, with the usual uniform-law scalar normalization optional. -/
def paperTranspositionEnergy (N : ℕ) (f : PaperPermutationSpace N) : ℝ :=
  inner ℝ f (f - paperTranspositionOperator N f)

theorem paperTranspositionEnergy_eq_laplacian (N : ℕ) (f : PaperPermutationSpace N) :
    paperTranspositionEnergy N f =
      (2 / (N : ℝ) ^ 2) * inner ℝ f (transpositionLaplacian finiteRightRepresentation f) := by
  simp only [paperTranspositionEnergy, paperTranspositionOperator,
    sub_apply, one_apply_eq_self,
    smul_apply, sub_sub_cancel, real_inner_smul_right]

theorem paperTranspositionEnergy_pairs (N : ℕ) (f : PaperPermutationSpace N) :
    paperTranspositionEnergy N f = ((N : ℝ) ^ 2)⁻¹ *
      ∑ p ∈ coulombPairs N, ‖f - finiteRightRepresentation (Equiv.swap p.1 p.2) f‖ ^ 2 := by
  rw [paperTranspositionEnergy_eq_laplacian, transpositionLaplacian_apply, inner_sum]
  have he : (2 : ℝ) * ∑ s ∈ (Finset.univ : Finset (Fin N)).powersetCard 2,
      inner ℝ f (unitaryDifference finiteRightRepresentation (edgeTransposition s) f) =
      ∑ p ∈ coulombPairs N, ‖f - finiteRightRepresentation (Equiv.swap p.1 p.2) f‖ ^ 2 := by
    rw [Finset.mul_sum]
    simp_rw [unitaryDifference_energy (finiteRightRepresentation (G := Equiv.Perm (Fin N)))
      finiteRightRepresentation_inner,
      unitaryDifference_apply]
    rw [← ordered_pair_edge_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [edgeTransposition_pair p.1 p.2 (ne_of_lt (Finset.mem_filter.mp hp).2)]
  rw [← he]
  ring

theorem paperTransposition_gap_lower {N : ℕ} (hN : 2 ≤ N)
    (f : PaperPermutationSpace N) :
    (2 / (N : ℝ)) * ‖f - finiteUnitaryAverage finiteRightRepresentation f‖ ^ 2 ≤
      paperTranspositionEnergy N f := by
  have hp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h := mul_le_mul_of_nonneg_left
    (finite_transposition_gap hN finiteRightRepresentation finiteRightRepresentation_inner f)
    (by positivity : 0 ≤ 2 / (N : ℝ) ^ 2)
  rw [paperTranspositionEnergy_eq_laplacian]
  convert h using 1
  field_simp

/-- Elementary coordinate action needed to exhibit the sharp second eigenvalue. -/
theorem paper_sum_swap_coordinate {N : ℕ} (g : Fin N → ℝ) (k : Fin N) :
    (∑ i : Fin N, ∑ j : Fin N, g (Equiv.swap i j k)) =
      ((N : ℝ) ^ 2 - 2 * N) * g k + 2 * ∑ i, g i := by
  have he (i j : Fin N) : g (Equiv.swap i j k) = g k +
      (if i = k then g j - g k else 0) + (if j = k then g i - g k else 0) := by
    by_cases hi : i = k <;> by_cases hj : j = k
    · subst i; subst j; simp
    · subst i; simp [hj, Equiv.swap_apply_left]
    · subst j; simp [hi, Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (Ne.symm hj)]
      simp [hi, hj]
  simp_rw [he, Finset.sum_add_distrib]
  simp [Finset.sum_sub_distrib]
  ring

def paperTranspositionEigenfunction {N : ℕ} (a b : Fin N) : PaperPermutationSpace N :=
  WithLp.toLp 2 (fun σ => (if σ a = a then (1 : ℝ) else 0) - (if σ a = b then 1 else 0))

theorem paperTranspositionEigenfunction_eigen {N : ℕ} (hN : 0 < N)
    (a b : Fin N) :
    paperTranspositionOperator N (paperTranspositionEigenfunction a b) =
      (1 - 2 / (N : ℝ)) • paperTranspositionEigenfunction a b := by
  have hnr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  ext σ
  rw [paperTranspositionOperator_apply hN]
  let g : Fin N → ℝ := fun k => (if σ k = a then 1 else 0) - (if σ k = b then 1 else 0)
  have hg : ∑ k, g k = 0 := by
    have he := Fintype.sum_equiv σ
      (fun k => (if σ k = a then (1 : ℝ) else 0) - (if σ k = b then 1 else 0))
      (fun k => (if k = a then (1 : ℝ) else 0) - (if k = b then 1 else 0)) (fun _ => rfl)
    simpa only [g, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, sub_self] using he
  change ((N : ℝ) ^ 2)⁻¹ * (∑ i, ∑ j, g (Equiv.swap i j a)) =
    (1 - 2 / (N : ℝ)) * g a
  rw [paper_sum_swap_coordinate, hg, mul_zero, add_zero]
  field_simp

theorem paperTranspositionEigenfunction_mean_zero {N : ℕ}
    (a b : Fin N) (hab : a ≠ b) :
    finiteUniformMean (paperTranspositionEigenfunction a b) = 0 := by
  let f := paperTranspositionEigenfunction a b
  have he (σ : Equiv.Perm (Fin N)) : f (Equiv.swap a b * σ) = -f σ := by
    change (if Equiv.swap a b (σ a) = a then (1 : ℝ) else 0) -
      (if Equiv.swap a b (σ a) = b then 1 else 0) =
      -((if σ a = a then (1 : ℝ) else 0) - (if σ a = b then 1 else 0))
    by_cases ha : σ a = a <;> by_cases hb : σ a = b <;>
      simp_all [Equiv.swap_apply_def, Ne.symm hab]
  have hs := Fintype.sum_equiv (Equiv.mulLeft (Equiv.swap a b))
    (fun σ => f (Equiv.swap a b * σ)) f (fun _ => rfl)
  simp_rw [he, Finset.sum_neg_distrib] at hs
  have hz : ∑ σ, f σ = 0 := by linarith
  change (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ * (∑ σ, f σ) = 0
  rw [hz, mul_zero]

theorem paperTranspositionEigenfunction_nonzero {N : ℕ}
    (a b : Fin N) (hab : a ≠ b) : paperTranspositionEigenfunction a b ≠ 0 := by
  intro hz
  have h := congrArg (fun f : PaperPermutationSpace N => f 1) hz
  simp [paperTranspositionEigenfunction, hab] at h

/-- The normalized gap is exactly 2/N: the lower bound is attained by a nonconstant eigenfunction. -/
theorem paperTransposition_gap_attained {N : ℕ} (hN : 2 ≤ N) :
    ∃ f : PaperPermutationSpace N, f ≠ 0 ∧
      finiteUnitaryAverage finiteRightRepresentation f = 0 ∧
      paperTranspositionOperator N f = (1 - 2 / (N : ℝ)) • f ∧
      paperTranspositionEnergy N f = (2 / (N : ℝ)) * ‖f‖ ^ 2 := by
  let a : Fin N := ⟨0, by omega⟩
  let b : Fin N := ⟨1, by omega⟩
  have hab : a ≠ b := by intro h; have hh := congrArg Fin.val h; norm_num [a,b] at hh
  let f := paperTranspositionEigenfunction a b
  have he := paperTranspositionEigenfunction_eigen (by omega : 0 < N) a b
  have hm : finiteUnitaryAverage finiteRightRepresentation f = 0 := by
    ext σ
    rw [finiteRightRepresentation_average, paperTranspositionEigenfunction_mean_zero a b hab]
    rfl
  refine ⟨f, paperTranspositionEigenfunction_nonzero a b hab, hm, he, ?_⟩
  rw [paperTranspositionEnergy, he, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  ring

def paperTranspositionGapBounds (N : ℕ) : Set ℝ :=
  {c | ∀ f : PaperPermutationSpace N,
    c * ‖f - finiteUnitaryAverage finiteRightRepresentation f‖ ^ 2 ≤
      paperTranspositionEnergy N f}

theorem paperTransposition_gap_exact {N : ℕ} (hN : 2 ≤ N) :
    IsGreatest (paperTranspositionGapBounds N) (2 / (N : ℝ)) := by
  refine ⟨paperTransposition_gap_lower hN, ?_⟩
  intro c hc
  obtain ⟨f, hf, hm, _he, hE⟩ := paperTransposition_gap_attained hN
  have h := hc f
  rw [hm, sub_zero, hE] at h
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (norm_pos_iff.mpr hf))).mp h

/-- The actual transition-matrix quadratic form, expressed under the uniform law. -/
def paperUniformTranspositionEnergy (N : ℕ) (f : PaperPermutationSpace N) : ℝ :=
  finiteUniformMean (fun σ => f σ * (f σ - ∑ τ, paperTranspositionKernel N σ τ * f τ))

def paperUniformTranspositionVariance (N : ℕ) (f : PaperPermutationSpace N) : ℝ :=
  finiteUniformMean (fun σ => (f σ - finiteUniformMean f) ^ 2)

theorem paperUniformTranspositionEnergy_eq {N : ℕ} (hN : 0 < N)
    (f : PaperPermutationSpace N) :
    paperUniformTranspositionEnergy N f =
      (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ * paperTranspositionEnergy N f := by
  simp only [paperUniformTranspositionEnergy, finiteUniformMean, paperTranspositionEnergy,
    PiLp.inner_apply, PiLp.sub_apply, RCLike.inner_apply, conj_trivial,
    paperTranspositionOperator_kernel hN, mul_comm]

theorem paperUniformTranspositionVariance_eq (N : ℕ) (f : PaperPermutationSpace N) :
    paperUniformTranspositionVariance N f =
      (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ‖f - finiteUnitaryAverage finiteRightRepresentation f‖ ^ 2 := by
  rw [finiteRightRepresentation_error_norm]
  rfl

def paperUniformTranspositionGapBounds (N : ℕ) : Set ℝ :=
  {c | ∀ f : PaperPermutationSpace N,
    c * paperUniformTranspositionVariance N f ≤ paperUniformTranspositionEnergy N f}

/-- The exact gap is now a statement about the actual normalized finite kernel
and its uniform stationary law, rather than only an auxiliary Laplacian. -/
theorem paperUniformTransposition_gap_exact {N : ℕ} (hN : 2 ≤ N) :
    IsGreatest (paperUniformTranspositionGapBounds N) (2 / (N : ℝ)) := by
  have hcard : 0 < (Fintype.card (Equiv.Perm (Fin N)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hs : paperUniformTranspositionGapBounds N = paperTranspositionGapBounds N := by
    ext c
    simp only [paperUniformTranspositionGapBounds, paperTranspositionGapBounds,
      Set.mem_ofPred_eq, paperUniformTranspositionVariance_eq,
      paperUniformTranspositionEnergy_eq (by omega : 0 < N)]
    constructor
    · intro h f
      exact (mul_le_mul_iff_right₀ (inv_pos.mpr hcard)).mp
        (by simpa only [mul_left_comm] using h f)
    · intro h f
      have hh := mul_le_mul_of_nonneg_left (h f) (inv_nonneg.mpr hcard.le)
      simpa only [mul_left_comm] using hh
  rw [hs]
  exact paperTransposition_gap_exact hN

end RepulsiveCoulomb.PaperRoute
