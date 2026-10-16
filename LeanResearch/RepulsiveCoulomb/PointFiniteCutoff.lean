module

public import LeanResearch.RepulsiveCoulomb.PointCutoffApproximation
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-! Finite products of smooth point-avoidance cutoffs. Only positive exponents
participate; repeated point locations are permitted. -/
noncomputable section
open MeasureTheory Set Filter TopologicalSpace Metric
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def positivePointIndices {m : ℕ} (a : Fin m → ℝ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun j ↦ 0 < a j)

@[simp] theorem mem_positivePointIndices {m : ℕ} (a : Fin m → ℝ) (j : Fin m) :
    j ∈ positivePointIndices a ↔ 0 < a j := by
  classical
  simp [positivePointIndices]

def pointAvoidanceCutoff {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (ε : ℝ) (hε : 0 < ε) (z : ℂ) : ℝ :=
  ∏ j ∈ positivePointIndices a, (1 - pointCutoffBump (y j) ε hε z)

theorem pointAvoidanceCutoff_nonneg {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (ε : ℝ) (hε : 0 < ε) (z : ℂ) : 0 ≤ pointAvoidanceCutoff a y ε hε z := by
  apply Finset.prod_nonneg
  intro j _
  exact sub_nonneg.mpr (pointCutoffBump (y j) ε hε).le_one

theorem pointAvoidanceCutoff_le_one {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (ε : ℝ) (hε : 0 < ε) (z : ℂ) : pointAvoidanceCutoff a y ε hε z ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro j _
    exact sub_nonneg.mpr (pointCutoffBump (y j) ε hε).le_one
  · intro j _
    linarith [(pointCutoffBump (y j) ε hε).nonneg (x := z)]

theorem pointAvoidanceCutoff_contDiff {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ (↑(⊤ : ℕ∞)) (pointAvoidanceCutoff a y ε hε) := by
  have hb : ∀ j : Fin m, ContDiff ℝ (↑(⊤ : ℕ∞)) (pointCutoffBump (y j) ε hε) :=
    fun j ↦ pointCutoffBump_contDiff (y j) ε hε
  unfold pointAvoidanceCutoff
  fun_prop

theorem pointAvoidanceCutoff_zero_near {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (ε : ℝ) (hε : 0 < ε) (j : Fin m) (hj : 0 < a j) {z : ℂ}
    (hz : z ∈ closedBall (y j) ε) : pointAvoidanceCutoff a y ε hε z = 0 := by
  apply Finset.prod_eq_zero ((mem_positivePointIndices a j).mpr hj)
  rw [pointCutoffBump_one (y j) ε hε hz, sub_self]

theorem pointAvoidanceCutoff_tendsto_one {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    {ι : Type*} {l : Filter ι} (ε : ι → ℝ) (hε : ∀ t, 0 < ε t)
    (hlim : Tendsto ε l (𝓝 0)) {z : ℂ} (hz : z ∉ pointPunctures a y) :
    Tendsto (fun t ↦ pointAvoidanceCutoff a y (ε t) (hε t) z) l (𝓝 1) := by
  have h : ∀ j ∈ positivePointIndices a,
      Tendsto (fun t ↦ 1 - pointCutoffBump (y j) (ε t) (hε t) z) l (𝓝 1) := by
    intro j hj
    have hne : z ≠ y j := fun he ↦ hz ⟨j, (mem_positivePointIndices a j).mp hj, he⟩
    simpa using tendsto_const_nhds.sub (pointCutoff_tendsto_zero_off_center (y j) z hne ε hε hlim)
  simpa [pointAvoidanceCutoff] using tendsto_finsetProd (positivePointIndices a) h

theorem pointAvoidanceCutoff_tsupport_subset {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (ε : ℝ) (hε : 0 < ε) (φ : ℂ → ℝ) :
    tsupport (fun z ↦ φ z * pointAvoidanceCutoff a y ε hε z) ⊆ pointDomain a y := by
  intro z hz
  change z ∉ pointPunctures a y
  rintro ⟨j, hj, rfl⟩
  have hsub : Function.support (fun z ↦ φ z * pointAvoidanceCutoff a y ε hε z) ⊆
      (ball (y j) ε)ᶜ := by
    intro w hw hball
    apply hw
    dsimp only
    rw [pointAvoidanceCutoff_zero_near a y ε hε j hj (ball_subset_closedBall hball), mul_zero]
  have ht := closure_minimal hsub isOpen_ball.isClosed_compl
  have hnot := ht hz
  exact hnot (mem_ball_self hε)

/-- Multiplication by the finite cutoff gives a genuine puncture-avoiding core test function. -/
def pointAvoidanceTestFunction {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (ε : ℝ) (hε : 0 < ε) (φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) :
    TestFunction (pointDomain a y) ℝ ⊤ :=
  ⟨fun z ↦ φ z * pointAvoidanceCutoff a y ε hε z,
    φ.contDiff.mul (pointAvoidanceCutoff_contDiff a y ε hε),
    φ.hasCompactSupport.mul_right,
    pointAvoidanceCutoff_tsupport_subset a y ε hε φ⟩

theorem pointAvoidanceCutoff_gradient_bound {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    ‖gradient (pointAvoidanceCutoff a y ε hε) z‖ ≤
      ∑ j ∈ positivePointIndices a, ‖gradient (pointCutoffBump (y j) ε hε) z‖ := by
  classical
  have hd (j : Fin m) : DifferentiableAt ℝ (pointCutoffBump (y j) ε hε) z :=
    ((pointCutoffBump_contDiff (y j) ε hε).differentiable (by simp)) z
  rw [TauCeti.norm_gradient_eq_norm_fderiv]
  unfold pointAvoidanceCutoff
  rw [fderiv_finsetProd (fun j _ ↦ (hd j).const_sub 1)]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [norm_smul, fderiv_const_sub 1, norm_neg, TauCeti.norm_gradient_eq_norm_fderiv]
  have hp0 : 0 ≤ ∏ k ∈ (positivePointIndices a).erase j, (1 - pointCutoffBump (y k) ε hε z) :=
    Finset.prod_nonneg fun k _ ↦ sub_nonneg.mpr (pointCutoffBump (y k) ε hε).le_one
  have hp1 : (∏ k ∈ (positivePointIndices a).erase j, (1 - pointCutoffBump (y k) ε hε z)) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro k _
      exact sub_nonneg.mpr (pointCutoffBump (y k) ε hε).le_one
    · intro k _
      linarith [(pointCutoffBump (y k) ε hε).nonneg (x := z)]
  rw [Real.norm_eq_abs, abs_of_nonneg hp0]
  exact mul_le_of_le_one_left (norm_nonneg _) hp1

theorem pointAvoidanceCutoff_gradient_sq_bound {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    ‖gradient (pointAvoidanceCutoff a y ε hε) z‖ ^ 2 ≤
      (positivePointIndices a).card *
        ∑ j ∈ positivePointIndices a, ‖gradient (pointCutoffBump (y j) ε hε) z‖ ^ 2 :=
  (pow_le_pow_left₀ (norm_nonneg _) (pointAvoidanceCutoff_gradient_bound a y ε hε z) 2).trans
    sq_sum_le_card_mul_sum_sq

theorem pointAvoidanceCutoff_energy_integrable {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun z ↦ ‖gradient (pointAvoidanceCutoff a y ε hε) z‖ ^ 2)
      (pointMeasure γ a y) := by
  have hi := (integrable_finsetSum (positivePointIndices a)
    (fun j _ ↦ pointCutoff_energy_integrable hγ ha y (y j) ε hε)).const_mul
      ((positivePointIndices a).card : ℝ)
  apply hi.mono'
  · exact (((pointAvoidanceCutoff_contDiff a y ε hε).gradient_right (m := (⊤ : ℕ∞)) (by simp)).continuous.norm.pow 2).aestronglyMeasurable
  · exact Eventually.of_forall fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pointAvoidanceCutoff_gradient_sq_bound a y ε hε z

theorem pointAvoidanceCutoff_energy_le_sum {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    (∫ z, ‖gradient (pointAvoidanceCutoff a y ε hε) z‖ ^ 2 ∂pointMeasure γ a y) ≤
      (positivePointIndices a).card * ∑ j ∈ positivePointIndices a,
        ∫ z, ‖gradient (pointCutoffBump (y j) ε hε) z‖ ^ 2 ∂pointMeasure γ a y := by
  have hi := integrable_finsetSum (positivePointIndices a)
    (fun j _ ↦ pointCutoff_energy_integrable hγ ha y (y j) ε hε)
  have h := integral_mono (pointAvoidanceCutoff_energy_integrable hγ ha y ε hε)
    (hi.const_mul ((positivePointIndices a).card : ℝ)) (pointAvoidanceCutoff_gradient_sq_bound a y ε hε)
  simpa only [integral_const_mul, integral_finsetSum _
    (fun j _ ↦ pointCutoff_energy_integrable hγ ha y (y j) ε hε)] using h

theorem pointAvoidanceCutoff_energy_tendsto_zero {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {ι : Type*} {l : Filter ι} (ε : ι → ℝ) (hε : ∀ t, 0 < ε t)
    (hlim : Tendsto ε l (𝓝 0)) :
    Tendsto (fun t ↦ ∫ z, ‖gradient (pointAvoidanceCutoff a y (ε t) (hε t)) z‖ ^ 2
      ∂pointMeasure γ a y) l (𝓝 0) := by
  have hsum := tendsto_finsetSum (positivePointIndices a) (fun j hj ↦
    pointCutoff_energy_tendsto_zero hγ ha y j ((mem_positivePointIndices a j).mp hj) ε hε hlim)
  apply squeeze_zero (fun t ↦ integral_nonneg fun z ↦ sq_nonneg _)
    (fun t ↦ pointAvoidanceCutoff_energy_le_sum hγ ha y (ε t) (hε t))
  simpa using hsum.const_mul ((positivePointIndices a).card : ℝ)

end RepulsiveCoulomb
