module

public import LeanResearch.RepulsiveCoulomb.PointFirstReturnFiniteGBData
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-! Source-only draft. Correct SIGNED finite curvature accounting after actual
mixed GB, and the independent old-boundary positive-mass comparison. Negative
old-boundary turns are preserved. These algebraic lemmas are not a no-return
certificate: the geometric endpoint/old-arc identifications must first be built. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace RepulsiveCoulomb

/-- The actual interior atomic curvature, retaining original labels so
coalesced locations automatically contribute the sum of their exponents. -/
def firstReturnInteriorCurvature {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (U : Set ℂ) : ℝ := ∑ j, if y j ∈ U then -Real.pi * a j else 0

/-- Interior curvature has its genuine nonpositive sign. -/
theorem firstReturnInteriorCurvature_nonpos {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (U : Set ℂ) :
    firstReturnInteriorCurvature a y U ≤ 0 := by
  apply Finset.sum_nonpos
  intro j _
  split_ifs
  · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (ha j)
  · exact le_rfl

/-- Rewrite the true mixed-GB result as interior curvature plus signed boundary
curvature equals 2*pi. No absolute values or positive parts are used here. -/
theorem PointFirstReturnFiniteGBData.signed_gauss_bonnet
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {arcs : ℕ → PointRadialC1PlaneArc ha y} {n : ℕ} {U V : Set ℂ}
    (D : PointFirstReturnFiniteGBData ha y arcs n U V) :
    firstReturnInteriorCurvature a y U +
      (∑ k ∈ Finset.range (n + 1), (Real.pi -
        (1 + coalescedPointExponent a y ((D.oriented k).curve 0) / 2) * D.angle k)) =
      2 * Real.pi := by
  have hmass : firstReturnInteriorCurvature a y U =
      -(2 * Real.pi * (∑ j, if y j ∈ U then a j / 2 else 0)) := by
    unfold firstReturnInteriorCurvature
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [hmass, D.gauss_bonnet]
  ring

/-- In particular genuine mixed GB forces at least 2*pi of signed corner
turn, since every interior atom is nonpositive. -/
theorem PointFirstReturnFiniteGBData.two_pi_le_corner_turn_sum
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {arcs : ℕ → PointRadialC1PlaneArc ha y} {n : ℕ} {U V : Set ℂ}
    (D : PointFirstReturnFiniteGBData ha y arcs n U V) :
    2 * Real.pi ≤ ∑ k ∈ Finset.range (n + 1), (Real.pi -
      (1 + coalescedPointExponent a y ((D.oriented k).curve 0) / 2) * D.angle k) := by
  linarith [D.signed_gauss_bonnet, firstReturnInteriorCurvature_nonpos ha y U]

/-- A simple actual old arc charges each old physical vertex at most once.
Its signed coefficient sum is bounded by the positive boundary mass away
from the omitted base point. Outside the finite support, nonpositive values
are sufficient. Thus negative old turns are neither discarded nor reversed
inside the exact GB identity. -/
theorem old_arc_signed_sum_le_positive_mass_away
    {ι X : Type*} [DecidableEq X] (s : Finset ι) (vertex : ι → X) (ν : X → ℝ)
    (support : Finset X) {base : X}
    (hinj : Set.InjOn vertex (s : Set ι))
    (hbase : ∀ i ∈ s, vertex i ≠ base)
    (hoff : ∀ i ∈ s, vertex i ∉ support → ν (vertex i) ≤ 0) :
    (∑ i ∈ s, ν (vertex i)) ≤ ∑ p ∈ support.erase base, max (ν p) 0 := by
  classical
  let t := s.filter (fun i => vertex i ∈ support)
  have hsub : t ⊆ s := Finset.filter_subset _ _
  have hdiscard : (∑ i ∈ s, ν (vertex i)) ≤ ∑ i ∈ t, ν (vertex i) := by
    apply Finset.sum_le_sum_of_subset_of_nonpos hsub
    intro i hi hit
    apply hoff i hi
    intro his
    exact hit (Finset.mem_filter.mpr ⟨hi, his⟩)
  apply hdiscard.trans
  apply Finset.sum_le_sum_of_injOn vertex
    (fun i hi j hj he => hinj (hsub hi) (hsub hj) he)
  · rintro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_erase.mpr ⟨hbase i (hsub hi), (Finset.mem_filter.mp hi).2⟩
  · intro i hi
    exact le_max_left _ _
  · intro p hp hnot
    exact le_max_right _ _

end RepulsiveCoulomb
