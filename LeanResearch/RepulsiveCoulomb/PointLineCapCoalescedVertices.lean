import LeanResearch.RepulsiveCoulomb.PointLineCapNatGerms
import LeanResearch.RepulsiveCoulomb.PointLineCapActualFamily
import LeanResearch.RepulsiveCoulomb.PointLineCapAtomSupport
import LeanResearch.RepulsiveCoulomb.PointFiniteBoundaryCoalescence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order

/-! Uncompiled records-only successor. The actual positive line atoms and
positive cap vertices are bijectively identified. Coincident original source
locations coalesce once; zero-weight locations create no fictitious atom. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace RepulsiveCoulomb

def pointLinePositiveAtomLocations {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (c : ℝ → ℂ) : Finset ℂ := (positivePointLocations a y).filter (fun p => p ∈ range c)

theorem coalescedPointExponent_pos_iff_location
    {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (p : ℂ) :
    0 < coalescedPointExponent a y p ↔ p ∈ positivePointLocations a y := by
  constructor
  · intro hp
    by_contra hn
    rw [coalescedPointExponent_eq_zero_of_not_mem a y hn] at hp
    exact lt_irrefl _ hp
  · exact coalescedPointExponent_pos a y

/-- This is equality of finite sets of actual points, not a weak-limit or
source-index allocation. Every positive point is owned by one vertex. -/
theorem pointLineCap_positive_vertex_image
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {c : ℝ → ℂ} {R : ℝ} (D : LineCapGeometry c R)
    (hy : ∀ j, ‖y j‖ < R) (f : ℕ → ℝ → ℂ) (n : ℕ)
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (havoid : ∀ k ≤ n, ∀ t ∈ Ioo (0 : ℝ) 1, f k t ∉ pointPunctures a y)
    (hcarrier : (⋃ k ≤ n, f k '' Icc (0 : ℝ) 1) = D.boundary) :
    ((Finset.range (n + 1)).filter (fun k => f k 0 ∈ positivePointLocations a y)).image
      (fun k => f k 0) = pointLinePositiveAtomLocations a y c := by
  ext p
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, pointLinePositiveAtomLocations]
  constructor
  · rintro ⟨k, ⟨hk, hp⟩, rfl⟩
    obtain ⟨j, _, hj⟩ := (mem_positivePointLocations a y (f k 0)).mp hp
    have hpR : ‖f k 0‖ < R := by rw [← hj]; exact hy j
    have hpC : f k 0 ∈ D.boundary := by
      rw [← hcarrier]
      exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨by omega, ⟨0, by norm_num, rfl⟩⟩⟩
    exact ⟨hp, (lineCap_boundary_membership_inside_circle D.radius_pos D.disk_preimage hpR).mp hpC⟩
  · rintro ⟨hp, hline⟩
    obtain ⟨j, haj, hj⟩ := (mem_positivePointLocations a y p).mp hp
    have hpC : p ∈ D.boundary :=
      (lineCap_boundary_membership_inside_circle D.radius_pos D.disk_preimage (by rw [← hj]; exact hy j)).mpr hline
    obtain ⟨k, hk, hpk⟩ := active_location_on_finite_boundary_is_vertex ha y f n hv hclose havoid
      haj.ne' (by rw [hcarrier, hj]; exact hpC)
    have hpEq : f k 0 = p := hpk.symm.trans hj
    exact ⟨k, ⟨by omega, hpEq.symm ▸ hp⟩, hpEq⟩

/-- Arbitrary coefficients on actual positive atom LOCATIONS transport
exactly through the genuine vertex bijection. -/
theorem pointLineCap_positive_vertex_sum
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {c : ℝ → ℂ} {R : ℝ} (D : LineCapGeometry c R)
    (hy : ∀ j, ‖y j‖ < R) (f : ℕ → ℝ → ℂ) (n : ℕ)
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 → f i s = f j t → i = j ∧ s = t)
    (havoid : ∀ k ≤ n, ∀ t ∈ Ioo (0 : ℝ) 1, f k t ∉ pointPunctures a y)
    (hcarrier : (⋃ k ≤ n, f k '' Icc (0 : ℝ) 1) = D.boundary) (W : ℂ → ℝ) :
    (∑ k ∈ Finset.range (n + 1), if 0 < coalescedPointExponent a y (f k 0)
      then W (f k 0) else 0) = ∑ p ∈ pointLinePositiveAtomLocations a y c, W p := by
  simp_rw [coalescedPointExponent_pos_iff_location]
  rw [← Finset.sum_filter, ← pointLineCap_positive_vertex_image ha y D hy f n hv hclose havoid hcarrier]
  symm
  apply Finset.sum_image
  intro i hi j hj heq
  exact finite_halfOpen_simple_vertices_injective f n hinj i
    (by have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1; omega) j
    (by have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1; omega) heq

/-- A finite weight identity on actual coalesced locations. It applies to
interior curvature selectors and retains all original nonnegative exponents. -/
theorem pointCoalesced_location_weight_sum
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (W : ℂ → ℝ) :
    (∑ p ∈ positivePointLocations a y, coalescedPointExponent a y p * W p) =
      ∑ j, a j * W (y j) := by
  simp_rw [coalescedPointExponent_eq_sum_ite ha, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases haj : a j = 0
  · simp [haj]
  · have hj : y j ∈ positivePointLocations a y :=
      (mem_positivePointLocations a y (y j)).mpr ⟨j, lt_of_le_of_ne (ha j) (Ne.symm haj), rfl⟩
    simp only [ite_mul, zero_mul]
    simp [hj]

end RepulsiveCoulomb
