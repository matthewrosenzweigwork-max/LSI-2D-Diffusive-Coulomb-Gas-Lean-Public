module

public import LeanResearch.RepulsiveCoulomb.PlanarWeightedGaussian
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-! Literal full labeled N-particle repulsive Coulomb model, canonical manuscript
thm:main. The configuration norm is the Euclidean l2 norm, not the Pi sup norm.
Finite-positive normalization, full collision-form realization and functional
inequalities for this law are subsequent obligations, not model fields. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology BigOperators ENNReal
namespace RepulsiveCoulomb

abbrev CoulombConfig (N : ℕ) := EuclideanSpace ℂ (Fin N)

def coulombPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun p => p.1 < p.2)

theorem mem_coulombPairs {N : ℕ} (p : Fin N × Fin N) : p ∈ coulombPairs N ↔ p.1 < p.2 := by
  simp [coulombPairs]

def coulombCoordinate {N : ℕ} (i : Fin N) : CoulombConfig N →L[ℝ] ℂ :=
  (EuclideanSpace.proj i).restrictScalars ℝ

theorem coulombCoordinate_apply {N : ℕ} (i : Fin N) (z : CoulombConfig N) :
    coulombCoordinate i z = z i := rfl

def coulombVandermonde {N : ℕ} (z : CoulombConfig N) : ℂ :=
  ∏ p ∈ coulombPairs N, (z p.1 - z p.2)

theorem coulombVandermonde_continuous (N : ℕ) : Continuous (coulombVandermonde (N := N)) := by
  unfold coulombVandermonde
  exact continuous_finset_prod _ (fun p _ => (coulombCoordinate p.1).continuous.sub (coulombCoordinate p.2).continuous)

theorem coulombVandermonde_ne_zero_iff {N : ℕ} (z : CoulombConfig N) :
    coulombVandermonde z ≠ 0 ↔ ∀ i j : Fin N, i ≠ j → z i ≠ z j := by
  rw [coulombVandermonde, Finset.prod_ne_zero_iff]
  constructor
  · intro h i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact sub_ne_zero.mp (h (i, j) ((mem_coulombPairs _).mpr hlt))
    · exact (sub_ne_zero.mp (h (j, i) ((mem_coulombPairs _).mpr hgt))).symm
  · intro h p hp
    exact sub_ne_zero.mpr (h p.1 p.2 (ne_of_lt ((mem_coulombPairs _).mp hp)))

def coulombDomain (N : ℕ) : Opens (CoulombConfig N) :=
  ⟨{z | coulombVandermonde z ≠ 0}, (isClosed_eq (coulombVandermonde_continuous N) continuous_const).isOpen_compl⟩

def coulombWeight {N : ℕ} (β : ℝ) (z : CoulombConfig N) : ℝ :=
  Real.exp (-β * ‖z‖ ^ 2 / 2) *
    ∏ p ∈ coulombPairs N, ‖z p.1 - z p.2‖ ^ (β / (N : ℝ))

theorem coulombWeight_nonneg {N : ℕ} (β : ℝ) (z : CoulombConfig N) : 0 ≤ coulombWeight β z := by
  unfold coulombWeight
  exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun p _ => Real.rpow_nonneg (norm_nonneg _) _))

theorem coulombWeight_continuous {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) : Continuous (coulombWeight (N := N) β) := by
  unfold coulombWeight
  apply Continuous.mul
  · fun_prop
  · apply continuous_finset_prod
    intro p hp
    exact (Real.continuous_rpow_const (div_nonneg hβ (Nat.cast_nonneg N))).comp
      (((coulombCoordinate p.1).continuous.sub (coulombCoordinate p.2).continuous).norm)

theorem coulombWeight_pos_off_collisions {N : ℕ} (β : ℝ) (z : CoulombConfig N)
    (hz : z ∈ coulombDomain N) : 0 < coulombWeight β z := by
  have hne := (coulombVandermonde_ne_zero_iff z).mp hz
  unfold coulombWeight
  apply mul_pos (Real.exp_pos _)
  apply Finset.prod_pos
  intro p hp
  exact Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr
    (hne p.1 p.2 (ne_of_lt ((mem_coulombPairs _).mp hp))))) _

theorem coulombWeight_zero_at_collision {N : ℕ} {β : ℝ} (hN : 0 < N) (hβ : 0 < β)
    (z : CoulombConfig N) {i j : Fin N} (hij : i ≠ j) (hz : z i = z j) :
    coulombWeight β z = 0 := by
  have hexp : 0 < β / (N : ℝ) := div_pos hβ (by exact_mod_cast hN)
  have hfactor (p : Fin N × Fin N) (hp : p ∈ coulombPairs N) (h : z p.1 = z p.2) :
      (∏ q ∈ coulombPairs N, ‖z q.1 - z q.2‖ ^ (β / (N : ℝ))) = 0 :=
    Finset.prod_eq_zero hp (by rw [h, sub_self, norm_zero, Real.zero_rpow hexp.ne'])
  unfold coulombWeight
  rcases lt_or_gt_of_ne hij with hl | hl
  · rw [hfactor (i, j) ((mem_coulombPairs _).mpr hl) hz, mul_zero]
  · rw [hfactor (j, i) ((mem_coulombPairs _).mpr hl) hz.symm, mul_zero]

def coulombPartition (N : ℕ) (β : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : CoulombConfig N, ENNReal.ofReal (coulombWeight β z)

def coulombMeasure (N : ℕ) (β : ℝ) : Measure (CoulombConfig N) :=
  (coulombPartition N β)⁻¹ • volume.withDensity (fun z => ENNReal.ofReal (coulombWeight β z))

end RepulsiveCoulomb
