import LeanResearch.RepulsiveCoulomb.CoulombCollisionCapacity

/-! Finite products avoiding all particle collisions, including their intersections. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace Metric
open scoped Topology BigOperators
namespace RepulsiveCoulomb

def coulombAvoidanceCutoff (N : ℕ) (ε : ℝ) (hε : 0 < ε) (z : CoulombConfig N) : ℝ :=
  ∏ p ∈ coulombPairs N, (1 - coulombCollisionBump p.1 p.2 ε hε z)

theorem coulombAvoidanceCutoff_nonneg (N : ℕ) (ε : ℝ) (hε : 0 < ε) (z : CoulombConfig N) :
    0 ≤ coulombAvoidanceCutoff N ε hε z :=
  Finset.prod_nonneg (fun p _ => sub_nonneg.mpr (coulombCollisionBump_le_one p.1 p.2 ε hε z))

theorem coulombAvoidanceCutoff_le_one (N : ℕ) (ε : ℝ) (hε : 0 < ε) (z : CoulombConfig N) :
    coulombAvoidanceCutoff N ε hε z ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro p hp
    exact sub_nonneg.mpr (coulombCollisionBump_le_one p.1 p.2 ε hε z)
  · intro p hp
    linarith [coulombCollisionBump_nonneg p.1 p.2 ε hε z]

theorem coulombAvoidanceCutoff_contDiff (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (coulombAvoidanceCutoff N ε hε) := by
  have hb : ∀ p : Fin N × Fin N, ContDiff ℝ (⊤ : ℕ∞) (coulombCollisionBump p.1 p.2 ε hε) :=
    fun p => coulombCollisionBump_contDiff p.1 p.2 ε hε
  unfold coulombAvoidanceCutoff
  fun_prop

theorem coulombAvoidanceCutoff_zero_near {N : ℕ} (ε : ℝ) (hε : 0 < ε)
    (p : Fin N × Fin N) (hp : p ∈ coulombPairs N) {z : CoulombConfig N}
    (hz : ‖coulombCollisionProjection p.1 p.2 z‖ ≤ ε) :
    coulombAvoidanceCutoff N ε hε z = 0 := by
  apply Finset.prod_eq_zero hp
  rw [coulombCollisionBump_one p.1 p.2 ε hε hz, sub_self]

theorem coulombAvoidanceCutoff_tendsto_one {N : ℕ} (z : CoulombConfig N)
    (hz : z ∈ coulombDomain N) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => coulombAvoidanceCutoff N (ε n) (hε n) z) atTop (𝓝 1) := by
  have hn := (coulombVandermonde_ne_zero_iff z).mp hz
  have ht : ∀ p ∈ coulombPairs N,
      Tendsto (fun n => 1 - coulombCollisionBump p.1 p.2 (ε n) (hε n) z) atTop (𝓝 1) := by
    intro p hp
    simpa using tendsto_const_nhds.sub (coulombCollisionBump_tendsto_zero_off_collision p.1 p.2 z
      (hn p.1 p.2 (ne_of_lt ((mem_coulombPairs p).mp hp))) ε hε hlim)
  simpa [coulombAvoidanceCutoff] using tendsto_finsetProd (coulombPairs N) ht

theorem coulombAvoidanceCutoff_tsupport_subset (N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (φ : CoulombConfig N → ℝ) :
    tsupport (fun z => φ z * coulombAvoidanceCutoff N ε hε z) ⊆ coulombDomain N := by
  intro z hz
  change coulombVandermonde z ≠ 0
  rw [coulombVandermonde_ne_zero_iff]
  intro i j hij heq
  obtain ⟨p, hp, hpz⟩ : ∃ p ∈ coulombPairs N, z p.1 = z p.2 := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨(i, j), (mem_coulombPairs _).mpr h, heq⟩
    · exact ⟨(j, i), (mem_coulombPairs _).mpr h, heq.symm⟩
  let U : Set (CoulombConfig N) := {w | ‖coulombCollisionProjection p.1 p.2 w‖ < ε}
  have hU : IsOpen U := isOpen_lt (coulombCollisionProjection p.1 p.2).continuous.norm continuous_const
  have hsub : Function.support (fun w => φ w * coulombAvoidanceCutoff N ε hε w) ⊆ Uᶜ := by
    intro w hw hwU
    apply hw
    change φ w * coulombAvoidanceCutoff N ε hε w = 0
    rw [coulombAvoidanceCutoff_zero_near ε hε p hp hwU.le, mul_zero]
  have hn := (closure_minimal hsub hU.isClosed_compl) hz
  apply hn
  change ‖(Real.sqrt 2)⁻¹ • (z p.1 - z p.2)‖ < ε
  rw [hpz, sub_self, smul_zero, norm_zero]
  exact hε

def coulombAvoidanceTestFunction (N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤) :
    TestFunction (coulombDomain N) ℝ ⊤ :=
  ⟨fun z => φ z * coulombAvoidanceCutoff N ε hε z,
    φ.contDiff.mul (coulombAvoidanceCutoff_contDiff N ε hε),
    φ.hasCompactSupport.mul_right, coulombAvoidanceCutoff_tsupport_subset N ε hε φ⟩

end RepulsiveCoulomb

