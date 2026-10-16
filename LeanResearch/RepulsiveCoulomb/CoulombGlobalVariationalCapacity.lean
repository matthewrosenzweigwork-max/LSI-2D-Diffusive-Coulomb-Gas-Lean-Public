module

public import LeanResearch.RepulsiveCoulomb.CoulombVariationalCapacity
public import LeanResearch.RepulsiveCoulomb.CoulombConstantDomain

@[expose] public section

/-! Literal global collision capacity, manuscript Proposition prop:capacity.
The existing constant-domain theorem was proved by the actual outer and
collision cutoffs. Its collision-free core approximants give DIRECT GLOBAL
admissible functions: 1 minus each approximant equals one on the open
complement of that approximant's support. Thus no compact-only conclusion or
unproved countable-subadditivity premise is used here. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology ENNReal
namespace RepulsiveCoulomb

/-- The full collision set in the ambient labeled configuration space. -/
def coulombCollisionSet (N : ℕ) : Set (CoulombConfig N) :=
  (coulombDomain N : Set (CoulombConfig N))ᶜ

/-- A pair collision stratum; the zero-capacity theorem assumes distinct labels. -/
def coulombPairCollisionStratum (N : ℕ) (i j : Fin N) : Set (CoulombConfig N) :=
  {z | z i = z j}

theorem coulombPairCollisionStratum_subset {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    coulombPairCollisionStratum N i j ⊆ coulombCollisionSet N := by
  intro z hz hfree
  exact ((coulombVandermonde_ne_zero_iff z).mp hfree i j hij) hz

/-- Subtracting a collision-free core function from the constant one gives
an admissible function on an open neighborhood of the ENTIRE collision set. -/
theorem coulomb_constant_sub_core_capacity_admissible (N : ℕ) {β : ℝ}
    (hβ : 0 < β) (one : CoulombFormDomain N hβ)
    (hone : coulombFormValueL N hβ one =ᵐ[coulombMeasure N β] (fun _ ↦ (1 : ℝ)))
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombCapacityAdmissible N hβ (coulombCollisionSet N)
      (one - coulombFormCore hβ φ) := by
  let O : Set (CoulombConfig N) := (tsupport (φ : CoulombConfig N → ℝ))ᶜ
  have hO : IsOpen O := (isClosed_tsupport (φ : CoulombConfig N → ℝ)).isOpen_compl
  refine ⟨O, hO, ?_, ?_⟩
  · intro z hz hsupport
    exact hz (φ.tsupport_subset hsupport)
  · apply (ae_restrict_iff' hO.measurableSet).mpr
    have hsub := Lp.coeFn_sub (coulombFormValueL N hβ one)
      (coulombFormValueL N hβ (coulombFormCore hβ φ))
    filter_upwards [hone, coulombFormCore_value hβ φ, hsub] with z h1 hφ hs
    intro hz
    rw [map_sub, hs, Pi.sub_apply, h1, hφ, image_eq_zero_of_notMem_tsupport hz, sub_zero]

theorem coulombCollisionSet_capacity_zero_add_two (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    coulombVariationalOneCapacity (N + 2) hβ (coulombCollisionSet (N + 2)) = 0 := by
  obtain ⟨φ, hφ⟩ := coulombFormCore_approximation (N + 2) hβ (coulombConstantForm N hβ)
  apply coulombVariationalOneCapacity_zero_of_tendsto (N + 2) hβ
    (coulombCollisionSet (N + 2))
    (fun n ↦ coulombConstantForm N hβ - coulombFormCore hβ (φ n))
  · intro n
    exact coulomb_constant_sub_core_capacity_admissible (N + 2) hβ
      (coulombConstantForm N hβ) (coulombConstantForm_value N hβ) (φ n)
  · simpa only [sub_self] using
      ((tendsto_const_nhds (x := coulombConstantForm N hβ)).sub hφ)

/-- For the vacuous particle counts there are no distinct colliding labels. -/
theorem coulombCollisionSet_eq_empty_of_le_one (N : ℕ) (hN : N ≤ 1) :
    coulombCollisionSet N = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  apply hz
  apply (coulombVandermonde_ne_zero_iff z).mpr
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have he : i = j := Fin.ext (by omega)
  exact (hij he).elim

/-- Global, usual variational 1-capacity zero for every particle count and
positive inverse temperature. In particular this covers every N >= 2 in the
manuscript, without a compact-support restriction on the collision set. -/
theorem coulombCollisionSet_capacity_zero (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    coulombVariationalOneCapacity N hβ (coulombCollisionSet N) = 0 := by
  by_cases hN : 2 ≤ N
  · obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
    exact coulombCollisionSet_capacity_zero_add_two k hβ
  · rw [coulombCollisionSet_eq_empty_of_le_one N (by omega)]
    exact coulombVariationalOneCapacity_empty N hβ

/-- Every collision stratum, including all multiple-collision strata and
arbitrary subsets thereof, has zero capacity by monotonicity. -/
theorem coulomb_collision_stratum_capacity_zero (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (s : Set (CoulombConfig N)) (hs : s ⊆ coulombCollisionSet N) :
    coulombVariationalOneCapacity N hβ s = 0 := by
  apply le_antisymm _ zero_le
  exact (coulombVariationalOneCapacity_mono N hβ hs).trans
    (le_of_eq (coulombCollisionSet_capacity_zero N hβ))

theorem coulomb_pair_collision_capacity_zero (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (i j : Fin N) (hij : i ≠ j) :
    coulombVariationalOneCapacity N hβ (coulombPairCollisionStratum N i j) = 0 :=
  coulomb_collision_stratum_capacity_zero N hβ _
    (coulombPairCollisionStratum_subset i j hij)

/-- Both assertions of manuscript Proposition prop:capacity, in the same
closed physical-gradient graph used by the final LSI theorem. -/
theorem coulomb_collision_capacity_and_common_core (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    (∀ s : Set (CoulombConfig (N + 2)), s ⊆ coulombCollisionSet (N + 2) →
      coulombVariationalOneCapacity (N + 2) hβ s = 0) ∧
    closure (range (coulombAmbientJet N hβ)) = coulombCoreGraph (N + 2) hβ := by
  exact ⟨fun s hs ↦ coulomb_collision_stratum_capacity_zero (N + 2) hβ s hs,
    coulomb_common_core N hβ⟩

end RepulsiveCoulomb
