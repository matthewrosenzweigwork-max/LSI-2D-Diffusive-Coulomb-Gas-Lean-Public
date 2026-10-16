import LeanResearch.RepulsiveCoulomb.CoulombGlobalVariationalCapacity

/-! Fresh literal exposure of the original global variational 1-capacity and
ambient common core. Admissibility is on an open neighborhood and the cost is
the full physical form norm, not a measure-zero surrogate. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RepulsiveCoulomb.PaperRoute

theorem paper_original_collision_capacity (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    coulombVariationalOneCapacity N hβ (coulombCollisionSet N) = 0 :=
  coulombCollisionSet_capacity_zero N hβ

theorem paper_original_collision_capacity_and_common_core (m : ℕ) {β : ℝ}
    (hβ : 0 < β) :
    (∀ s : Set (CoulombConfig (m + 2)), s ⊆ coulombCollisionSet (m + 2) →
      coulombVariationalOneCapacity (m + 2) hβ s = 0) ∧
    closure (range (coulombAmbientJet m hβ)) = coulombCoreGraph (m + 2) hβ :=
  coulomb_collision_capacity_and_common_core m hβ

theorem paper_original_capacity_open_neighborhood (N : ℕ) {β : ℝ}
    (hβ : 0 < β) (s : Set (CoulombConfig N)) :
    coulombVariationalOneCapacity N hβ s =
      ⨅ (O : Opens (CoulombConfig N)) (_ : s ⊆ O)
        (u : CoulombFormDomain N hβ)
        (_ : ∀ᵐ z ∂(coulombMeasure N β).restrict (O : Set (CoulombConfig N)),
          1 ≤ coulombFormValueL N hβ u z), ENNReal.ofReal (‖u‖ ^ 2) :=
  coulombVariationalOneCapacity_eq_open_inf N hβ s

theorem paper_original_capacity_physical_cost (N : ℕ) {β : ℝ}
    (hβ : 0 < β) (u : CoulombFormDomain N hβ) :
    ENNReal.ofReal (‖u‖ ^ 2) = ENNReal.ofReal
      ((∫ z, (coulombFormValueL N hβ u z) ^ 2 ∂coulombMeasure N β) +
        ∫ z, ‖coulombFormGradientL N hβ u z‖ ^ 2 ∂coulombMeasure N β) :=
  coulomb_capacity_cost_eq_mass_add_energy N hβ u

end RepulsiveCoulomb.PaperRoute
