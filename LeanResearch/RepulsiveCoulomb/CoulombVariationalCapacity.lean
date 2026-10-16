import LeanResearch.RepulsiveCoulomb.CoulombFormIntegrals

/-! The usual outer variational 1-capacity of the actual closed Coulomb form.
The admissible value is at least one almost everywhere on an OPEN neighborhood
of the target set, not merely almost everywhere on the target itself.
The cost is the full L2-plus-physical-gradient form norm. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology ENNReal
namespace RepulsiveCoulomb

/-- Usual outer-capacity admissibility: a full-domain function which is at
least one almost everywhere on an open neighborhood of the target set. -/
def coulombCapacityAdmissible (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (s : Set (CoulombConfig N)) (u : CoulombFormDomain N hβ) : Prop :=
  ∃ O : Set (CoulombConfig N), IsOpen O ∧ s ⊆ O ∧
    ∀ᵐ z ∂(coulombMeasure N β).restrict O, 1 ≤ coulombFormValueL N hβ u z

/-- The variational 1-capacity, including outer regularization by all open
neighborhoods. An empty admissible class has infimum infinity. -/
def coulombVariationalOneCapacity (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (s : Set (CoulombConfig N)) : ℝ≥0∞ :=
  ⨅ (u : CoulombFormDomain N hβ) (_ : coulombCapacityAdmissible N hβ s u),
    ENNReal.ofReal (‖u‖ ^ 2)

/-- Explicit agreement with the usual two-stage definition: first minimize
E_1 over full-domain functions dominating one a.e. on an open set, then take
the infimum over all open supersets of the target. -/
theorem coulombVariationalOneCapacity_eq_open_inf (N : ℕ) {β : ℝ}
    (hβ : 0 < β) (s : Set (CoulombConfig N)) :
    coulombVariationalOneCapacity N hβ s =
      ⨅ (O : Opens (CoulombConfig N)) (_ : s ⊆ O)
        (u : CoulombFormDomain N hβ)
        (_ : ∀ᵐ z ∂(coulombMeasure N β).restrict (O : Set (CoulombConfig N)),
          1 ≤ coulombFormValueL N hβ u z), ENNReal.ofReal (‖u‖ ^ 2) := by
  apply le_antisymm
  · apply le_iInf
    intro O
    apply le_iInf
    intro hsO
    apply le_iInf
    intro u
    apply le_iInf
    intro hu
    exact iInf_le_of_le u (iInf_le_of_le ⟨O, O.isOpen, hsO, hu⟩ le_rfl)
  · apply le_iInf
    intro u
    apply le_iInf
    rintro ⟨O, hO, hsO, hu⟩
    exact iInf_le_of_le (⟨O, hO⟩ : Opens (CoulombConfig N))
      (iInf_le_of_le hsO (iInf_le_of_le u (iInf_le_of_le hu le_rfl)))

/-- The cost is exactly E(u,u) + ||u||_2^2 for the full physical form. -/
theorem coulomb_capacity_cost_eq_mass_add_energy (N : ℕ) {β : ℝ}
    (hβ : 0 < β) (u : CoulombFormDomain N hβ) :
    ENNReal.ofReal (‖u‖ ^ 2) = ENNReal.ofReal
      ((∫ z, (coulombFormValueL N hβ u z) ^ 2 ∂coulombMeasure N β) +
        ∫ z, ‖coulombFormGradientL N hβ u z‖ ^ 2 ∂coulombMeasure N β) := by
  rw [coulombForm_norm_sq, coulombFormValue_norm_sq_eq_integral,
    coulombFormEnergy_eq_integral]

theorem coulombVariationalOneCapacity_le (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (s : Set (CoulombConfig N)) (u : CoulombFormDomain N hβ)
    (hu : coulombCapacityAdmissible N hβ s u) :
    coulombVariationalOneCapacity N hβ s ≤ ENNReal.ofReal (‖u‖ ^ 2) := by
  exact iInf_le_of_le u (iInf_le_of_le hu le_rfl)

theorem coulombVariationalOneCapacity_mono (N : ℕ) {β : ℝ} (hβ : 0 < β)
    {s t : Set (CoulombConfig N)} (hst : s ⊆ t) :
    coulombVariationalOneCapacity N hβ s ≤ coulombVariationalOneCapacity N hβ t := by
  apply le_iInf
  intro u
  apply le_iInf
  rintro ⟨O, hO, htO, hu⟩
  exact coulombVariationalOneCapacity_le N hβ s u ⟨O, hO, hst.trans htO, hu⟩

theorem coulombVariationalOneCapacity_empty (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    coulombVariationalOneCapacity N hβ ∅ = 0 := by
  apply le_antisymm _ (zero_le)
  have hadm : coulombCapacityAdmissible N hβ ∅ (0 : CoulombFormDomain N hβ) := by
    refine ⟨∅, isOpen_empty, subset_rfl, ?_⟩
    simp
  simpa using coulombVariationalOneCapacity_le N hβ ∅ 0 hadm

/-- Any sequence of genuinely admissible full-domain functions with vanishing
form norm proves zero capacity. No null-set or collision assumption is used. -/
theorem coulombVariationalOneCapacity_zero_of_tendsto (N : ℕ) {β : ℝ}
    (hβ : 0 < β) (s : Set (CoulombConfig N))
    (u : ℕ → CoulombFormDomain N hβ)
    (hu : ∀ n, coulombCapacityAdmissible N hβ s (u n))
    (hlim : Tendsto u atTop (𝓝 0)) :
    coulombVariationalOneCapacity N hβ s = 0 := by
  have hcost : Tendsto (fun n ↦ ENNReal.ofReal (‖u n‖ ^ 2)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (hlim.norm.pow 2)
  apply le_antisymm _ (zero_le)
  exact ge_of_tendsto hcost
    (Eventually.of_forall fun n ↦ coulombVariationalOneCapacity_le N hβ s (u n) (hu n))

end RepulsiveCoulomb
