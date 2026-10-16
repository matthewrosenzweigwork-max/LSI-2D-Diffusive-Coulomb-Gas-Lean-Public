import LeanResearch.RepulsiveCoulomb.CoulombExhaustionGeometry

/-! Compact sublevels of the canonical exhaustion stay away from every collision. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem coulombExhaustion_sublevel_eq (N : ℕ) (R : ℝ) :
    {z : CoulombConfig N | z ∈ coulombDomain N ∧ coulombExhaustion z ≤ R} =
      {z : CoulombConfig N | 1 ≤ ‖coulombVandermonde z‖ ^ 2 * (R - ‖z‖ ^ 2)} := by
  ext z
  constructor
  · rintro ⟨hz,he⟩
    have hp : 0 < ‖coulombVandermonde z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
    rw [coulombExhaustion_eq] at he
    have hi : (‖coulombVandermonde z‖ ^ 2)⁻¹ ≤ R - ‖z‖ ^ 2 := by linarith
    have hi' : 1 / (‖coulombVandermonde z‖ ^ 2) ≤ R - ‖z‖ ^ 2 := by simpa only [one_div] using hi
    have hh := (div_le_iff₀ hp).mp hi'
    simpa only [Set.mem_setOf_eq, mul_comm] using hh
  · intro h
    change 1 ≤ ‖coulombVandermonde z‖ ^ 2 * (R - ‖z‖ ^ 2) at h
    have hz : coulombVandermonde z ≠ 0 := by
      intro hz
      norm_num [hz] at h
    have hp : 0 < ‖coulombVandermonde z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
    refine ⟨hz, ?_⟩
    rw [coulombExhaustion_eq]
    have hi : 1 / (‖coulombVandermonde z‖ ^ 2) ≤ R - ‖z‖ ^ 2 :=
      (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using h)
    rw [one_div] at hi
    linarith

theorem coulombExhaustion_sublevel_isCompact (N : ℕ) (R : ℝ) :
    IsCompact {z : CoulombConfig N | z ∈ coulombDomain N ∧ coulombExhaustion z ≤ R} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · rw [coulombExhaustion_sublevel_eq]
    exact isClosed_le continuous_const
      (((coulombVandermonde_continuous N).norm.pow 2).mul (continuous_const.sub (continuous_norm.pow 2)))
  · apply (isBounded_iff_forall_norm_le).mpr
    refine ⟨max R 0 + 1, ?_⟩
    intro z hz
    have hn : ‖z‖ ^ 2 ≤ R := by
      have hp : 0 ≤ ‖(coulombVandermonde z)⁻¹‖ ^ 2 := sq_nonneg _
      have he := hz.2
      change ‖z‖ ^ 2 + ‖(coulombVandermonde z)⁻¹‖ ^ 2 ≤ R at he
      linarith
    have hR := le_max_left R 0
    have h0 := le_max_right R 0
    nlinarith [norm_nonneg z]

theorem coulombExhaustion_strict_sublevel_closure_subset (N : ℕ) (R : ℝ) :
    closure {z : CoulombConfig N | z ∈ coulombDomain N ∧ coulombExhaustion z < R} ⊆
      {z : CoulombConfig N | z ∈ coulombDomain N ∧ coulombExhaustion z ≤ R} :=
  closure_minimal (fun _ hz => ⟨hz.1, hz.2.le⟩) (coulombExhaustion_sublevel_isCompact N R).isClosed

theorem coulombExhaustion_strict_sublevel_relativelyCompact (N : ℕ) (R : ℝ) :
    IsCompact (closure {z : CoulombConfig N | z ∈ coulombDomain N ∧ coulombExhaustion z < R}) ∧
      closure {z : CoulombConfig N | z ∈ coulombDomain N ∧ coulombExhaustion z < R} ⊆ coulombDomain N := by
  have hs := coulombExhaustion_strict_sublevel_closure_subset N R
  exact ⟨(coulombExhaustion_sublevel_isCompact N R).of_isClosed_subset isClosed_closure hs,
    fun z hz => (hs hz).1⟩

end RepulsiveCoulomb
