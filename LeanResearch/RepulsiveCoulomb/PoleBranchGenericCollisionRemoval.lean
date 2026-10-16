import LeanResearch.RepulsiveCoulomb.PoleBranchPairWeightedIntegrability
import LeanResearch.RepulsiveCoulomb.PoleBranchGenericCollisionGeometry
import LeanResearch.RepulsiveCoulomb.PoleBranchCauchyFamily

/-! Genuine local removal at a generic selected collision. The chart is the
actual orthonormal relative coordinate, transported by the selected label
permutation; all weighted integrability comes from the original Gibbs L2 norm. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem poleBranch_generic_collision_removable
    {N : ℕ} {β : ℝ} (hβ : 0 < β) (ha2 : β / ((N + 2 : ℕ) : ℝ) ≤ 2)
    {f : CoulombConfig (N + 2) → ℂ} (hf : DifferentiableOn ℂ f (coulombDomain (N + 2)))
    (hi : MemLp f 2 (coulombMeasure (N + 2) β))
    (hsym : ∀ σ : Equiv.Perm (Fin (N + 2)), ∀ z ∈ coulombDomain (N + 2),
      f (coulombPermute σ z) = f z)
    (p : Fin (N + 2) × Fin (N + 2)) (hp : p ∈ coulombPairs (N + 2))
    (z₀ : CoulombConfig (N + 2)) (hz₀ : z₀ p.1 = z₀ p.2)
    (hother : z₀ ∈ poleBranchPairOtherRegular p) :
    ∃ W : Set (CoulombConfig (N + 2)), IsOpen W ∧ z₀ ∈ W ∧
      ∃ F : CoulombConfig (N + 2) → ℂ, DifferentiableOn ℂ F W ∧
        EqOn F f (W ∩ coulombDomain (N + 2)) := by
  obtain ⟨σ, hσ0, hσ1⟩ := exists_coulomb_pair_permutation p.1 p.2
    (ne_of_lt ((mem_coulombPairs p).mp hp))
  let e := poleBranchPairChart σ
  let p₀ : ℂ × CoulombConfig N := (e.symm z₀).1
  have he₀ : e (p₀, 0) = z₀ := by
    have hzero := poleBranchPairChart_inverse_normal_zero σ p.1 p.2 hσ0 hσ1 z₀ hz₀
    have he : (p₀, (0 : ℂ)) = e.symm z₀ := by
      exact Prod.ext rfl hzero.symm
    rw [he, e.apply_symm_apply]
  obtain ⟨ε, C, hε, hC, hbound⟩ :=
    poleBranch_coulomb_collision_lower_neighborhood hβ p hp z₀ hother
  let K : Set (CoulombConfig (N + 2)) := ball z₀ ε ∩ poleBranchPairOtherRegular p
  have hK : IsOpen K := isOpen_ball.inter (poleBranchPairOtherRegular_isOpen p)
  have hzK : z₀ ∈ K := ⟨mem_ball_self hε, hother⟩
  obtain ⟨δ, hδ, hδK⟩ := Metric.isOpen_iff.mp (hK.preimage e.continuous) (p₀, 0)
    (by simpa only [mem_preimage, he₀] using hzK)
  let U : Set (ℂ × CoulombConfig N) := ball p₀ δ
  have hmap : MapsTo e (U ×ˢ ball (0 : ℂ) δ) K := by
    intro pu hpu
    apply hδK
    rw [← ball_prod_same]
    exact hpu
  have hdom (q : ℂ × CoulombConfig N) (hq : q ∈ U) (u : ℂ)
      (hu : u ∈ ball (0 : ℂ) δ \ {0}) : e (q, u) ∈ coulombDomain (N + 2) := by
    apply (poleBranch_domain_iff_selected_pair p hp (hmap ⟨hq, hu.1⟩).2).mpr
    apply sub_ne_zero.mp
    rw [poleBranchPairChart_difference σ p.1 p.2 hσ0 hσ1]
    exact smul_ne_zero (Real.sqrt_pos.mpr (by norm_num)).ne'
      (by simpa only [mem_singleton_iff] using hu.2)
  have hfd : DifferentiableOn ℂ (fun pu => f (e pu)) (U ×ˢ (ball (0 : ℂ) δ \ {0})) :=
    hf.comp e.differentiableOn (fun pu hpu => hdom pu.1 hpu.1 pu.2 hpu.2)
  have hfi := poleBranch_pair_weighted_integrable hβ hC σ p.1 p.2 hσ0 hσ1 hK.measurableSet hi
    (fun z hz => hbound z hz.1) hmap
  have heven : ∀ q ∈ U, ∀ u ∈ ball (0 : ℂ) δ, f (e (q, -u)) = f (e (q, u)) := by
    intro q hq u hu
    by_cases hu0 : u = 0
    · simp only [hu0, neg_zero]
    · rw [poleBranchPairChart_reflection σ p.1 p.2 hσ0 hσ1]
      exact hsym (Equiv.swap p.1 p.2) _ (hdom q hq u ⟨hu, by simpa only [mem_singleton_iff] using hu0⟩)
  obtain ⟨G, hG, hEq⟩ := weighted_even_puncture_removable_family
    (volume : Measure (ℂ × CoulombConfig N)) isOpen_ball
    (div_nonneg hβ.le (Nat.cast_nonneg _)) ha2 (by positivity : 0 < δ / 2)
    (by linarith : δ / 2 < δ) hfd hfi heven
  let W : Set (CoulombConfig (N + 2)) := e '' (U ×ˢ ball (0 : ℂ) (δ / 2))
  have hW : IsOpen W := e.toHomeomorph.isOpenMap _ (isOpen_ball.prod isOpen_ball)
  have hzW : z₀ ∈ W := ⟨(p₀, 0), ⟨mem_ball_self hδ, mem_ball_self (by positivity)⟩, he₀⟩
  refine ⟨W, hW, hzW, fun z => G (e.symm z), ?_, ?_⟩
  · apply hG.comp e.symm.differentiableOn
    intro z hz
    obtain ⟨pu, hpu, rfl⟩ := hz
    simpa only [e.symm_apply_apply] using hpu
  · intro z hz
    change G (e.symm z) = f z
    obtain ⟨pu, hpu, heq⟩ := hz.1
    have hzu : pu.2 ≠ 0 := by
      intro hu
      have hn := (coulombVandermonde_ne_zero_iff z).mp hz.2 p.1 p.2
        (ne_of_lt ((mem_coulombPairs p).mp hp))
      apply hn
      apply sub_eq_zero.mp
      rw [← heq, poleBranchPairChart_difference σ p.1 p.2 hσ0 hσ1, hu, smul_zero]
    rw [← heq, e.symm_apply_apply]
    exact hEq pu.1 hpu.1 pu.2 ⟨hpu.2, by simpa only [mem_singleton_iff] using hzu⟩

end RepulsiveCoulomb
