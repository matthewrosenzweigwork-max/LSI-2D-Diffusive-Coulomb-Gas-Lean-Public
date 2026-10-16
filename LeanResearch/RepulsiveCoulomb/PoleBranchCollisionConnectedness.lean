import LeanResearch.RepulsiveCoulomb.PoleBranchGenericCollisionGeometry
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! The actual collision complement is path connected for every particle count.
A complex affine line between two regular configurations has only finitely many
bad parameters. A path in their planar complement maps back into the original
domain. This argument has no temperature or collision-exponent restriction. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

theorem poleBranch_finite_affine_zero_set {a b : ℂ} (ha : a ≠ 0) :
    {t : ℂ | a + t * b = 0}.Finite := by
  by_cases hb : b = 0
  · simp only [hb, mul_zero, add_zero, ha, setOf_false]
    exact finite_empty
  · have hinj : Function.Injective (fun t : ℂ => a + t * b) := by
      intro t u h
      exact mul_right_cancel₀ hb (add_left_cancel h)
    exact (finite_singleton (0 : ℂ)).preimage hinj.injOn

theorem poleBranch_coulomb_affine_bad_parameters_finite
    {N : ℕ} {z w : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    {t : ℂ | z + t • (w - z) ∉ coulombDomain N}.Finite := by
  let γ : ℂ → CoulombConfig N := fun t => z + t • (w - z)
  let B : Set ℂ := ⋃ p : PoleBranchCoulombPair N, {t | γ t p.1.1 = γ t p.1.2}
  have hpair (p : PoleBranchCoulombPair N) : {t : ℂ | γ t p.1.1 = γ t p.1.2}.Finite := by
    have hne : z p.1.1 - z p.1.2 ≠ 0 := sub_ne_zero.mpr
      ((coulombVandermonde_ne_zero_iff z).mp hz p.1.1 p.1.2 (ne_of_lt p.2))
    have heq : {t : ℂ | γ t p.1.1 = γ t p.1.2} =
        {t : ℂ | (z p.1.1 - z p.1.2) +
          t * ((w p.1.1 - z p.1.1) - (w p.1.2 - z p.1.2)) = 0} := by
      ext t
      have hdiff : γ t p.1.1 - γ t p.1.2 = (z p.1.1 - z p.1.2) +
          t * ((w p.1.1 - z p.1.1) - (w p.1.2 - z p.1.2)) := by
        dsimp only [γ]
        simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
        ring
      change (γ t p.1.1 = γ t p.1.2) ↔
        (z p.1.1 - z p.1.2) + t * ((w p.1.1 - z p.1.1) - (w p.1.2 - z p.1.2)) = 0
      rw [← sub_eq_zero, hdiff]
    rw [heq]
    exact poleBranch_finite_affine_zero_set hne
  have hB : B.Finite := Set.finite_iUnion hpair
  have hbad : {t : ℂ | γ t ∉ coulombDomain N} = B := by
    ext t
    constructor
    · intro ht
      by_contra hn
      apply ht
      change (∏ q ∈ coulombPairs N, (γ t q.1 - γ t q.2)) ≠ 0
      apply Finset.prod_ne_zero_iff.mpr
      intro q hq
      apply sub_ne_zero.mpr
      intro heq
      exact hn (mem_iUnion.mpr ⟨⟨q, (mem_coulombPairs q).mp hq⟩, heq⟩)
    · intro ht hreg
      obtain ⟨p, hp⟩ := mem_iUnion.mp ht
      exact ((coulombVandermonde_ne_zero_iff (γ t)).mp hreg p.1.1 p.1.2 (ne_of_lt p.2)) hp
  simpa only [← hbad, γ] using hB

theorem poleBranch_coulombDomain_joinedIn
    {N : ℕ} {z w : CoulombConfig N} (hz : z ∈ coulombDomain N) (hw : w ∈ coulombDomain N) :
    JoinedIn (coulombDomain N : Set (CoulombConfig N)) z w := by
  let γ : ℂ → CoulombConfig N := fun t => z + t • (w - z)
  let B : Set ℂ := {t | γ t ∉ coulombDomain N}
  have hB : B.Finite := poleBranch_coulomb_affine_bad_parameters_finite hz
  have hg : Continuous γ := by fun_prop
  have hg0 : γ 0 = z := by simp only [γ, zero_smul, add_zero]
  have hg1 : γ 1 = w := by dsimp only [γ]; rw [one_smul]; abel
  have h0 : (0 : ℂ) ∈ Bᶜ := by simpa only [B, mem_compl_iff, mem_setOf_eq, not_not, hg0] using hz
  have h1 : (1 : ℂ) ∈ Bᶜ := by simpa only [B, mem_compl_iff, mem_setOf_eq, not_not, hg1] using hw
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  have hc := hB.countable.isPathConnected_compl_of_one_lt_rank hrank
  have hpath := (hc.joinedIn 0 h0 1 h1).map hg.continuousOn
  have hsub : γ '' Bᶜ ⊆ (coulombDomain N : Set (CoulombConfig N)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact not_not.mp ht
  simpa only [hg0, hg1] using hpath.mono hsub

theorem poleBranch_coulombDomain_isPathConnected (N : ℕ) :
    IsPathConnected (coulombDomain N : Set (CoulombConfig N)) := by
  apply isPathConnected_iff.mpr
  exact ⟨(poleBranch_coulombDomain_dense N).nonempty,
    fun _ hz _ hw => poleBranch_coulombDomain_joinedIn hz hw⟩

theorem poleBranch_coulombDomain_isPreconnected (N : ℕ) :
    IsPreconnected (coulombDomain N : Set (CoulombConfig N)) :=
  (poleBranch_coulombDomain_isPathConnected N).isConnected.isPreconnected

end RepulsiveCoulomb
