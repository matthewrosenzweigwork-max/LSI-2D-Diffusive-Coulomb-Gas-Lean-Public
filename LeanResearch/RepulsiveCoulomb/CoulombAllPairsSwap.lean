module

public import LeanResearch.RepulsiveCoulomb.CoulombPermutationCore
public import LeanResearch.RepulsiveCoulomb.CoulombFirstSwapBound
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section

/-! Label transport for an arbitrary selected pair. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombSwapFirst_eq_permute (N : ℕ) (z : CoulombConfig (N + 2)) :
    coulombSwapFirst N z = coulombPermute (Equiv.swap 0 (Fin.succ 0)) z := by
  ext k
  refine Fin.cases ?_ (fun l => Fin.cases ?_ (fun j => ?_) l) k
  · change z (Fin.succ 0) = z (Equiv.swap 0 (Fin.succ 0) 0)
    rw [Equiv.swap_apply_left]
  · change z 0 = z (Equiv.swap 0 (Fin.succ 0) (Fin.succ 0))
    rw [Equiv.swap_apply_right]
  · change z j.succ.succ = z (Equiv.swap 0 (Fin.succ 0) j.succ.succ)
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero j.succ)
      (fun h => Fin.succ_ne_zero j (Fin.succ_inj.mp h))]

theorem coulombPermute_swap_conjugacy {N : ℕ} (σ : Equiv.Perm (Fin N))
    (i j : Fin N) (z : CoulombConfig N) :
    coulombPermute σ (coulombPermute (Equiv.swap i j) z) =
      coulombPermute (Equiv.swap (σ.symm i) (σ.symm j)) (coulombPermute σ z) := by
  ext k
  simp only [coulombPermute_apply]
  have he := σ.injective.swap_apply (σ.symm i) (σ.symm j) k
  simp only [Equiv.apply_symm_apply] at he
  exact congrArg (fun l => z l) he

theorem exists_coulomb_pair_permutation {N : ℕ} (i j : Fin (N + 2)) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin (N + 2)), σ 0 = i ∧ σ (Fin.succ 0) = j := by
  let f : Fin 2 → Fin (N + 2) := Fin.castLE (by omega)
  let g : Fin 2 → Fin (N + 2) := Fin.cons i (fun _ : Fin 1 => j)
  have hf : Function.Injective f := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun x : Fin (N + 2) => x.val) h
  have hg : Function.Injective g := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [g]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  exact ⟨σ, hσ 0, hσ 1⟩

theorem coulomb_core_all_pairs_swap_bound {β : ℝ} (hβ : 0 < β) :
    ∃ P : ℝ, 0 < P ∧ ∀ (N : ℕ) (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤)
      (i j : Fin (N + 2)), i ≠ j →
      (∫ z, (φ z - φ (coulombPermute (Equiv.swap i j) z)) ^ 2 ∂coulombMeasure (N + 2) β) ≤
        (2 * P) * (∫ z, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) z i -
          gradient (φ : CoulombConfig (N + 2) → ℝ) z j‖ ^ 2 ∂coulombMeasure (N + 2) β) := by
  obtain ⟨P, hP, hp⟩ := coulomb_core_first_swap_bound hβ
  refine ⟨P, hP, ?_⟩
  intro N φ i j hij
  obtain ⟨σ, hσ0, hσ1⟩ := exists_coulomb_pair_permutation i j hij
  have h := hp N (coulombPermuteCore σ.symm φ)
  have hswap (z : CoulombConfig (N + 2)) :
      coulombPermute σ.symm (coulombSwapFirst N z) =
        coulombPermute (Equiv.swap i j) (coulombPermute σ.symm z) := by
    rw [coulombSwapFirst_eq_permute, coulombPermute_swap_conjugacy]
    simp only [Equiv.symm_symm, hσ0, hσ1]
  simp only [coulombPermuteCore_apply, coulombPermuteCore_gradient_component,
    Equiv.symm_symm, hσ0, hσ1, hswap] at h
  have hm := coulombPermute_gibbs_preserving hβ.le σ.symm
  have hF := hm.integral_comp (coulombPermute σ.symm).toMeasurableEquiv.measurableEmbedding
    (fun z => (φ z - φ (coulombPermute (Equiv.swap i j) z)) ^ 2)
  have hG := hm.integral_comp (coulombPermute σ.symm).toMeasurableEquiv.measurableEmbedding
    (fun z => ‖gradient (φ : CoulombConfig (N + 2) → ℝ) z i -
      gradient (φ : CoulombConfig (N + 2) → ℝ) z j‖ ^ 2)
  rw [hF, hG] at h
  exact h

end RepulsiveCoulomb

