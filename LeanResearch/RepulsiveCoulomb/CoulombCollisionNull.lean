module

public import LeanResearch.RepulsiveCoulomb.LabeledCoulombNormalization
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

/-! Every pair-collision hyperplane is a proper real linear subspace and is
Lebesgue null. The full collision-free domain has full Lebesgue measure. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem coulomb_pair_collision_volume_zero {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    volume {z : CoulombConfig N | z i = z j} = 0 := by
  let L : CoulombConfig N →L[ℝ] ℂ := coulombCoordinate i - coulombCoordinate j
  have hp : LinearMap.ker L.toLinearMap ≠ ⊤ := by
    intro ht
    have hv : EuclideanSpace.single i (1 : ℂ) ∈ LinearMap.ker L.toLinearMap := by rw [ht]; trivial
    change (EuclideanSpace.single i (1 : ℂ)) i - (EuclideanSpace.single i (1 : ℂ)) j = 0 at hv
    simp [PiLp.single_apply, hij, hij.symm] at hv
  have he : {z : CoulombConfig N | z i = z j} = (LinearMap.ker L.toLinearMap : Set (CoulombConfig N)) := by
    ext z
    change z i = z j ↔ z i - z j = 0
    exact sub_eq_zero.symm
  rw [he]
  exact Measure.addHaar_submodule volume _ hp

theorem coulombDomain_ae (N : ℕ) : ∀ᵐ z : CoulombConfig N, z ∈ coulombDomain N := by
  have hpair (i j : Fin N) : ∀ᵐ z : CoulombConfig N, i ≠ j → z i ≠ z j := by
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    · have h : ∀ᵐ z : CoulombConfig N, z i ≠ z j := by
        rw [ae_iff]
        simpa only [not_not] using coulomb_pair_collision_volume_zero hij
      exact h.mono (fun _ hz _ => hz)
  have h : ∀ᵐ z : CoulombConfig N, ∀ i j : Fin N, i ≠ j → z i ≠ z j :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hpair i j))
  filter_upwards [h] with z hz
  exact (coulombVandermonde_ne_zero_iff z).mpr hz

theorem coulombWeight_pos_ae {N : ℕ} (β : ℝ) : ∀ᵐ z : CoulombConfig N, 0 < coulombWeight β z := by
  filter_upwards [coulombDomain_ae N] with z hz
  exact coulombWeight_pos_off_collisions β z hz

end RepulsiveCoulomb
