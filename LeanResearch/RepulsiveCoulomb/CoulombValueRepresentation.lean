module

public import LeanResearch.RepulsiveCoulomb.CoulombFormPairMaps

@[expose] public section

/-! The actual normalized Gibbs L2 representation of the label group. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombPermute_one (N : ℕ) (z : CoulombConfig N) :
    coulombPermute (1 : Equiv.Perm (Fin N)) z = z := by
  ext i
  rfl

theorem coulombPermute_mul {N : ℕ} (σ τ : Equiv.Perm (Fin N)) (z : CoulombConfig N) :
    coulombPermute (σ * τ) z = coulombPermute τ (coulombPermute σ z) := by
  ext i
  rfl

theorem coulombValuePermuteL_one (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    coulombValuePermuteL N hβ 1 = ContinuousLinearMap.id ℝ (Lp ℝ 2 (coulombMeasure N β)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [coulombValuePermuteL_coe N hβ 1 v] with z hz
  change coulombValuePermuteL N hβ 1 v z = v z
  rw [hz, coulombPermute_one]

theorem coulombValuePermuteL_mul_apply (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (σ τ : Equiv.Perm (Fin N)) (v : Lp ℝ 2 (coulombMeasure N β)) :
    coulombValuePermuteL N hβ σ (coulombValuePermuteL N hβ τ v) =
      coulombValuePermuteL N hβ (σ * τ) v := by
  have ht := (coulombPermute_gibbs_preserving hβ.le σ).quasiMeasurePreserving.ae
    (coulombValuePermuteL_coe N hβ τ v)
  apply Lp.ext
  filter_upwards [coulombValuePermuteL_coe N hβ σ (coulombValuePermuteL N hβ τ v),
    ht, coulombValuePermuteL_coe N hβ (σ * τ) v] with z hs ht hst
  rw [hs, ht, hst, coulombPermute_mul]

def coulombValueRepresentation (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Equiv.Perm (Fin N) →* (Lp ℝ 2 (coulombMeasure N β) →L[ℝ] Lp ℝ 2 (coulombMeasure N β)) where
  toFun := coulombValuePermuteL N hβ
  map_one' := coulombValuePermuteL_one N hβ
  map_mul' σ τ := by
    apply ContinuousLinearMap.ext
    intro v
    exact (coulombValuePermuteL_mul_apply N hβ σ τ v).symm

theorem coulombValueRepresentation_inner (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (σ : Equiv.Perm (Fin N)) (v w : Lp ℝ 2 (coulombMeasure N β)) :
    inner ℝ (coulombValueRepresentation N hβ σ v) (coulombValueRepresentation N hβ σ w) =
      inner ℝ v w :=
  (Lp.compMeasurePreservingₗᵢ ℝ (coulombPermute σ)
    (coulombPermute_gibbs_preserving hβ.le σ)).inner_map_map v w

end RepulsiveCoulomb

