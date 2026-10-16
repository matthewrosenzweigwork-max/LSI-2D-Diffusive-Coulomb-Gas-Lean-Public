module

public import LeanResearch.RepulsiveCoulomb.CoulombConstantDomain

@[expose] public section

/-! Continuous L2 operators for literal value permutations and physical gradient differences. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

def coulombValuePermuteL (N : ℕ) {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N)) :
    Lp ℝ 2 (coulombMeasure N β) →L[ℝ] Lp ℝ 2 (coulombMeasure N β) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (coulombPermute σ) (coulombPermute_gibbs_preserving hβ.le σ)).toContinuousLinearMap

theorem coulombValuePermuteL_coe (N : ℕ) {β : ℝ} (hβ : 0 < β) (σ : Equiv.Perm (Fin N))
    (v : Lp ℝ 2 (coulombMeasure N β)) :
    coulombValuePermuteL N hβ σ v =ᵐ[coulombMeasure N β] fun z => v (coulombPermute σ z) :=
  Lp.coeFn_compMeasurePreserving v (coulombPermute_gibbs_preserving hβ.le σ)

def coulombFormSwapDifferenceL (N : ℕ) {β : ℝ} (hβ : 0 < β) (i j : Fin N) :
    CoulombFormDomain N hβ →L[ℝ] Lp ℝ 2 (coulombMeasure N β) :=
  coulombFormValueL N hβ -
    (coulombValuePermuteL N hβ (Equiv.swap i j)).comp (coulombFormValueL N hβ)

def coulombFormPairGradientL (N : ℕ) {β : ℝ} (hβ : 0 < β) (i j : Fin N) :
    CoulombFormDomain N hβ →L[ℝ] Lp ℂ 2 (coulombMeasure N β) :=
  ((coulombCoordinate i - coulombCoordinate j).compLpL 2 (coulombMeasure N β)).comp
    (coulombFormGradientL N hβ)

theorem coulombFormSwapDifferenceL_coe (N : ℕ) {β : ℝ} (hβ : 0 < β) (i j : Fin N)
    (u : CoulombFormDomain N hβ) :
    coulombFormSwapDifferenceL N hβ i j u =ᵐ[coulombMeasure N β] fun z =>
      coulombFormValueL N hβ u z -
        coulombFormValueL N hβ u (coulombPermute (Equiv.swap i j) z) := by
  filter_upwards [Lp.coeFn_sub (coulombFormValueL N hβ u)
    (coulombValuePermuteL N hβ (Equiv.swap i j) (coulombFormValueL N hβ u)),
    coulombValuePermuteL_coe N hβ (Equiv.swap i j) (coulombFormValueL N hβ u)] with z hs hp
  change (coulombFormValueL N hβ u -
    coulombValuePermuteL N hβ (Equiv.swap i j) (coulombFormValueL N hβ u)) z = _
  rw [hs, Pi.sub_apply, hp]

theorem coulombFormPairGradientL_coe (N : ℕ) {β : ℝ} (hβ : 0 < β) (i j : Fin N)
    (u : CoulombFormDomain N hβ) :
    coulombFormPairGradientL N hβ i j u =ᵐ[coulombMeasure N β] fun z =>
      coulombFormGradientL N hβ u z i - coulombFormGradientL N hβ u z j :=
  (coulombCoordinate i - coulombCoordinate j).coeFn_compLpL (coulombFormGradientL N hβ u)

theorem coulombFormSwapDifferenceL_core {N : ℕ} {β : ℝ} (hβ : 0 < β) (i j : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombFormSwapDifferenceL N hβ i j (coulombFormCore hβ φ) =ᵐ[coulombMeasure N β]
      fun z => φ z - φ (coulombPermute (Equiv.swap i j) z) := by
  have hp := (coulombPermute_gibbs_preserving hβ.le (Equiv.swap i j)).quasiMeasurePreserving.ae
    (coulombFormCore_value hβ φ)
  filter_upwards [coulombFormSwapDifferenceL_coe N hβ i j (coulombFormCore hβ φ),
    coulombFormCore_value hβ φ, hp] with z hz hv he
  rw [hz, hv, he]

theorem coulombFormPairGradientL_core {N : ℕ} {β : ℝ} (hβ : 0 < β) (i j : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombFormPairGradientL N hβ i j (coulombFormCore hβ φ) =ᵐ[coulombMeasure N β]
      fun z => gradient (φ : CoulombConfig N → ℝ) z i - gradient (φ : CoulombConfig N → ℝ) z j := by
  filter_upwards [coulombFormPairGradientL_coe N hβ i j (coulombFormCore hβ φ),
    coulombFormCore_gradient hβ φ] with z hz hg
  rw [hz, hg]

theorem coulombFormSwapDifferenceL_core_norm (N : ℕ) {β : ℝ} (hβ : 0 < β) (i j : Fin (N + 2))
    (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤) :
    ‖coulombFormSwapDifferenceL (N + 2) hβ i j (coulombFormCore hβ φ)‖ ^ 2 =
      ∫ z, (φ z - φ (coulombPermute (Equiv.swap i j) z)) ^ 2 ∂coulombMeasure (N + 2) β := by
  rw [coulomb_L2_norm_sq N]
  apply integral_congr_ae
  filter_upwards [coulombFormSwapDifferenceL_core hβ i j φ] with z hz
  simp only [hz, Real.norm_eq_abs, sq_abs]

theorem coulombFormPairGradientL_core_norm (N : ℕ) {β : ℝ} (hβ : 0 < β) (i j : Fin (N + 2))
    (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤) :
    ‖coulombFormPairGradientL (N + 2) hβ i j (coulombFormCore hβ φ)‖ ^ 2 =
      ∫ z, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) z i -
        gradient (φ : CoulombConfig (N + 2) → ℝ) z j‖ ^ 2 ∂coulombMeasure (N + 2) β := by
  rw [coulomb_L2_norm_sq N]
  apply integral_congr_ae
  filter_upwards [coulombFormPairGradientL_core hβ i j φ] with z hz
  rw [hz]

end RepulsiveCoulomb

