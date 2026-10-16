module

public import LeanResearch.RepulsiveCoulomb.DbarBranchTestPairing
public import LeanResearch.RepulsiveCoulomb.CoulombWirtinger
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule

@[expose] public section

/-! The maximal distributional dbar graph on the actual weighted L2 spaces.
Its equations test the literal (D_x + i D_y)/2 against every compact smooth
test on the collision complement. Closedness and single-valuedness are proved;
no boundary condition, core-density claim, regularity, or estimate is assumed. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology Distributions
namespace RepulsiveCoulomb

abbrev CoulombDbarL2Pair (N : ℕ) (β : ℝ) :=
  Lp ℂ 2 (coulombMeasure N β) × Lp (CoulombConfig N) 2 (coulombMeasure N β)

def coulombWeakDbarConstraintL {N : ℕ} {β : ℝ} (hβ : 0 < β) (i : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) : CoulombDbarL2Pair N β →L[ℝ] ℂ :=
  ((coulombL2TestPairingL hβ φ).comp ((coulombCoordinate i).compLpL 2 (coulombMeasure N β))).comp
      (ContinuousLinearMap.snd ℝ _ _) +
    (1 / 2 : ℝ) •
      (((coulombL2TestPairingL hβ
          (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N i 1) φ)).comp
          (ContinuousLinearMap.fst ℝ _ _)) +
        ((Complex.I • ContinuousLinearMap.id ℝ ℂ).comp
          ((coulombL2TestPairingL hβ
            (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N i Complex.I) φ)).comp
            (ContinuousLinearMap.fst ℝ _ _))))

theorem coulombWeakDbarConstraintL_apply {N : ℕ} {β : ℝ} (hβ : 0 < β) (i : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (J : CoulombDbarL2Pair N β) :
    coulombWeakDbarConstraintL hβ i φ J =
      coulombL2Distribution hβ ((coulombCoordinate i).compLpL 2 (coulombMeasure N β) J.2) φ +
        (1 / 2 : ℝ) •
          (coulombL2Distribution hβ J.1
            (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N i 1) φ) +
          Complex.I * coulombL2Distribution hβ J.1
            (TestFunction.lineDerivCLM ℝ (coulombCoordinateInjection N i Complex.I) φ)) := by
  simp only [coulombWeakDbarConstraintL, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, coulombL2TestPairingL_apply]
  rfl

def coulombMaxDbarGraph {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    Submodule ℝ (CoulombDbarL2Pair N β) where
  carrier := {J | ∀ i φ, coulombWeakDbarConstraintL hβ i φ J = 0}
  zero_mem' := by intro i φ; exact map_zero _
  add_mem' := by
    intro J K hJ hK i φ
    rw [map_add, hJ i φ, hK i φ, add_zero]
  smul_mem' := by
    intro c J hJ i φ
    rw [map_smul, hJ i φ, smul_zero]

theorem coulombMaxDbarGraph_mem_iff {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (J : CoulombDbarL2Pair N β) :
    J ∈ coulombMaxDbarGraph hβ ↔ ∀ i φ, coulombWeakDbarConstraintL hβ i φ J = 0 := Iff.rfl

theorem coulombMaxDbarGraph_isClosed {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    IsClosed (coulombMaxDbarGraph (N := N) hβ : Set (CoulombDbarL2Pair N β)) := by
  change IsClosed {J | ∀ i φ, coulombWeakDbarConstraintL hβ i φ J = 0}
  simp only [setOf_forall]
  exact isClosed_iInter (fun i => isClosed_iInter (fun φ =>
    isClosed_eq (coulombWeakDbarConstraintL hβ i φ).continuous continuous_const))

theorem coulombMaxDbarGraph_unique {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {f : Lp ℂ 2 (coulombMeasure N β)}
    {g g' : Lp (CoulombConfig N) 2 (coulombMeasure N β)}
    (hg : (f, g) ∈ coulombMaxDbarGraph hβ) (hg' : (f, g') ∈ coulombMaxDbarGraph hβ) :
    g = g' := by
  have hc (i : Fin N) :
      (coulombCoordinate i).compLpL 2 (coulombMeasure N β) g =
        (coulombCoordinate i).compLpL 2 (coulombMeasure N β) g' := by
    apply coulombL2Distribution_injective hβ
    ext φ
    have h1 := hg i φ
    have h2 := hg' i φ
    rw [coulombWeakDbarConstraintL_apply] at h1 h2
    exact add_right_cancel (h1.trans h2.symm)
  apply Lp.ext
  have hcoord (i : Fin N) : ∀ᵐ z ∂coulombMeasure N β, g z i = g' z i := by
    have he := (coulombCoordinate i).coeFn_compLpL (p := 2) (μ := coulombMeasure N β) g
    have he' := (coulombCoordinate i).coeFn_compLpL (p := 2) (μ := coulombMeasure N β) g'
    filter_upwards [he, he'] with z hz hz'
    rw [hc i] at hz
    exact hz.symm.trans hz'
  filter_upwards [ae_all_iff.mpr hcoord] with z hz
  ext i
  exact hz i

abbrev CoulombMaxDbarDomain (N : ℕ) {β : ℝ} (hβ : 0 < β) :=
  coulombMaxDbarGraph (N := N) hβ

instance coulombMaxDbarDomain_completeSpace (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    CompleteSpace (CoulombMaxDbarDomain N hβ) :=
  (coulombMaxDbarGraph_isClosed hβ).completeSpace_coe

def coulombMaxDbarValueL (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    CoulombMaxDbarDomain N hβ →L[ℝ] Lp ℂ 2 (coulombMeasure N β) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (coulombMaxDbarGraph hβ).subtypeL

def coulombMaxDbarL (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    CoulombMaxDbarDomain N hβ →L[ℝ] Lp (CoulombConfig N) 2 (coulombMeasure N β) :=
  (ContinuousLinearMap.snd ℝ _ _).comp (coulombMaxDbarGraph hβ).subtypeL

theorem coulombMaxDbarValueL_injective (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Function.Injective (coulombMaxDbarValueL N hβ) := by
  intro u v huv
  apply Subtype.ext
  apply Prod.ext
  · exact huv
  · have hu : (u.val.1, u.val.2) ∈ coulombMaxDbarGraph hβ := u.property
    have hv : (v.val.1, v.val.2) ∈ coulombMaxDbarGraph hβ := v.property
    change u.val.1 = v.val.1 at huv
    rw [← huv] at hv
    exact coulombMaxDbarGraph_unique hβ hu hv

end RepulsiveCoulomb
