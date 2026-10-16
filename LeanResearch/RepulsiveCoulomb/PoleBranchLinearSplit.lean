module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-! A genuine complex-linear product chart adapted to a transverse line. -/
noncomputable section
namespace RepulsiveCoulomb

def poleBranchLinearSplit
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    (q : X →L[ℂ] ℂ) (v : X) (hq : q v = 1) : X ≃L[ℂ] q.ker × ℂ :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun x => (⟨x - q x • v, by
      change q (x - q x • v) = 0
      simp [hq]⟩, q x)
    invFun := fun p => (p.1 : X) + p.2 • v
    left_inv := by
      intro x
      exact sub_add_cancel x (q x • v)
    right_inv := by
      rintro ⟨p, t⟩
      apply Prod.ext
      · apply Subtype.ext
        have hp : q (p : X) = 0 := p.property
        change (p : X) + t • v - q ((p : X) + t • v) • v = (p : X)
        simp [hq, hp]
      · have hp : q (p : X) = 0 := p.property
        change q ((p : X) + t • v) = t
        simp [hq, hp]
    map_add' := by
      intro x y
      apply Prod.ext
      · apply Subtype.ext
        change x + y - q (x + y) • v = (x - q x • v) + (y - q y • v)
        rw [map_add, add_smul]
        abel
      · exact map_add q x y
    map_smul' := by
      intro a x
      apply Prod.ext
      · apply Subtype.ext
        change a • x - q (a • x) • v = a • (x - q x • v)
        rw [map_smul, smul_sub, smul_smul]
        simp only [smul_eq_mul]
      · exact map_smul q a x }

theorem poleBranchLinearSplit_symm_apply
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    (q : X →L[ℂ] ℂ) (v : X) (hq : q v = 1) (p : q.ker × ℂ) :
    (poleBranchLinearSplit q v hq).symm p = (p.1 : X) + p.2 • v := rfl

def poleBranchHyperplaneHeight
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (q ℓ : X →L[ℂ] ℂ) (v : X) : q.ker →L[ℂ] ℂ :=
  (-(ℓ v)⁻¹) • (ℓ.comp q.ker.subtypeL)

theorem poleBranchHyperplaneHeight_zero_iff
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (q ℓ : X →L[ℂ] ℂ) (v : X) (hv : ℓ v ≠ 0) (p : q.ker × ℂ) :
    ℓ ((p.1 : X) + p.2 • v) = 0 ↔ p.2 = poleBranchHyperplaneHeight q ℓ v p.1 := by
  simp only [map_add, map_smul, smul_eq_mul, poleBranchHyperplaneHeight,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  constructor
  · intro h
    apply (mul_right_cancel₀ hv)
    field_simp
    linear_combination h
  · intro h
    rw [h]
    field_simp
    ring

end RepulsiveCoulomb
