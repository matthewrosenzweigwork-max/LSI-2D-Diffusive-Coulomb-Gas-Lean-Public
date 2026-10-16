module

public import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryJointData

@[expose] public section

/-! Coefficients of C div(Aw) in nondivergence form. The lower coefficient
is C times the derivative of A; derivatives of C belong to the weak product
rule and cancel when the combined system is written in nondivergence form. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace RepulsiveCoulomb

def dbarOutputSystemPrincipal {N : ℕ} {ι κ η δ : Type*} [Fintype κ]
    (A : κ → ι → δ → CoulombConfig N → ℂ)
    (C : η → κ → CoulombConfig N → ℂ)
    (q : η) (b : ι) (d : δ) (z : CoulombConfig N) : ℂ :=
  ∑ a, C q a z * A a b d z

def dbarOutputSystemLower {N : ℕ} {ι κ η δ : Type*} [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → CoulombConfig N → ℂ)
    (C : η → κ → CoulombConfig N → ℂ) (v : δ → CoulombConfig N)
    (q : η) (b : ι) (z : CoulombConfig N) : ℂ :=
  ∑ a, ∑ d, C q a z * fderiv ℝ (A a b d) z (v d)

theorem dbarOutputSystemPrincipal_contDiffAt {N : ℕ} {ι κ η δ : Type*} [Fintype κ]
    (A : κ → ι → δ → CoulombConfig N → ℂ)
    (C : η → κ → CoulombConfig N → ℂ)
    (hA : ∀ a b d z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (A a b d) z)
    (hC : ∀ q a z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (C q a) z)
    (q : η) (b : ι) (d : δ) {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    ContDiffAt ℝ (⊤ : ℕ∞) (dbarOutputSystemPrincipal A C q b d) z := by
  apply ContDiffAt.sum
  intro a _
  exact (hC q a z hz).mul (hA a b d z hz)

theorem dbarOutputSystemLower_contDiffAt {N : ℕ} {ι κ η δ : Type*}
    [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → CoulombConfig N → ℂ)
    (C : η → κ → CoulombConfig N → ℂ) (v : δ → CoulombConfig N)
    (hA : ∀ a b d z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (A a b d) z)
    (hC : ∀ q a z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (C q a) z)
    (q : η) (b : ι) {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    ContDiffAt ℝ (⊤ : ℕ∞) (dbarOutputSystemLower A C v q b) z := by
  apply ContDiffAt.sum
  intro a _
  apply ContDiffAt.sum
  intro d _
  exact (hC q a z hz).mul
    (((hA a b d z hz).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const)

theorem dbarOutputSystemPrincipal_fderiv {N : ℕ} {ι κ η δ : Type*} [Fintype κ]
    (A : κ → ι → δ → CoulombConfig N → ℂ)
    (C : η → κ → CoulombConfig N → ℂ)
    (hA : ∀ a b d z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (A a b d) z)
    (hC : ∀ q a z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (C q a) z)
    (q : η) (b : ι) (d : δ) {z : CoulombConfig N} (hz : z ∈ coulombDomain N)
    (v : CoulombConfig N) :
    fderiv ℝ (dbarOutputSystemPrincipal A C q b d) z v =
      ∑ a, (C q a z * fderiv ℝ (A a b d) z v + A a b d z * fderiv ℝ (C q a) z v) := by
  have hc (a : κ) := (hC q a z hz).differentiableAt (by simp)
  have ha (a : κ) := (hA a b d z hz).differentiableAt (by simp)
  have hprod (a : κ) : DifferentiableAt ℝ
      (fun x : CoulombConfig N => C q a x * A a b d x) z := (hc a).mul (ha a)
  unfold dbarOutputSystemPrincipal
  rw [fderiv_fun_sum (u := Finset.univ) (fun a _ => hprod a)]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [fderiv_fun_mul (hc a) (ha a)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

def coulombAuxiliaryJointPrincipal {N : ℕ} (β : ℝ) :=
  dbarOutputSystemPrincipal (coulombAuxiliaryRawSystemPrincipal (N := N) β)
    (coulombAuxiliaryOutputMultiplier β)

def coulombAuxiliaryJointLower {N : ℕ} (β : ℝ) :=
  dbarOutputSystemLower (coulombAuxiliaryRawSystemPrincipal (N := N) β)
    (coulombAuxiliaryOutputMultiplier β) (dbarSystemDirection N)

theorem coulombAuxiliaryRawSystemPrincipal_contDiffAt {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (a : CoulombAuxiliaryRawIndex N) (b : Fin N) (d : Fin N × Bool)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    ContDiffAt ℝ (⊤ : ℕ∞) (coulombAuxiliaryRawSystemPrincipal β a b d) z := by
  cases a with
  | none => exact coulombAuxiliaryScalarDensityPrincipal_contDiffAt b d hz
  | some p => exact coulombAuxiliaryRawCurlDensityPrincipal_contDiffAt hβ p.1 p.2 b d hz

theorem coulombAuxiliaryJointPrincipal_contDiffAt {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (q : CoulombAuxiliaryJointIndex N) (b : Fin N) (d : Fin N × Bool)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    ContDiffAt ℝ (⊤ : ℕ∞) (coulombAuxiliaryJointPrincipal β q b d) z :=
  dbarOutputSystemPrincipal_contDiffAt _ _
    (fun a b d z hz => coulombAuxiliaryRawSystemPrincipal_contDiffAt hβ a b d hz)
    (fun q a z hz => coulombAuxiliaryOutputMultiplier_contDiffAt hβ q a hz) q b d hz

theorem coulombAuxiliaryJointLower_contDiffAt {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (q : CoulombAuxiliaryJointIndex N) (b : Fin N)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    ContDiffAt ℝ (⊤ : ℕ∞) (coulombAuxiliaryJointLower β q b) z :=
  dbarOutputSystemLower_contDiffAt _ _ _
    (fun a b d z hz => coulombAuxiliaryRawSystemPrincipal_contDiffAt hβ a b d hz)
    (fun q a z hz => coulombAuxiliaryOutputMultiplier_contDiffAt hβ q a hz) q b hz

end RepulsiveCoulomb
