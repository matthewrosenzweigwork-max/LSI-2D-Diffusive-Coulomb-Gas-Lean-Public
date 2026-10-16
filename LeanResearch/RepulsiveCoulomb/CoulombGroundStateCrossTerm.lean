module

public import LeanResearch.RepulsiveCoulomb.CoulombGroundStateIBP

@[expose] public section

/-! Finite real orthonormal-basis aggregation of the actual ground-state
cross term. No integration-by-parts or integrability hypothesis is supplied. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped BigOperators
namespace RepulsiveCoulomb

theorem coulombPotential_component_hasFDerivAt {N : ℕ} (β : ℝ)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) (v : CoulombConfig N) :
    HasFDerivAt (fun x => fderiv ℝ (coulombPotential β) x v)
      ((fderiv ℝ (fderiv ℝ (coulombPotential β)) z).flip v) z := by
  have hU : ContDiffAt ℝ 2 (coulombPotential (N := N) β) z :=
    (coulombPotential_contDiffAt β hz).of_le (by simp)
  have hd := (hU.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  simpa only [ContinuousLinearMap.comp_zero, zero_add] using
    hd.hasFDerivAt.clm_apply (hasFDerivAt_const v z)

theorem coulombCore_potential_directional_cross_integrable {N : ℕ} (β : ℝ)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (v : CoulombConfig N) :
    Integrable (fun x : CoulombConfig N => φ x * fderiv ℝ (φ : CoulombConfig N → ℝ) x v *
      fderiv ℝ (coulombPotential β) x v) := by
  have h := TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn
    (coulombPotential_component_locallyIntegrable β v) (coulombCoreSquare φ) v
  have hi : Integrable (fun x : CoulombConfig N =>
      (2 * φ x * fderiv ℝ (φ : CoulombConfig N → ℝ) x v) *
        fderiv ℝ (coulombPotential β) x v) := by
    simpa only [coulombCoreSquare_lineDeriv, smul_eq_mul] using h
  convert! hi.const_mul (1 / 2 : ℝ) using 1
  funext x
  ring

theorem coulombCore_potential_directional_divergence_integrable {N : ℕ} (β : ℝ)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (v : CoulombConfig N) :
    Integrable (fun x : CoulombConfig N => φ x ^ 2 *
      fderiv ℝ (fun y => fderiv ℝ (coulombPotential β) y v) x v) := by
  have h := TauCeti.integrable_smul_of_locallyIntegrableOn
    (coulombPotential_component_derivative_locallyIntegrable β v v) (coulombCoreSquare φ)
  simpa only [coulombCoreSquare_apply, smul_eq_mul] using h

theorem coulombCore_potential_directional_cross_integral {N : ℕ} (β : ℝ)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (v : CoulombConfig N) :
    2 * (∫ x : CoulombConfig N, φ x * fderiv ℝ (φ : CoulombConfig N → ℝ) x v *
      fderiv ℝ (coulombPotential β) x v) =
      -(∫ x : CoulombConfig N, φ x ^ 2 *
        fderiv ℝ (fun y => fderiv ℝ (coulombPotential β) y v) x v) := by
  rw [← integral_const_mul]
  convert! coulombCoreSquare_potential_integrationByParts β φ v using 1
  congr 1
  funext x
  ring

theorem coulombCore_potential_cross_sum {N : ℕ} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (CoulombConfig N)) (β : ℝ)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (x : CoulombConfig N) :
    φ x * inner ℝ (gradient (φ : CoulombConfig N → ℝ) x) (gradient (coulombPotential β) x) =
      ∑ i, φ x * fderiv ℝ (φ : CoulombConfig N → ℝ) x (b i) *
        fderiv ℝ (coulombPotential β) x (b i) := by
  rw [← b.sum_inner_mul_inner, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← real_inner_comm (b i) (gradient (coulombPotential β) x),
    inner_gradient_left, inner_gradient_left]
  ring

theorem coulombCore_potential_cross_integrable {N : ℕ} (β : ℝ)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    Integrable (fun x : CoulombConfig N => φ x *
      inner ℝ (gradient (φ : CoulombConfig N → ℝ) x) (gradient (coulombPotential β) x)) := by
  let b := stdOrthonormalBasis ℝ (CoulombConfig N)
  have hi := integrable_finset_sum Finset.univ
    (fun i _ => coulombCore_potential_directional_cross_integrable β φ (b i))
  exact hi.congr (Eventually.of_forall fun x => (coulombCore_potential_cross_sum b β φ x).symm)

theorem coulombCore_potential_cross_integral {N : ℕ} (β : ℝ)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    (∫ x : CoulombConfig N, φ x *
      inner ℝ (gradient (φ : CoulombConfig N → ℝ) x) (gradient (coulombPotential β) x)) =
      -(N : ℝ) * β * (∫ x : CoulombConfig N, φ x ^ 2) := by
  let b := stdOrthonormalBasis ℝ (CoulombConfig N)
  let A := fun i x => φ x * fderiv ℝ (φ : CoulombConfig N → ℝ) x (b i) *
    fderiv ℝ (coulombPotential β) x (b i)
  let D := fun i x => φ x ^ 2 * fderiv ℝ (fun y => fderiv ℝ (coulombPotential β) y (b i)) x (b i)
  have hA (i) : Integrable (A i) := coulombCore_potential_directional_cross_integrable β φ (b i)
  have hD (i) : Integrable (D i) := coulombCore_potential_directional_divergence_integrable β φ (b i)
  have htrace (x : CoulombConfig N) (hx : x ∈ coulombDomain N) :
      (∑ i, fderiv ℝ (fun y => fderiv ℝ (coulombPotential β) y (b i)) x (b i)) = 2 * (N : ℝ) * β := by
    rw [← coulombPotential_laplacian β hx,
      laplacian_eq_iteratedFDeriv_orthonormalBasis (coulombPotential β) b]
    apply Finset.sum_congr rfl
    intro i _
    rw [(coulombPotential_component_hasFDerivAt β hx (b i)).fderiv]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      ContinuousLinearMap.flip_apply]
  have hpD (x : CoulombConfig N) : (∑ i, D i x) = (2 * (N : ℝ) * β) * φ x ^ 2 := by
    by_cases hx : x ∈ coulombDomain N
    · dsimp only [D]
      rw [← Finset.mul_sum, htrace x hx]
      ring
    · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hx (φ.tsupport_subset ht))
      simp [D, hz]
  have hAi : (∫ x : CoulombConfig N, φ x *
      inner ℝ (gradient (φ : CoulombConfig N → ℝ) x) (gradient (coulombPotential β) x)) =
      ∑ i, ∫ x, A i x := by
    rw [integral_congr_ae (Eventually.of_forall (coulombCore_potential_cross_sum b β φ))]
    exact integral_finsetSum _ (fun i _ => hA i)
  have hDi : (∑ i, ∫ x, D i x) = (2 * (N : ℝ) * β) * (∫ x : CoulombConfig N, φ x ^ 2) := by
    rw [← integral_finsetSum _ (fun i _ => hD i),
      integral_congr_ae (Eventually.of_forall hpD), integral_const_mul]
  have hsum : (∑ i, 2 * (∫ x, A i x)) = -(∑ i, ∫ x, D i x) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => coulombCore_potential_directional_cross_integral β φ (b i))
  rw [← Finset.mul_sum, ← hAi, hDi] at hsum
  linarith only [hsum]

end RepulsiveCoulomb
