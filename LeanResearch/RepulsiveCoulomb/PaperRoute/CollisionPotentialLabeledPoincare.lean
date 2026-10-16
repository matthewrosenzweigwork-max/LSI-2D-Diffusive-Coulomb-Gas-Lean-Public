module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.PairDiracLabeledPoincare
public import LeanResearch.RepulsiveCoulomb.CoulombLeviQuadratic

@[expose] public section

/-! Additive original-paper producer. Actual finite Vandermonde log decomposition and the singular
part of the original potential's distributional Laplacian. The totalized
logarithm is used only through an equality a.e. off the collision union. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

def paperPairCollisionMeasure {N : ℕ} (i j : Fin (N + 2)) : Measure (CoulombConfig (N + 2)) :=
  if hij : i ≠ j then paperPairNormalDirac i j hij else 0

theorem paperPairCollisionMeasure_of_ne {N : ℕ} (i j : Fin (N + 2)) (hij : i ≠ j) :
    paperPairCollisionMeasure i j = paperPairNormalDirac i j hij := by
  rw [paperPairCollisionMeasure, dite_eq_left hij]

theorem paper_vandermonde_log_ae (N : ℕ) :
    (fun z : CoulombConfig N => Real.log ‖coulombVandermonde z‖) =ᵐ[volume]
      (fun z => ∑ p ∈ coulombPairs N, Real.log ‖z p.1 - z p.2‖) := by
  filter_upwards [coulombDomain_ae N] with z hz
  have hne := (coulombVandermonde_ne_zero_iff z).mp hz
  rw [coulombVandermonde, norm_prod]
  exact Real.log_prod (fun p hp => norm_ne_zero_iff.mpr
    (sub_ne_zero.mpr (hne p.1 p.2 (ne_of_lt ((mem_coulombPairs p).mp hp)))))

theorem paper_vandermonde_collision_pairing {N : ℕ}
    {φ : CoulombConfig (N + 2) → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z : CoulombConfig (N + 2) => Real.log ‖coulombVandermonde z‖ * Laplacian.laplacian φ z) ∧
    (∫ z : CoulombConfig (N + 2), Real.log ‖coulombVandermonde z‖ * Laplacian.laplacian φ z) =
      (2 * Real.pi) * ∑ p ∈ coulombPairs (N + 2), ∫ z, φ z ∂paperPairCollisionMeasure p.1 p.2 := by
  have hp (p : Fin (N + 2) × Fin (N + 2)) (hp : p ∈ coulombPairs (N + 2)) :=
    paper_pair_collision_dirac p.1 p.2 (ne_of_lt ((mem_coulombPairs p).mp hp)) hφ hφc
  have hi (p : Fin (N + 2) × Fin (N + 2)) (hmem : p ∈ coulombPairs (N + 2)) := (hp p hmem).1
  have he : (fun z : CoulombConfig (N + 2) => Real.log ‖coulombVandermonde z‖ * Laplacian.laplacian φ z) =ᵐ[volume]
      (fun z => ∑ p ∈ coulombPairs (N + 2), Real.log ‖z p.1 - z p.2‖ * Laplacian.laplacian φ z) := by
    filter_upwards [paper_vandermonde_log_ae (N + 2)] with z hz
    rw [hz, Finset.sum_mul]
  have hsum := integrable_finsetSum (coulombPairs (N + 2)) hi
  refine ⟨hsum.congr he.symm, ?_⟩
  rw [integral_congr_ae he, integral_finsetSum _ hi, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hmem
  rw [paperPairCollisionMeasure_of_ne p.1 p.2 (ne_of_lt ((mem_coulombPairs p).mp hmem))]
  exact (hp p hmem).2.2

/-- Exact singular distributional part of -1/2 Delta U after the explicit
smooth Gaussian confinement term is removed. The unit-normal mass is pi*aN. -/
theorem paper_coulomb_singular_distribution {N : ℕ} (β : ℝ)
    {φ : CoulombConfig (N + 2) → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z : CoulombConfig (N + 2) =>
      (coulombPotential β z - (β / 2) * ‖z‖ ^ 2) * Laplacian.laplacian φ z) ∧
    -(1 / 2 : ℝ) * (∫ z : CoulombConfig (N + 2),
      (coulombPotential β z - (β / 2) * ‖z‖ ^ 2) * Laplacian.laplacian φ z) =
      (Real.pi * (β / (N + 2 : ℕ))) *
        ∑ p ∈ coulombPairs (N + 2), ∫ z, φ z ∂paperPairCollisionMeasure p.1 p.2 := by
  obtain ⟨hi, he⟩ := paper_vandermonde_collision_pairing hφ hφc
  have hfun : (fun z : CoulombConfig (N + 2) =>
      (coulombPotential β z - (β / 2) * ‖z‖ ^ 2) * Laplacian.laplacian φ z) =
      (fun z => -(β / (N + 2 : ℕ)) *
        (Real.log ‖coulombVandermonde z‖ * Laplacian.laplacian φ z)) := by
    funext z
    unfold coulombPotential
    ring
  rw [hfun]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul, he]
  ring

/-- Nonnegativity of the actual singular measure tested on nonnegative compact tests. -/
theorem paper_coulomb_singular_nonnegative {N : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    {φ : CoulombConfig (N + 2) → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ z, 0 ≤ φ z) :
    0 ≤ -(1 / 2 : ℝ) * (∫ z : CoulombConfig (N + 2),
      (coulombPotential β z - (β / 2) * ‖z‖ ^ 2) * Laplacian.laplacian φ z) := by
  rw [(paper_coulomb_singular_distribution β hφ hφc).2]
  exact mul_nonneg (mul_nonneg Real.pi_pos.le (div_nonneg hβ (by positivity)))
    (Finset.sum_nonneg (fun _ _ => integral_nonneg hφ0))

/-- Generic compact-test Green symmetry for the actual physical configuration Laplacian. -/
theorem collision_integral_mul_laplacian_eq {M : ℕ} {f φ : CoulombConfig M → ℝ}
    (hf : ContDiff ℝ 2 f) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ z, f z * Laplacian.laplacian φ z) =
      ∫ z, Laplacian.laplacian f z * φ z := by
  let b := stdOrthonormalBasis ℝ (CoulombConfig M)
  have hiL (i : Fin (Module.finrank ℝ (CoulombConfig M))) :
      Integrable (fun z => f z * fderiv ℝ (fun x => fderiv ℝ φ x (b i)) z (b i)) :=
    (hf.continuous.mul (CollisionCalculus.continuous_second_fderiv_apply hφ _ _)).integrable_of_hasCompactSupport
      ((hφc.fderiv_apply ℝ (b i)).fderiv_apply ℝ (b i)).mul_left
  have hiR (i : Fin (Module.finrank ℝ (CoulombConfig M))) :
      Integrable (fun z => fderiv ℝ (fun x => fderiv ℝ f x (b i)) z (b i) * φ z) :=
    ((CollisionCalculus.continuous_second_fderiv_apply hf _ _).mul hφ.continuous).integrable_of_hasCompactSupport
      hφc.mul_left
  rw [CollisionCalculus.laplacian_eq_second_fderiv_basis hφ b,
    CollisionCalculus.laplacian_eq_second_fderiv_basis hf b]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => hiL i), integral_finsetSum _ (fun i _ => hiR i)]
  exact Finset.sum_congr rfl (fun i _ => CollisionCalculus.integral_mul_second_fderiv_eq hf hφ hφc (b i))

theorem collision_norm_sq_second {M : ℕ} (z v : CoulombConfig M) :
    collisionSecondDirection (fun x : CoulombConfig M => ‖x‖ ^ 2) v z = 2 * ‖v‖ ^ 2 := by
  have he (x : CoulombConfig M) :
      fderiv ℝ (fun y : CoulombConfig M => ‖y‖ ^ 2) x v = 2 * inner ℝ v x := by
    rw [(hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv]
    simp only [smul_apply, innerSL_apply_apply, nsmul_eq_mul, real_inner_comm, Nat.cast_ofNat]
  unfold collisionSecondDirection
  simp_rw [he]
  have hd := ((innerSL ℝ v).hasFDerivAt (x := z)).const_mul (2 : ℝ)
  have hdf := hd.fderiv
  change fderiv ℝ (fun x => (2 : ℝ) * inner ℝ v x) z = _ at hdf
  rw [hdf]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, real_inner_self_eq_norm_sq]

theorem collision_norm_sq_laplacian (M : ℕ) (z : CoulombConfig M) :
    Laplacian.laplacian (fun x : CoulombConfig M => ‖x‖ ^ 2) z = 4 * (M : ℝ) := by
  have hf : ContDiff ℝ 2 (fun x : CoulombConfig M => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  rw [collisionConfig_laplacian_sum hf]
  simp only [collision_norm_sq_second, coulombCoordinateInjection_norm,
    Complex.orthonormalBasisOneI.norm_eq_one, one_pow, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem collision_gaussian_pairing {M : ℕ} (β : ℝ)
    {φ : CoulombConfig M → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z => ((β / 2) * ‖z‖ ^ 2) * Laplacian.laplacian φ z) ∧
    (∫ z : CoulombConfig M, ((β / 2) * ‖z‖ ^ 2) * Laplacian.laplacian φ z) =
      (2 * β * (M : ℝ)) * ∫ z, φ z := by
  have hn : ContDiff ℝ 2 (fun z : CoulombConfig M => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
  have hi : Integrable (fun z : CoulombConfig M => ‖z‖ ^ 2 * Laplacian.laplacian φ z) :=
    (hn.continuous.mul (CollisionCalculus.continuous_laplacian hφ)).integrable_of_hasCompactSupport
      (CollisionCalculus.hasCompactSupport_laplacian hφ hφc).mul_left
  have he := collision_integral_mul_laplacian_eq hn hφ hφc
  simp_rw [collision_norm_sq_laplacian] at he
  rw [integral_const_mul] at he
  have hfun : (fun z : CoulombConfig M => ((β / 2) * ‖z‖ ^ 2) * Laplacian.laplacian φ z) =
      (fun z => (β / 2) * (‖z‖ ^ 2 * Laplacian.laplacian φ z)) := by funext z; ring
  rw [hfun]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul, he]
  ring

/-- Full canonical distributional formula, with both the smooth -beta*N term
and the nonnegative unit-normal collision Dirac contribution. -/
theorem paper_coulomb_potential_distribution {N : ℕ} (β : ℝ)
    {φ : CoulombConfig (N + 2) → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z : CoulombConfig (N + 2) => coulombPotential β z * Laplacian.laplacian φ z) ∧
    -(1 / 2 : ℝ) * (∫ z : CoulombConfig (N + 2), coulombPotential β z * Laplacian.laplacian φ z) =
      -β * (N + 2 : ℕ) * (∫ z, φ z) + (Real.pi * (β / (N + 2 : ℕ))) *
        ∑ p ∈ coulombPairs (N + 2), ∫ z, φ z ∂paperPairCollisionMeasure p.1 p.2 := by
  obtain ⟨hiS, hS⟩ := paper_coulomb_singular_distribution β hφ hφc
  obtain ⟨hiG, hG⟩ := collision_gaussian_pairing β hφ hφc
  have he : (fun z : CoulombConfig (N + 2) => coulombPotential β z * Laplacian.laplacian φ z) =
      (fun z => (coulombPotential β z - (β / 2) * ‖z‖ ^ 2) * Laplacian.laplacian φ z +
        ((β / 2) * ‖z‖ ^ 2) * Laplacian.laplacian φ z) := by funext z; ring
  rw [he]
  refine ⟨hiS.add hiG, ?_⟩
  rw [integral_add hiS hiG, hG]
  nlinarith only [hS]

end RepulsiveCoulomb.PaperRoute
