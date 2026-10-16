import LeanResearch.RepulsiveCoulomb.PaperRoute.CollisionNormalLabeledPoincare
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-! Additive original-paper producer. The literal physical Laplacian splits into the two real
normal directions and the remaining tangential Euclidean directions. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

private theorem collision_second_iterated {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (z v w : E) :
    fderiv ℝ (fun x => fderiv ℝ φ x v) z w = iteratedFDeriv ℝ 2 φ z ![w,v] := by
  rw [fderiv_clm_apply ((hφ.fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num) z) (differentiableAt_const v)]
  simp [iteratedFDeriv_two_apply]

def collisionSecondDirection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E → ℝ) (v : E) (z : E) : ℝ := fderiv ℝ (fun x => fderiv ℝ φ x v) z v

theorem collisionSecondDirection_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (v : E) : Continuous (collisionSecondDirection φ v) := by
  have hd : ContDiff ℝ 1 (fun x => fderiv ℝ φ x v) :=
    (hφ.fderiv_right (by norm_num)).clm_apply contDiff_const
  exact (hd.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem collisionSecondDirection_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} (hφc : HasCompactSupport φ) (v : E) : HasCompactSupport (collisionSecondDirection φ v) :=
  (hφc.fderiv_apply ℝ v).fderiv_apply ℝ v

def collisionNormalLaplacian {N : ℕ} (φ : CoulombConfig (N + 1) → ℝ)
    (z : CoulombConfig (N + 1)) : ℝ :=
  ∑ a : Fin 2, collisionSecondDirection φ
    (coulombCoordinateInjection (N + 1) 0 (Complex.orthonormalBasisOneI a)) z

def collisionTangentLaplacian {N : ℕ} (φ : CoulombConfig (N + 1) → ℝ)
    (z : CoulombConfig (N + 1)) : ℝ :=
  ∑ j : Fin N, ∑ a : Fin 2, collisionSecondDirection φ
    (coulombCoordinateInjection (N + 1) j.succ (Complex.orthonormalBasisOneI a)) z

theorem collisionConfig_laplacian_sum {N : ℕ} {φ : CoulombConfig N → ℝ}
    (hφ : ContDiff ℝ 2 φ) (z : CoulombConfig N) :
    Laplacian.laplacian φ z = ∑ j : Fin N, ∑ a : Fin 2,
      collisionSecondDirection φ (coulombCoordinateInjection N j (Complex.orthonormalBasisOneI a)) z := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis φ
    (Pi.orthonormalBasis (fun _ : Fin N => Complex.orthonormalBasisOneI))]
  simp only [Pi.orthonormalBasis_apply, Fintype.sum_sigma]
  simp only [collisionSecondDirection, collision_second_iterated hφ,
    coulombCoordinateInjection_eq_single]

theorem collisionConfig_laplacian_split {N : ℕ} {φ : CoulombConfig (N + 1) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (z : CoulombConfig (N + 1)) :
    Laplacian.laplacian φ z = collisionNormalLaplacian φ z + collisionTangentLaplacian φ z := by
  rw [collisionConfig_laplacian_sum hφ, Fin.sum_univ_succ]
  rfl

theorem collisionNormalLaplacian_continuous {N : ℕ} {φ : CoulombConfig (N + 1) → ℝ}
    (hφ : ContDiff ℝ 2 φ) : Continuous (collisionNormalLaplacian φ) :=
  continuous_finsetSum _ (fun _ _ => collisionSecondDirection_continuous hφ _)

theorem collisionTangentLaplacian_continuous {N : ℕ} {φ : CoulombConfig (N + 1) → ℝ}
    (hφ : ContDiff ℝ 2 φ) : Continuous (collisionTangentLaplacian φ) :=
  continuous_finsetSum _ (fun _ _ => continuous_finsetSum _
    (fun _ _ => collisionSecondDirection_continuous hφ _))

theorem collisionNormalLaplacian_compact {N : ℕ} {φ : CoulombConfig (N + 1) → ℝ}
    (hφc : HasCompactSupport φ) : HasCompactSupport (collisionNormalLaplacian φ) := by
  have he : collisionNormalLaplacian φ =
      ∑ a : Fin 2, collisionSecondDirection φ
        (coulombCoordinateInjection (N + 1) 0 (Complex.orthonormalBasisOneI a)) := by
    funext z
    rw [Finset.sum_apply]
    rfl
  rw [he]
  exact HasCompactSupport.finset_sum (fun a _ => collisionSecondDirection_compact hφc
    (coulombCoordinateInjection (N + 1) 0 (Complex.orthonormalBasisOneI a)))

theorem collisionTangentLaplacian_compact {N : ℕ} {φ : CoulombConfig (N + 1) → ℝ}
    (hφc : HasCompactSupport φ) : HasCompactSupport (collisionTangentLaplacian φ) := by
  have he : collisionTangentLaplacian φ =
      ∑ j : Fin N, ∑ a : Fin 2, collisionSecondDirection φ
        (coulombCoordinateInjection (N + 1) j.succ (Complex.orthonormalBasisOneI a)) := by
    funext z
    simp only [Finset.sum_apply]
    rfl
  rw [he]
  exact HasCompactSupport.finset_sum (fun j _ => HasCompactSupport.finset_sum
    (fun a _ => collisionSecondDirection_compact hφc
      (coulombCoordinateInjection (N + 1) j.succ (Complex.orthonormalBasisOneI a))))

/-- Genuine Hessian chain rule under an affine coordinate insertion. -/
theorem collision_second_affine_chain
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (a : F) {φ : F → ℝ} (hφ : ContDiff ℝ 2 φ) (x v w : E) :
    iteratedFDeriv ℝ 2 (fun z => φ (L z + a)) x ![v,w] =
      iteratedFDeriv ℝ 2 φ (L x + a) ![L v,L w] := by
  have ht : ContDiff ℝ 2 (fun z : F => φ (z + a)) := hφ.comp (contDiff_id.add contDiff_const)
  change iteratedFDeriv ℝ 2 ((fun z : F => φ (z + a)) ∘ L) x ![v,w] = _
  rw [L.iteratedFDeriv_comp_right ht x (by norm_num)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_comp_add_right]
  congr 1
  ext k
  fin_cases k <;> rfl

theorem collision_normal_trace_slice {N : ℕ} {φ : CoulombConfig (N + 1) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (u : ℂ) (y : CoulombConfig N) :
    collisionNormalLaplacian φ (coulombInsertZero u y) =
      Laplacian.laplacian (fun w : ℂ => φ (coulombInsertZero w y)) u := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ Complex.orthonormalBasisOneI]
  apply Finset.sum_congr rfl
  intro a _
  change collisionSecondDirection φ
    (coulombCoordinateInjection (N + 1) 0 (Complex.orthonormalBasisOneI a))
    (coulombInsertZero u y) = _
  rw [collisionSecondDirection, collision_second_iterated hφ]
  have he : (fun w : ℂ => φ (coulombInsertZero w y)) =
      (fun w => φ (coulombCoordinateInjection (N + 1) 0 w + coulombInsertZero 0 y)) := by
    funext w
    rw [coulombInsertZero_affine]
  rw [he, collision_second_affine_chain _ _ hφ]
  rw [← coulombInsertZero_affine]

def collisionTailInjection (N : ℕ) : CoulombConfig N →L[ℝ] CoulombConfig (N + 1) where
  toFun := coulombInsertZero 0
  map_add' x y := by
    ext k
    exact Fin.cases (by change (0 : ℂ) = 0 + 0; simp) (fun _ => rfl) k
  map_smul' c x := by
    ext k
    exact Fin.cases (by change (0 : ℂ) = c • (0 : ℂ); simp) (fun _ => rfl) k
  cont := (cylindrical_tangent_insert_isometry 0).continuous

theorem collision_tangent_insert_affine {N : ℕ} (u : ℂ) (y : CoulombConfig N) :
    coulombInsertZero u y = collisionTailInjection N y + coulombInsertZero u 0 := by
  ext k
  exact Fin.cases (by change u = 0 + u; simp)
    (fun j => by change y j = y j + 0; simp) k

theorem collision_tangent_insert_contDiff {N : ℕ} (u : ℂ) :
    ContDiff ℝ 2 (fun y : CoulombConfig N => coulombInsertZero u y) := by
  have he : (fun y : CoulombConfig N => coulombInsertZero u y) =
      fun y => collisionTailInjection N y + coulombInsertZero u 0 := funext (collision_tangent_insert_affine u)
  rw [he]
  exact (collisionTailInjection N).contDiff.add contDiff_const

theorem collision_tangent_injection_direction {N : ℕ} (j : Fin N) (a : ℂ) :
    collisionTailInjection N (coulombCoordinateInjection N j a) =
      coulombCoordinateInjection (N + 1) j.succ a := by
  ext k
  refine Fin.cases ?_ (fun l => ?_) k
  · change (0 : ℂ) = (EuclideanSpace.single j.succ a) 0
    simp
  · change (EuclideanSpace.single j a) l = (EuclideanSpace.single j.succ a) l.succ
    simp [PiLp.single_apply]

theorem collision_tangent_trace_slice {N : ℕ} {φ : CoulombConfig (N + 1) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (u : ℂ) (y : CoulombConfig N) :
    collisionTangentLaplacian φ (coulombInsertZero u y) =
      Laplacian.laplacian (fun ξ : CoulombConfig N => φ (coulombInsertZero u ξ)) y := by
  have hs : ContDiff ℝ 2 (fun ξ : CoulombConfig N => φ (coulombInsertZero u ξ)) :=
    hφ.comp (collision_tangent_insert_contDiff u)
  rw [collisionConfig_laplacian_sum hs]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  simp only [collisionSecondDirection, collision_second_iterated hφ, collision_second_iterated hs]
  have he : (fun ξ : CoulombConfig N => φ (coulombInsertZero u ξ)) =
      (fun ξ => φ (collisionTailInjection N ξ + coulombInsertZero u 0)) := by
    funext ξ
    rw [collision_tangent_insert_affine]
  rw [he, collision_second_affine_chain _ _ hφ,
    collision_tangent_injection_direction, ← collision_tangent_insert_affine]

end RepulsiveCoulomb.PaperRoute
