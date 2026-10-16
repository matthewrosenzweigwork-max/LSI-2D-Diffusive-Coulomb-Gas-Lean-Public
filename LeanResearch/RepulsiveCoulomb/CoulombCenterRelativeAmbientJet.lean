import LeanResearch.RepulsiveCoulomb.CoulombCenterRelativeEmbedding
import Mathlib.MeasureTheory.Integral.Average

/-! Ambient relative physical jets and the contractive projection of original
jets onto the relative value/gradient components. These are used to prove
relative common-core equality, rather than presuming that closability alone
removes the collision set. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

variable {n : ℕ}

theorem coulombCenterRelativeProjection_norm_le (e : CoulombCenterRotation n)
    (z : CoulombConfig (n + 1)) : ‖coulombCenterRelativeProjection e z‖ ≤ ‖z‖ := by
  rw [coulombCenterRelativeProjection_apply]
  have h := coulombInsertZero_norm_sq (e z 0) (coulombTail (e z))
  rw [coulombInsertZero_head_tail, e.norm_map] at h
  nlinarith [sq_nonneg ‖e z 0‖, norm_nonneg (coulombTail (e z)), norm_nonneg z]

def coulombCenterRelativeJetProjectLinear (e : CoulombCenterRotation n) :
    TauCeti.Sobolev1Jet (CoulombConfig (n + 1)) →ₗ[ℝ] TauCeti.Sobolev1Jet (CoulombConfig n) where
  toFun q := WithLp.toLp 2 (WithLp.fst q, coulombCenterRelativeProjection e (WithLp.snd q))
  map_add' p q := by
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (CoulombConfig n)).injective
    change (WithLp.fst (p + q), coulombCenterRelativeProjection e (WithLp.snd (p + q))) =
      (WithLp.fst p, coulombCenterRelativeProjection e (WithLp.snd p)) +
        (WithLp.fst q, coulombCenterRelativeProjection e (WithLp.snd q))
    apply Prod.ext
    · rfl
    · change coulombCenterRelativeProjection e (WithLp.snd p + WithLp.snd q) =
        coulombCenterRelativeProjection e (WithLp.snd p) + coulombCenterRelativeProjection e (WithLp.snd q)
      exact map_add _ _ _
  map_smul' a p := by
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (CoulombConfig n)).injective
    change (WithLp.fst (a • p), coulombCenterRelativeProjection e (WithLp.snd (a • p))) =
      a • (WithLp.fst p, coulombCenterRelativeProjection e (WithLp.snd p))
    apply Prod.ext
    · rfl
    · change coulombCenterRelativeProjection e (a • WithLp.snd p) =
        a • coulombCenterRelativeProjection e (WithLp.snd p)
      exact map_smul _ _ _

theorem coulombCenterRelativeJetProjectLinear_norm_le (e : CoulombCenterRotation n)
    (q : TauCeti.Sobolev1Jet (CoulombConfig (n + 1))) :
    ‖coulombCenterRelativeJetProjectLinear e q‖ ≤ ‖q‖ := by
  have h := coulombCenterRelativeProjection_norm_le e (WithLp.snd q)
  have hs := WithLp.prod_norm_sq_eq_of_L2 q
  have ht := WithLp.prod_norm_sq_eq_of_L2 (coulombCenterRelativeJetProjectLinear e q)
  change ‖coulombCenterRelativeJetProjectLinear e q‖ ^ 2 =
    ‖WithLp.fst q‖ ^ 2 + ‖coulombCenterRelativeProjection e (WithLp.snd q)‖ ^ 2 at ht
  nlinarith [norm_nonneg (coulombCenterRelativeJetProjectLinear e q), norm_nonneg q,
    norm_nonneg (coulombCenterRelativeProjection e (WithLp.snd q)), norm_nonneg (WithLp.snd q)]

def coulombCenterRelativeJetProject (e : CoulombCenterRotation n) :
    TauCeti.Sobolev1Jet (CoulombConfig (n + 1)) →L[ℝ] TauCeti.Sobolev1Jet (CoulombConfig n) :=
  (coulombCenterRelativeJetProjectLinear e).mkContinuous 1
    (fun q => by simpa only [one_mul] using coulombCenterRelativeJetProjectLinear_norm_le e q)

theorem coulombCenterRelativeJetProject_apply (e : CoulombCenterRotation n)
    (q : TauCeti.Sobolev1Jet (CoulombConfig (n + 1))) :
    coulombCenterRelativeJetProject e q =
      WithLp.toLp 2 (WithLp.fst q, coulombCenterRelativeProjection e (WithLp.snd q)) := rfl

theorem coulombCenterRelativeJetProject_fiber (e : CoulombCenterRotation n)
    (q : TauCeti.Sobolev1Jet (CoulombConfig n)) :
    coulombCenterRelativeJetProject e (coulombCenterRelativeJetFiber e q) = q := by
  rw [coulombCenterRelativeJetFiber_apply, coulombCenterRelativeJetProject_apply]
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (CoulombConfig n)).injective
  apply Prod.ext
  · rfl
  · change coulombCenterRelativeProjection e
      (e.symm (coulombCenterRelativeInjection n (WithLp.snd q))) = WithLp.snd q
    rw [coulombCenterRelativeProjection_apply, e.apply_symm_apply]
    ext j
    rfl

theorem coulombCenter_L2_norm_sq {A E : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure A} (v : Lp E 2 μ) : ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq v, L2.inner_def]
  exact integral_congr_ae (Eventually.of_forall (fun x => real_inner_self_eq_norm_sq (v x)))

def coulombCenterRelativeAmbientJet (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (⊤ : Opens (CoulombConfig n)) ℝ ⊤) : CoulombCenterRelativeJetL2 e β := by
  letI := coulombCenterRelativeMeasure_isProbability e he hβ
  have hv : MemLp (ψ : CoulombConfig n → ℝ) 2 (coulombCenterRelativeMeasure e β) :=
    ψ.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport
  have hg : MemLp (gradient (ψ : CoulombConfig n → ℝ)) 2 (coulombCenterRelativeMeasure e β) :=
    (TauCeti.continuous_gradient_testFunction ψ).memLp_of_hasCompactSupport
      (TauCeti.hasCompactSupport_gradient_testFunction ψ)
  have hj : MemLp (fun r => WithLp.toLp 2 (ψ r, gradient (ψ : CoulombConfig n → ℝ) r)) 2
      (coulombCenterRelativeMeasure e β) := by
    apply MemLp.of_fst_of_snd_prodLp
    exact ⟨by simpa only [WithLp.toLp_fst] using hv, by simpa only [WithLp.toLp_snd] using hg⟩
  exact hj.toLp _

theorem coulombCenterRelativeAmbientJet_coe (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (⊤ : Opens (CoulombConfig n)) ℝ ⊤) :
    coulombCenterRelativeAmbientJet e he hβ ψ =ᵐ[coulombCenterRelativeMeasure e β]
      fun r => WithLp.toLp 2 (ψ r, gradient (ψ : CoulombConfig n → ℝ) r) := by
  unfold coulombCenterRelativeAmbientJet
  exact MemLp.coeFn_toLp _

end RepulsiveCoulomb
