import LeanResearch.RepulsiveCoulomb.CoulombCenterRelativeForm
import LeanResearch.RepulsiveCoulomb.CoulombCenterCylinderTests

/-! Genuine isometric embedding of the closed relative physical graph into the
original full form. In particular, closability of the relative form is proved
from original-form injectivity; it is not presumed in the relative definition. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

variable {n : ℕ}

def coulombCenterRelativeJetFiber (e : CoulombCenterRotation n) :
    TauCeti.Sobolev1Jet (CoulombConfig n) →ₗᵢ[ℝ] TauCeti.Sobolev1Jet (CoulombConfig (n + 1)) :=
  LinearIsometry.withLpProdMap 2 (LinearIsometry.id : ℝ →ₗᵢ[ℝ] ℝ)
    (e.symm.toLinearIsometry.comp (coulombCenterRelativeInjection n))

theorem coulombCenterRelativeJetFiber_apply (e : CoulombCenterRotation n)
    (q : TauCeti.Sobolev1Jet (CoulombConfig n)) :
    coulombCenterRelativeJetFiber e q =
      WithLp.toLp 2 (WithLp.fst q, e.symm (coulombCenterRelativeInjection n (WithLp.snd q))) := rfl

def coulombCenterRelativeJetLiftL (e : CoulombCenterRotation n) (he : CoulombCenterAxis e)
    {β : ℝ} (hβ : 0 < β) : CoulombCenterRelativeJetL2 e β →L[ℝ] CoulombJetL2 (n + 1) β :=
  ((coulombCenterRelativeJetFiber e).toContinuousLinearMap.compLpL 2 (coulombMeasure (n + 1) β)).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (coulombCenterRelativeProjection e)
      (coulombCenterRelativeProjection_measurePreserving e he hβ)).toContinuousLinearMap

theorem coulombCenterRelativeJetLiftL_coe (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) (J : CoulombCenterRelativeJetL2 e β) :
    coulombCenterRelativeJetLiftL e he hβ J =ᵐ[coulombMeasure (n + 1) β] fun z =>
      coulombCenterRelativeJetFiber e (J (coulombCenterRelativeProjection e z)) := by
  let T := Lp.compMeasurePreservingₗᵢ (E := TauCeti.Sobolev1Jet (CoulombConfig n))
    (p := 2) ℝ (coulombCenterRelativeProjection e)
    (coulombCenterRelativeProjection_measurePreserving e he hβ)
  filter_upwards [(coulombCenterRelativeJetFiber e).toContinuousLinearMap.coeFn_compLpL (T J),
    Lp.coeFn_compMeasurePreserving J (coulombCenterRelativeProjection_measurePreserving e he hβ)]
    with z hm ht
  change ((coulombCenterRelativeJetFiber e).toContinuousLinearMap.compLpL
    2 (coulombMeasure (n + 1) β) (T J)) z = _
  rw [hm]
  change coulombCenterRelativeJetFiber e (T J z) = _
  change T J z = J (coulombCenterRelativeProjection e z) at ht
  rw [ht]

theorem coulombCenterRelativeJetLiftL_norm (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) (J : CoulombCenterRelativeJetL2 e β) :
    ‖coulombCenterRelativeJetLiftL e he hβ J‖ = ‖J‖ := by
  have hs : ‖coulombCenterRelativeJetLiftL e he hβ J‖ ^ 2 = ‖J‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (coulombCenterRelativeJetLiftL e he hβ J), L2.inner_def,
      ← real_inner_self_eq_norm_sq J, L2.inner_def]
    calc
      _ = ∫ z, inner ℝ (J (coulombCenterRelativeProjection e z))
          (J (coulombCenterRelativeProjection e z)) ∂coulombMeasure (n + 1) β := by
        apply integral_congr_ae
        filter_upwards [coulombCenterRelativeJetLiftL_coe e he hβ J] with z hz
        rw [hz, (coulombCenterRelativeJetFiber e).inner_map_map]
      _ = _ := by
        have hp := coulombCenterRelativeProjection_measurePreserving e he hβ
        have hm : AEStronglyMeasurable (fun r => inner ℝ (J r) (J r))
            ((coulombMeasure (n + 1) β).map (coulombCenterRelativeProjection e)) := by
          rw [hp.map_eq]
          exact (L2.integrable_inner J J).aestronglyMeasurable
        have h := integral_map hp.measurable.aemeasurable hm
        rw [hp.map_eq] at h
        exact h.symm
  nlinarith [norm_nonneg (coulombCenterRelativeJetLiftL e he hβ J), norm_nonneg J]

theorem coulombCenterRelativeJetLiftL_value (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) (J : CoulombCenterRelativeJetL2 e β) :
    coulombJetValueL (n + 1) β (coulombCenterRelativeJetLiftL e he hβ J) =
      Lp.compMeasurePreserving (coulombCenterRelativeProjection e)
        (coulombCenterRelativeProjection_measurePreserving e he hβ)
        (coulombCenterRelativeJetValueL e β J) := by
  have hrel := (WithLp.fstL 2 ℝ ℝ (CoulombConfig n)).coeFn_compLp J
  have hp := (coulombCenterRelativeProjection_measurePreserving e he hβ).quasiMeasurePreserving.ae hrel
  apply Lp.ext
  filter_upwards [coulombJetValueL_coe (n + 1) β (coulombCenterRelativeJetLiftL e he hβ J),
    coulombCenterRelativeJetLiftL_coe e he hβ J,
    Lp.coeFn_compMeasurePreserving (coulombCenterRelativeJetValueL e β J)
      (coulombCenterRelativeProjection_measurePreserving e he hβ), hp] with z hv hl hc hr
  rw [hv, hl, coulombCenterRelativeJetFiber_apply, WithLp.toLp_fst, hc]
  exact hr.symm

theorem coulombCenterRelativeJetLiftL_core_mem (m : ℕ)
    (e : CoulombCenterRotation (m + 1)) (he : CoulombCenterAxis e)
    {β : ℝ} (hβ : 0 < β) (ψ : TestFunction (coulombCenterRelativeDomain e) ℝ ⊤) :
    coulombCenterRelativeJetLiftL e he hβ (coulombCenterRelativeCoreJet e he hβ ψ) ∈
      coulombCoreGraph (m + 2) hβ := by
  obtain ⟨u, hv, hg, henergy⟩ := coulombCenterRelativeCore_lift m e he hβ ψ
  have hp := (coulombCenterRelativeProjection_measurePreserving e he hβ).quasiMeasurePreserving.ae
    (coulombCenterRelativeCoreJet_coe e he hβ ψ)
  have hEq : coulombCenterRelativeJetLiftL e he hβ (coulombCenterRelativeCoreJet e he hβ ψ) =
      (u : CoulombJetL2 (m + 2) β) := by
    apply Lp.ext
    filter_upwards [coulombCenterRelativeJetLiftL_coe e he hβ
        (coulombCenterRelativeCoreJet e he hβ ψ), hp,
      coulombJetValueL_coe (m + 2) β (u : CoulombJetL2 (m + 2) β),
      coulombJetGradientL_coe (m + 2) β (u : CoulombJetL2 (m + 2) β), hv, hg]
      with z hl hc hvalue hgrad hvz hgz
    rw [hl, hc, coulombCenterRelativeJetFiber_apply]
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (CoulombConfig (m + 2))).injective
    apply Prod.ext
    · change ψ (coulombCenterRelativeProjection e z) = WithLp.fst ((u : CoulombJetL2 (m + 2) β) z)
      exact hvz.symm.trans hvalue
    · change e.symm (coulombCenterRelativeInjection (m + 1)
        (gradient (ψ : CoulombConfig (m + 1) → ℝ) (coulombCenterRelativeProjection e z))) =
          WithLp.snd ((u : CoulombJetL2 (m + 2) β) z)
      exact hgz.symm.trans hgrad
  rw [hEq, ← coe_coulombFormSubmodule]
  exact u.property

theorem coulombCenterRelativeJetLiftL_preserves_graph (m : ℕ)
    (e : CoulombCenterRotation (m + 1)) (he : CoulombCenterAxis e)
    {β : ℝ} (hβ : 0 < β) {J : CoulombCenterRelativeJetL2 e β}
    (hJ : J ∈ (coulombCenterRelativeFormSubmodule e he hβ : Set _)) :
    coulombCenterRelativeJetLiftL e he hβ J ∈ coulombCoreGraph (m + 2) hβ := by
  have hc : IsClosed ((coulombCenterRelativeJetLiftL e he hβ) ⁻¹' coulombCoreGraph (m + 2) hβ) :=
    isClosed_closure.preimage (coulombCenterRelativeJetLiftL e he hβ).continuous
  rw [coulombCenterRelativeFormSubmodule, Submodule.coe_closure, LinearMap.coe_range] at hJ
  apply closure_minimal ?_ hc hJ
  rintro K ⟨ψ, rfl⟩
  exact coulombCenterRelativeJetLiftL_core_mem m e he hβ ψ

/-- Relative weighted gradient closability, derived from the original closed
physical graph using the constructed bounded-smooth cylinder lifts. -/
theorem coulombCenterRelativeForm_value_eq_zero_iff (m : ℕ)
    (e : CoulombCenterRotation (m + 1)) (he : CoulombCenterAxis e)
    {β : ℝ} (hβ : 0 < β) (u : CoulombCenterRelativeFormDomain e he hβ) :
    coulombCenterRelativeFormValueL e he hβ u = 0 ↔ u = 0 := by
  constructor
  · intro hv
    have hJ := coulombCenterRelativeJetLiftL_preserves_graph m e he hβ u.property
    have hV : coulombJetValueL (m + 2) β
        (coulombCenterRelativeJetLiftL e he hβ (u : CoulombCenterRelativeJetL2 e β)) = 0 := by
      rw [coulombCenterRelativeJetLiftL_value]
      change Lp.compMeasurePreserving (coulombCenterRelativeProjection e)
        (coulombCenterRelativeProjection_measurePreserving e he hβ)
        (coulombCenterRelativeFormValueL e he hβ u) = 0
      rw [hv, map_zero]
    have hz := coulombCoreGraph_zero_of_value_zero hβ hJ hV
    have hn := coulombCenterRelativeJetLiftL_norm e he hβ (u : CoulombCenterRelativeJetL2 e β)
    rw [hz, norm_zero] at hn
    apply Subtype.ext
    exact norm_eq_zero.mp hn.symm
  · rintro rfl
    exact map_zero _

/-- The relative closed graph is therefore a genuine function-domain form. -/
theorem coulombCenterRelativeFormValueL_injective (m : ℕ)
    (e : CoulombCenterRotation (m + 1)) (he : CoulombCenterAxis e)
    {β : ℝ} (hβ : 0 < β) : Function.Injective (coulombCenterRelativeFormValueL e he hβ) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply (coulombCenterRelativeForm_value_eq_zero_iff m e he hβ (u - v)).mp
  rw [map_sub, huv, sub_self]

end RepulsiveCoulomb
