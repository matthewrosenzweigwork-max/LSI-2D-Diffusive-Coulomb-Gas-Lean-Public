import LeanResearch.RepulsiveCoulomb.CoulombCenterTensorCore

/-! The relative domain is the literal closed graph of all collision-free
compactly supported smooth value/physical-gradient jets. Core and full-domain
LSI are proved equivalent by extended entropy lower semicontinuity. The
value-projection injectivity is a separate embedding theorem, not a hypothesis
or field in this definition. Records-only, not yet admitted to checking. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open PeriodicAttractiveLogGas
open scoped Topology ENNReal
namespace RepulsiveCoulomb

variable {n : ℕ}

abbrev CoulombCenterRelativeJetL2 (e : CoulombCenterRotation n) (β : ℝ) :=
  Lp (TauCeti.Sobolev1Jet (CoulombConfig n)) 2 (coulombCenterRelativeMeasure e β)

def coulombCenterRelativeJetValueL (e : CoulombCenterRotation n) (β : ℝ) :
    CoulombCenterRelativeJetL2 e β →L[ℝ] Lp ℝ 2 (coulombCenterRelativeMeasure e β) :=
  (WithLp.fstL 2 ℝ ℝ (CoulombConfig n)).compLpL 2 (coulombCenterRelativeMeasure e β)

def coulombCenterRelativeJetGradientL (e : CoulombCenterRotation n) (β : ℝ) :
    CoulombCenterRelativeJetL2 e β →L[ℝ]
      Lp (CoulombConfig n) 2 (coulombCenterRelativeMeasure e β) :=
  (WithLp.sndL 2 ℝ ℝ (CoulombConfig n)).compLpL 2 (coulombCenterRelativeMeasure e β)

theorem coulombCenterRelativeCoreJet_memLp (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombCenterRelativeDomain e) ℝ ⊤) :
    MemLp (fun r => WithLp.toLp 2 (ψ r, gradient (ψ : CoulombConfig n → ℝ) r)) 2
      (coulombCenterRelativeMeasure e β) := by
  letI := coulombCenterRelativeMeasure_isProbability e he hβ
  apply MemLp.of_fst_of_snd_prodLp
  constructor
  · simpa only [WithLp.toLp_fst] using
      (ψ.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport :
        MemLp (ψ : CoulombConfig n → ℝ) 2 (coulombCenterRelativeMeasure e β))
  · simpa only [WithLp.toLp_snd] using
      ((TauCeti.continuous_gradient_testFunction ψ).memLp_of_hasCompactSupport
        (TauCeti.hasCompactSupport_gradient_testFunction ψ) :
        MemLp (fun r => gradient (ψ : CoulombConfig n → ℝ) r) 2
          (coulombCenterRelativeMeasure e β))

def coulombCenterRelativeCoreJet (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombCenterRelativeDomain e) ℝ ⊤) :
    CoulombCenterRelativeJetL2 e β :=
  (coulombCenterRelativeCoreJet_memLp e he hβ ψ).toLp _

theorem coulombCenterRelativeCoreJet_coe (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombCenterRelativeDomain e) ℝ ⊤) :
    coulombCenterRelativeCoreJet e he hβ ψ =ᵐ[coulombCenterRelativeMeasure e β]
      fun r => WithLp.toLp 2 (ψ r, gradient (ψ : CoulombConfig n → ℝ) r) :=
  (coulombCenterRelativeCoreJet_memLp e he hβ ψ).coeFn_toLp

private theorem coulombCenterRelativeCoreJet_add (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (φ ψ : TestFunction (coulombCenterRelativeDomain e) ℝ ⊤) :
    coulombCenterRelativeCoreJet e he hβ (φ + ψ) =
      coulombCenterRelativeCoreJet e he hβ φ + coulombCenterRelativeCoreJet e he hβ ψ := by
  apply Lp.ext
  filter_upwards [coulombCenterRelativeCoreJet_coe e he hβ (φ + ψ),
    coulombCenterRelativeCoreJet_coe e he hβ φ, coulombCenterRelativeCoreJet_coe e he hβ ψ,
    Lp.coeFn_add (coulombCenterRelativeCoreJet e he hβ φ)
      (coulombCenterRelativeCoreJet e he hβ ψ)] with r hsum hφ hψ hadd
  rw [hsum, hadd, Pi.add_apply, hφ, hψ]
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (CoulombConfig n)).injective
  change ((φ + ψ) r, gradient ((φ + ψ : TestFunction (coulombCenterRelativeDomain e) ℝ ⊤) :
    CoulombConfig n → ℝ) r) = (φ r, gradient (φ : CoulombConfig n → ℝ) r) +
      (ψ r, gradient (ψ : CoulombConfig n → ℝ) r)
  exact Prod.ext rfl (TauCeti.gradient_add (φ.contDiff.differentiable (by simp) r)
    (ψ.contDiff.differentiable (by simp) r))

private theorem coulombCenterRelativeCoreJet_smul (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (a : ℝ) (ψ : TestFunction (coulombCenterRelativeDomain e) ℝ ⊤) :
    coulombCenterRelativeCoreJet e he hβ (a • ψ) = a • coulombCenterRelativeCoreJet e he hβ ψ := by
  apply Lp.ext
  filter_upwards [coulombCenterRelativeCoreJet_coe e he hβ (a • ψ),
    coulombCenterRelativeCoreJet_coe e he hβ ψ,
    Lp.coeFn_smul a (coulombCenterRelativeCoreJet e he hβ ψ)] with r hsmul hψ hcoe
  rw [hsmul, hcoe, Pi.smul_apply, hψ]
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (CoulombConfig n)).injective
  change ((a • ψ) r, gradient ((a • ψ : TestFunction (coulombCenterRelativeDomain e) ℝ ⊤) :
    CoulombConfig n → ℝ) r) = a • (ψ r, gradient (ψ : CoulombConfig n → ℝ) r)
  apply Prod.ext
  · rfl
  · exact TauCeti.gradient_const_smul (𝕜 := ℝ) (f := (ψ : CoulombConfig n → ℝ)) (x := r) a

def coulombCenterRelativeCoreJetLinear (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) :
    TestFunction (coulombCenterRelativeDomain e) ℝ ⊤ →ₗ[ℝ] CoulombCenterRelativeJetL2 e β where
  toFun := coulombCenterRelativeCoreJet e he hβ
  map_add' := coulombCenterRelativeCoreJet_add e he hβ
  map_smul' := coulombCenterRelativeCoreJet_smul e he hβ

def coulombCenterRelativeFormSubmodule (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) :
    ClosedSubmodule ℝ (CoulombCenterRelativeJetL2 e β) :=
  (LinearMap.range (coulombCenterRelativeCoreJetLinear e he hβ)).closure

abbrev CoulombCenterRelativeFormDomain (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) :=
  (coulombCenterRelativeFormSubmodule e he hβ).toSubmodule

instance coulombCenterRelativeForm_complete (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) :
    CompleteSpace (CoulombCenterRelativeFormDomain e he hβ) :=
  (coulombCenterRelativeFormSubmodule e he hβ).isClosed.completeSpace_coe

def coulombCenterRelativeFormValueL (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) :
    CoulombCenterRelativeFormDomain e he hβ →L[ℝ] Lp ℝ 2 (coulombCenterRelativeMeasure e β) :=
  (coulombCenterRelativeJetValueL e β).comp
    (coulombCenterRelativeFormSubmodule e he hβ).toSubmodule.subtypeL

def coulombCenterRelativeFormGradientL (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) :
    CoulombCenterRelativeFormDomain e he hβ →L[ℝ]
      Lp (CoulombConfig n) 2 (coulombCenterRelativeMeasure e β) :=
  (coulombCenterRelativeJetGradientL e β).comp
    (coulombCenterRelativeFormSubmodule e he hβ).toSubmodule.subtypeL

def coulombCenterRelativeFormEnergy (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (u : CoulombCenterRelativeFormDomain e he hβ) : ℝ :=
  ‖coulombCenterRelativeFormGradientL e he hβ u‖ ^ 2

def coulombCenterRelativeFormCore (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombCenterRelativeDomain e) ℝ ⊤) :
    CoulombCenterRelativeFormDomain e he hβ :=
  ⟨coulombCenterRelativeCoreJet e he hβ ψ, by
    change coulombCenterRelativeCoreJet e he hβ ψ ∈
      (coulombCenterRelativeFormSubmodule e he hβ : Set _)
    rw [coulombCenterRelativeFormSubmodule, Submodule.coe_closure, LinearMap.coe_range]
    exact subset_closure ⟨ψ, rfl⟩⟩

theorem coulombCenterRelativeFormCore_value (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombCenterRelativeDomain e) ℝ ⊤) :
    coulombCenterRelativeFormValueL e he hβ (coulombCenterRelativeFormCore e he hβ ψ)
      =ᵐ[coulombCenterRelativeMeasure e β] ψ := by
  have h := (WithLp.fstL 2 ℝ ℝ (CoulombConfig n)).coeFn_compLp
    (coulombCenterRelativeCoreJet e he hβ ψ)
  filter_upwards [h, coulombCenterRelativeCoreJet_coe e he hβ ψ] with r hv hr
  change ((WithLp.fstL 2 ℝ ℝ (CoulombConfig n)).compLp
    (coulombCenterRelativeCoreJet e he hβ ψ)) r = ψ r
  rw [hv, hr]
  rfl

theorem coulombCenterRelativeFormCore_gradient (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombCenterRelativeDomain e) ℝ ⊤) :
    coulombCenterRelativeFormGradientL e he hβ (coulombCenterRelativeFormCore e he hβ ψ)
      =ᵐ[coulombCenterRelativeMeasure e β] fun r => gradient (ψ : CoulombConfig n → ℝ) r := by
  have h := (WithLp.sndL 2 ℝ ℝ (CoulombConfig n)).coeFn_compLp
    (coulombCenterRelativeCoreJet e he hβ ψ)
  filter_upwards [h, coulombCenterRelativeCoreJet_coe e he hβ ψ] with r hg hr
  change ((WithLp.sndL 2 ℝ ℝ (CoulombConfig n)).compLp
    (coulombCenterRelativeCoreJet e he hβ ψ)) r = gradient (ψ : CoulombConfig n → ℝ) r
  rw [hg, hr]
  rfl

theorem coulombCenterRelativeFormCore_energy (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombCenterRelativeDomain e) ℝ ⊤) :
    coulombCenterRelativeFormEnergy e he hβ (coulombCenterRelativeFormCore e he hβ ψ) =
      ∫ r, ‖gradient (ψ : CoulombConfig n → ℝ) r‖ ^ 2 ∂coulombCenterRelativeMeasure e β := by
  rw [coulombCenterRelativeFormEnergy, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coulombCenterRelativeFormCore_gradient e he hβ ψ] with r hr
  rw [hr, real_inner_self_eq_norm_sq]

theorem coulombCenterRelativeFormCore_approximation (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β)
    (u : CoulombCenterRelativeFormDomain e he hβ) :
    ∃ ψ : ℕ → TestFunction (coulombCenterRelativeDomain e) ℝ ⊤,
      Tendsto (fun k => coulombCenterRelativeFormCore e he hβ (ψ k)) atTop (𝓝 u) := by
  have hu : (u : CoulombCenterRelativeJetL2 e β) ∈
      closure (range (coulombCenterRelativeCoreJet e he hβ)) := by
    have h := u.property
    change (u : CoulombCenterRelativeJetL2 e β) ∈
      (coulombCenterRelativeFormSubmodule e he hβ : Set _) at h
    rw [coulombCenterRelativeFormSubmodule, Submodule.coe_closure, LinearMap.coe_range] at h
    change (u : CoulombCenterRelativeJetL2 e β) ∈
      closure (range (coulombCenterRelativeCoreJet e he hβ)) at h
    exact h
  obtain ⟨J, hJ, hlim⟩ := mem_closure_iff_seq_limit.mp hu
  choose ψ hψ using hJ
  refine ⟨ψ, tendsto_subtype_rng.mpr ?_⟩
  simpa only [coulombCenterRelativeFormCore, hψ] using hlim

def CoulombCenterRelativeFullLSI (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) (C : ℝ) : Prop :=
  ∀ u : CoulombCenterRelativeFormDomain e he hβ,
    entropy (coulombCenterRelativeMeasure e β)
      (fun r => (coulombCenterRelativeFormValueL e he hβ u r) ^ 2) ≤
      ((C * coulombCenterRelativeFormEnergy e he hβ u : ℝ) : EReal)

/-- Native closed-relative-domain LSI and core LSI are equivalent, including
limits whose entropy was not known finite beforehand. -/
theorem coulombCenterRelative_full_iff_core (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β C : ℝ} (hβ : 0 < β) :
    CoulombCenterRelativeFullLSI e he hβ C ↔ CoulombCenterRelativeCoreLSI e β C := by
  constructor
  · intro h ψ
    have hh := h (coulombCenterRelativeFormCore e he hβ ψ)
    have hv := (coulombCenterRelativeFormCore_value e he hβ ψ).mono
      (fun _ hr => congrArg (fun t : ℝ => t ^ 2) hr)
    rw [entropy_congr_ae hv, coulombCenterRelativeFormCore_energy] at hh
    exact hh
  · intro h u
    obtain ⟨ψ, hψ⟩ := coulombCenterRelativeFormCore_approximation e he hβ u
    have hv := ((coulombCenterRelativeFormValueL e he hβ).continuous.tendsto u).comp hψ
    have hg := ((coulombCenterRelativeFormGradientL e he hβ).continuous.tendsto u).comp hψ
    simp only [Function.comp_def] at hv hg
    apply entropy_sq_le_of_tendsto hv (tendsto_const_nhds.mul (hg.norm.pow 2))
    intro k
    have hval := (coulombCenterRelativeFormCore_value e he hβ (ψ k)).mono
      (fun _ hr => congrArg (fun t : ℝ => t ^ 2) hr)
    change entropy (coulombCenterRelativeMeasure e β)
      (fun r => (coulombCenterRelativeFormValueL e he hβ
        (coulombCenterRelativeFormCore e he hβ (ψ k)) r) ^ 2) ≤
      ((C * coulombCenterRelativeFormEnergy e he hβ
        (coulombCenterRelativeFormCore e he hβ (ψ k)) : ℝ) : EReal)
    rw [entropy_congr_ae hval, coulombCenterRelativeFormCore_energy]
    exact h (ψ k)

end RepulsiveCoulomb
