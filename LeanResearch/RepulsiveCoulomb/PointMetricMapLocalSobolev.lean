module

public import LeanResearch.RepulsiveCoulomb.PointMetricMapDifferential
public import LeanResearch.RepulsiveCoulomb.Imported.TauCeti.Analysis.Sobolev.WeakDeriv.Basic

@[expose] public section

/-!
# Genuine local weak derivatives for actual point-metric maps

Authoring draft: not compiled, staged, or accepted.

The endpoint uses the already accepted `TauCeti.HasWeakFDerivOn`, with its
local-integrability clauses and its identity against every smooth compactly
supported real test function. The representative is literally `fderiv ℝ F`.
Its restriction, and that of `F`, belong to `MemLp` on every compact subset,
for every exponent; in particular this is the standard weak-derivative
characterization of `W^{1,2}_loc`, and also of `W^{1,∞}_loc`.

The load-bearing identity comes from Mathlib's
`LipschitzWith.integral_lineDeriv_mul_eq`. That theorem is proved by dominated
convergence of difference quotients and translation invariance, rather than
assuming an integration-by-parts/ACL certificate. We localize it by extending
each real projection of `F` from one closed ball containing the test support
in its interior. Equality on that neighborhood transfers actual derivatives.

No map existence, orientation, signed Jacobian, global atlas, or
quasiconformality claim is made here. No Bessel-potential Sobolev definition is
substituted for the accepted weak-derivative definition.
-/

noncomputable section
open Set Metric Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal ContDiff Distributions

namespace RepulsiveCoulomb

/-- A ballwise Euclidean Lipschitz map is continuous on the whole plane. -/
theorem plane_continuous_of_lipschitzOn_closedBall {F : ℂ → ℂ}
    (hloc : ∀ R : ℝ, ∃ K : ℝ≥0, LipschitzOnWith K F (closedBall 0 R)) :
    Continuous F := by
  rw [continuous_iff_continuousAt]
  intro z
  obtain ⟨K, hK⟩ := hloc (‖z‖ + 1)
  apply hK.continuousOn.continuousAt
  apply closedBall_mem_nhds_of_mem
  simp only [mem_ball, dist_zero_right]
  exact lt_add_one _

/-- Rademacher on a countable ball cover; no differentiability certificate is
assumed in the local-Lipschitz bridge. -/
theorem plane_ae_differentiableAt_of_lipschitzOn_closedBall {F : ℂ → ℂ}
    (hloc : ∀ R : ℝ, ∃ K : ℝ≥0, LipschitzOnWith K F (closedBall 0 R)) :
    ∀ᵐ z ∂volume, DifferentiableAt ℝ F z := by
  have H (n : ℕ) : ∀ᵐ z ∂volume, z ∈ closedBall (0 : ℂ) (n : ℝ) →
      DifferentiableWithinAt ℝ F (closedBall 0 (n : ℝ)) z := by
    obtain ⟨K, hK⟩ := hloc n
    exact hK.ae_differentiableWithinAt_of_mem
  filter_upwards [ae_all_iff.mpr H] with z hz
  obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
  have hzball : z ∈ ball (0 : ℂ) (n : ℝ) := by
    simpa only [mem_ball, dist_zero_right] using hn
  exact (hz n (ball_subset_closedBall hzball)).differentiableAt
    (closedBall_mem_nhds_of_mem hzball)

/-- Local `L^p` integrability of the map itself, including `p = ∞`. -/
theorem plane_memLp_isCompact_of_lipschitzOn_closedBall {F : ℂ → ℂ}
    (hloc : ∀ R : ℝ, ∃ K : ℝ≥0, LipschitzOnWith K F (closedBall 0 R))
    (p : ℝ≥0∞) {S : Set ℂ} (hS : IsCompact S) :
    MemLp F p (volume.restrict S) := by
  have hF := plane_continuous_of_lipschitzOn_closedBall hloc
  letI : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_ne_top
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hF.continuousOn
  exact MemLp.of_bound hF.aestronglyMeasurable.restrict M
    (ae_restrict_of_forall_mem hS.measurableSet hM)

/-- The genuine real derivative is locally essentially bounded. Its value is
zero at nondifferentiability points, so this bound needs no extra a.e. premise. -/
theorem plane_fderiv_memLp_isCompact_of_lipschitzOn_closedBall {F : ℂ → ℂ}
    (hloc : ∀ R : ℝ, ∃ K : ℝ≥0, LipschitzOnWith K F (closedBall 0 R))
    (p : ℝ≥0∞) {S : Set ℂ} (hS : IsCompact S) :
    MemLp (fderiv ℝ F) p (volume.restrict S) := by
  letI : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_ne_top
  obtain ⟨R, hR⟩ := hS.isBounded.subset_ball (0 : ℂ)
  obtain ⟨K, hK⟩ := hloc R
  apply MemLp.of_bound (measurable_fderiv ℝ F).aestronglyMeasurable.restrict (K : ℝ)
  exact ae_restrict_of_forall_mem hS.measurableSet fun z hz ↦
    norm_fderiv_le_of_lipschitzOn ℝ (closedBall_mem_nhds_of_mem (hR hz)) hK

/-- Local integrability of the operator-valued derivative, independently of
any weak-derivative conclusion. -/
theorem plane_fderiv_locallyIntegrable_of_lipschitzOn_closedBall {F : ℂ → ℂ}
    (hloc : ∀ R : ℝ, ∃ K : ℝ≥0, LipschitzOnWith K F (closedBall 0 R)) :
    LocallyIntegrable (fderiv ℝ F) volume := by
  apply locallyIntegrable_iff.mpr
  intro S hS
  exact memLp_one_iff_integrable.mp
    (plane_fderiv_memLp_isCompact_of_lipschitzOn_closedBall hloc 1 hS)

/-- The load-bearing local scalar integration-by-parts identity. The only
regularity assumed of `u` is Lipschitz continuity on one actual ball containing
the test support in its interior. No ACL or weak-derivative identity is input. -/
theorem scalar_integral_lineDeriv_mul_of_lipschitzOn_closedBall
    {u φ : ℂ → ℝ} {R : ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u (closedBall 0 R))
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφR : tsupport φ ⊆ ball 0 R) (v : ℂ) :
    (∫ z, lineDeriv ℝ u z v * φ z) =
      -(∫ z, fderiv ℝ φ z v * u z) := by
  obtain ⟨g, hg, hug⟩ := hu.extend_real
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ (by simp)
  have hφdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hline (z : ℂ) (hz : z ∈ tsupport φ) :
      lineDeriv ℝ u z v = lineDeriv ℝ g z v := by
    have heq : u =ᶠ[𝓝 z] g := by
      filter_upwards [closedBall_mem_nhds_of_mem (hφR hz)] with w hw
      exact hug hw
    exact heq.lineDeriv_eq
  calc
    (∫ z, lineDeriv ℝ u z v * φ z) =
        ∫ z, lineDeriv ℝ g z v * φ z := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ tsupport φ
      · rw [hline z hz]
      · simp [image_eq_zero_of_notMem_tsupport hz]
    _ = ∫ z, lineDeriv ℝ φ z (-v) * g z :=
      hg.integral_lineDeriv_mul_eq hD hφc v
    _ = -(∫ z, fderiv ℝ φ z v * u z) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with z
      rw [(hφdiff z).lineDeriv_eq_fderiv, map_neg, neg_mul]
      by_cases hz : z ∈ tsupport φ
      · rw [hug (ball_subset_closedBall (hφR hz))]
      · simp [fderiv_of_notMem_tsupport ℝ hz]

/-- Scalarization of the actual real derivative satisfies the full test
identity. Rademacher identifies the line derivative only after the identity
has been obtained from Lipschitz difference quotients. -/
theorem plane_projection_integral_fderiv_mul_of_lipschitzOn_closedBall
    {F : ℂ → ℂ}
    (hloc : ∀ R : ℝ, ∃ K : ℝ≥0, LipschitzOnWith K F (closedBall 0 R))
    (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ z, fderiv ℝ φ z v * ℓ (F z)) =
      -(∫ z, φ z * ℓ (fderiv ℝ F z v)) := by
  obtain ⟨R, hR⟩ := hφc.isBounded.subset_ball (0 : ℂ)
  obtain ⟨K, hK⟩ := hloc R
  have h := scalar_integral_lineDeriv_mul_of_lipschitzOn_closedBall
    (ℓ.lipschitzWith.comp_lipschitzOnWith hK) hφ hφc hR v
  have heq : (∫ z, lineDeriv ℝ (ℓ ∘ F) z v * φ z) =
      ∫ z, φ z * ℓ (fderiv ℝ F z v) := by
    apply integral_congr_ae
    filter_upwards [plane_ae_differentiableAt_of_lipschitzOn_closedBall hloc] with z hz
    have hc := ℓ.hasFDerivAt.comp z hz.hasFDerivAt
    rw [hc.differentiableAt.lineDeriv_eq_fderiv, hc.fderiv]
    simp only [ContinuousLinearMap.comp_apply, mul_comm]
  rw [heq] at h
  change (∫ z, φ z * ℓ (fderiv ℝ F z v)) =
    -(∫ z, fderiv ℝ φ z v * ℓ (F z)) at h
  linarith

/-- A scalar projection has its actual projected derivative as a weak
coordinate/directional derivative, in the accepted Tau Ceti definition. -/
theorem plane_projection_hasWeakLineDerivOn_of_lipschitzOn_closedBall
    {F : ℂ → ℂ}
    (hloc : ∀ R : ℝ, ∃ K : ℝ≥0, LipschitzOnWith K F (closedBall 0 R))
    (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) :
    TauCeti.HasWeakLineDerivOn volume (⊤ : Opens ℂ)
      (fun z ↦ ℓ (F z)) (fun z ↦ ℓ (fderiv ℝ F z v)) v := by
  have hF := plane_continuous_of_lipschitzOn_closedBall hloc
  have hD := plane_fderiv_locallyIntegrable_of_lipschitzOn_closedBall hloc
  have hFℓ : LocallyIntegrableOn (fun z ↦ ℓ (F z)) (⊤ : Opens ℂ) volume :=
    (ℓ.continuous.comp hF).locallyIntegrable.locallyIntegrableOn _
  have hDℓ : LocallyIntegrableOn (fun z ↦ ℓ (fderiv ℝ F z v)) (⊤ : Opens ℂ) volume := by
    exact (ℓ.comp (ContinuousLinearMap.apply ℝ ℂ v)).locallyIntegrableOn_comp
      (hD.locallyIntegrableOn _)
  apply (TauCeti.hasWeakLineDerivOn_iff hFℓ hDℓ).mpr
  intro φ hφ hφc _
  have h := plane_projection_integral_fderiv_mul_of_lipschitzOn_closedBall
    hloc ℓ v hφ hφc
  simpa only [(hφ.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv,
    smul_eq_mul] using h

/-- Local Lipschitz continuity constructs the actual complex-valued weak
Fréchet derivative. The real and imaginary component identities are combined
by the accepted weak-derivative linearity theorems. -/
theorem plane_hasWeakFDerivOn_of_lipschitzOn_closedBall {F : ℂ → ℂ}
    (hloc : ∀ R : ℝ, ∃ K : ℝ≥0, LipschitzOnWith K F (closedBall 0 R)) :
    TauCeti.HasWeakFDerivOn volume (⊤ : Opens ℂ) F (fderiv ℝ F) := by
  apply TauCeti.hasWeakFDerivOn_iff.mpr
  intro v
  let B : ℝ →L[ℝ] ℂ := (1 : ℝ →L[ℝ] ℝ).smulRight Complex.I
  have hr := (plane_projection_hasWeakLineDerivOn_of_lipschitzOn_closedBall
    hloc Complex.reCLM v).clm_comp Complex.ofRealCLM
  have hi := (plane_projection_hasWeakLineDerivOn_of_lipschitzOn_closedBall
    hloc Complex.imCLM v).clm_comp B
  have hsum := hr.add hi
  have hsplit (z : ℂ) : Complex.ofRealCLM (Complex.reCLM z) + B (Complex.imCLM z) = z := by
    simpa [B, Complex.real_smul] using Complex.re_add_im z
  have hvalue :
      (fun z ↦ Complex.ofRealCLM (Complex.reCLM (F z))) +
        (fun z ↦ B (Complex.imCLM (F z))) = F := by
    funext z
    exact hsplit (F z)
  have hderiv :
      (fun z ↦ Complex.ofRealCLM (Complex.reCLM (fderiv ℝ F z v))) +
        (fun z ↦ B (Complex.imCLM (fderiv ℝ F z v))) =
        (fun z ↦ fderiv ℝ F z v) := by
    funext z
    exact hsplit (fderiv ℝ F z v)
  rw [hvalue, hderiv] at hsum
  exact hsum

/-- An actual point-metric upper bound supplies the only regularity hypothesis
needed above. It is valid at every atom as well as away from them. -/
theorem pointMetricMap_hasWeakFDerivOn {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ p z, dist (F p) (F z) ≤
      C * (pointSmoothConformalEDist a y p z).toReal) :
    TauCeti.HasWeakFDerivOn volume (⊤ : Opens ℂ) F (fderiv ℝ F) := by
  apply plane_hasWeakFDerivOn_of_lipschitzOn_closedBall
  intro R
  exact ⟨_, pointMetricMap_lipschitzOn_ball ha y hC hupper R⟩

/-- Exact weak-derivative/local-`L^p` endpoint. Taking `p = 2` gives genuine
`W^{1,2}_loc`; taking `p = ∞` gives the stronger conclusion in Pro §11.
The a.e. `HasFDerivAt` clause identifies the same representative with the
actual classical derivative. This does not assume map existence. -/
theorem pointMetricMap_localSobolev {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ p z, dist (F p) (F z) ≤
      C * (pointSmoothConformalEDist a y p z).toReal) :
    TauCeti.HasWeakFDerivOn volume (⊤ : Opens ℂ) F (fderiv ℝ F) ∧
      (∀ p : ℝ≥0∞, ∀ S : Set ℂ, IsCompact S →
        MemLp F p (volume.restrict S) ∧
        MemLp (fderiv ℝ F) p (volume.restrict S)) ∧
      (∀ᵐ z ∂volume, HasFDerivAt F (fderiv ℝ F z) z) := by
  have hloc : ∀ R : ℝ, ∃ K : ℝ≥0, LipschitzOnWith K F (closedBall 0 R) :=
    fun R ↦ ⟨_, pointMetricMap_lipschitzOn_ball ha y hC hupper R⟩
  refine ⟨pointMetricMap_hasWeakFDerivOn ha y hC hupper, ?_, ?_⟩
  · intro p S hS
    exact ⟨plane_memLp_isCompact_of_lipschitzOn_closedBall hloc p hS,
      plane_fderiv_memLp_isCompact_of_lipschitzOn_closedBall hloc p hS⟩
  · filter_upwards [pointMetricMap_ae_differentiableAt ha y hC hupper] with z hz
    exact hz.hasFDerivAt

/-- The explicit `W^{1,2}_loc` endpoint, using the accepted weak derivative
and actual `L²` membership on every compact set rather than a newly introduced
Sobolev predicate. -/
theorem pointMetricMap_localW12 {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ p z, dist (F p) (F z) ≤
      C * (pointSmoothConformalEDist a y p z).toReal) :
    TauCeti.HasWeakFDerivOn volume (⊤ : Opens ℂ) F (fderiv ℝ F) ∧
      (∀ S : Set ℂ, IsCompact S →
        MemLp F 2 (volume.restrict S) ∧
        MemLp (fderiv ℝ F) 2 (volume.restrict S)) ∧
      (∀ᵐ z ∂volume, HasFDerivAt F (fderiv ℝ F z) z) := by
  have h := pointMetricMap_localSobolev ha y hC hupper
  exact ⟨h.1, h.2.1 2, h.2.2⟩

/-- Literal, integrable compact-test identity for the actual metric map. -/
theorem pointMetricMap_weak_test_identity {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ p z, dist (F p) (F z) ≤
      C * (pointSmoothConformalEDist a y p z).toReal)
    (v : ℂ) (φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) :
    Integrable (fun z ↦ lineDeriv ℝ (φ : ℂ → ℝ) z v • F z) volume ∧
      Integrable (fun z ↦ φ z • fderiv ℝ F z v) volume ∧
      (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z v • F z) =
        -(∫ z, φ z • fderiv ℝ F z v) := by
  have hw := (pointMetricMap_hasWeakFDerivOn ha y hC hupper).hasWeakLineDerivOn v
  exact ⟨TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn
      hw.locallyIntegrableOn φ v,
    TauCeti.integrable_smul_of_locallyIntegrableOn hw.locallyIntegrableOn_deriv φ,
    hw.integral_lineDeriv_smul_eq_neg_integral_smul φ⟩

end RepulsiveCoulomb
