module

public import LeanResearch.RepulsiveCoulomb.PointConformalLocalMetric
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

/-!
# Local regularity of the same point-metric map's inverse

For a supplied homeomorphism F, the lower smooth conformal metric inequality
implies that the actual inverse F.symm is locally Euclidean Lipschitz away from
the finite image of the point punctures. One analytic flat chart supplies both
the metric identity and the locally Lipschitz inverse; no independently chosen
charts are identified. No inverse-Lipschitz certificate, QC, Jacobian, or
David–Semmes estimate is assumed. Specializing the metric inequality to an
accepted Bonk–Lang map remains a separate obligation.
-/

noncomputable section
open Set Metric Filter
open scoped ENNReal NNReal Topology
namespace RepulsiveCoulomb.PaperRoute

/-- A single flat chart has both the actual ambient metric identity and an
analytic inverse. Keeping these properties together prevents chart mismatch. -/
theorem exists_pointConformal_analytic_flat_metric_chart
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (y : Fin m → ℂ) {p : ℂ} (hp : p ∉ pointPunctures a y) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ r : ℝ,
      0 < r ∧ p ∈ e.source ∧ e p = 0 ∧ ball p r ⊆ e.source ∧
      AnalyticOnNhd ℂ e.symm e.target ∧
      ∀ u ∈ ball p r, ∀ v ∈ ball p r,
        pointSmoothConformalEDist a y u v = ENNReal.ofReal ‖e v - e u‖ := by
  obtain ⟨e, hep, he0, _, hinv, he⟩ :=
    exists_pointConformal_flat_chart_with_inverse ha y hp
  have hF : ∀ z ∈ e.source, AnalyticAt ℂ e z ∧
      pointConformalDensity (standardConeExponents 0) standardConeLocations (e z) *
        ‖deriv e z‖ = pointConformalDensity a y z := by
    intro z hz
    refine ⟨(he z hz).1, ?_⟩
    rw [standardCone_density, Real.rpow_zero, one_mul]
    exact (he z hz).2.1
  have hb : ∀ j, 0 ≤ standardConeExponents 0 j := by
    simp [standardConeExponents]
  obtain ⟨r, hr, hsub, hmetric⟩ :=
    pointConformal_chart_local_metric_eq ha y hb standardConeLocations e hF hinv hep
  refine ⟨e, r, hr, hep, he0, hsub, hinv, ?_⟩
  intro u hu v hv
  rw [hmetric u hu v hv, standardCone_zero_distance]

/-- The exceptional set is the finite image under the same supplied map. -/
theorem pointMap_puncture_image_finite {m : ℕ} (a : Fin m → ℝ)
    (y : Fin m → ℂ) (F : ℂ ≃ₜ ℂ) : (F '' pointPunctures a y).Finite :=
  (pointPunctures_finite a y).image F

/-- The actual inverse is Lipschitz on a ball about each nonexceptional target
point. The local constant is produced from the same analytic chart's inverse. -/
theorem pointMapInverse_lipschitzOn_ball_of_metric_lower
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (y : Fin m → ℂ) (F : ℂ ≃ₜ ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hlower : ∀ u v,
      (pointSmoothConformalEDist a y u v).toReal ≤ L * dist (F u) (F v))
    {q : ℂ} (hq : q ∉ F '' pointPunctures a y) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ≥0, LipschitzOnWith C F.symm (ball q η) := by
  have hp : F.symm q ∉ pointPunctures a y := by
    intro hp
    exact hq ⟨F.symm q, hp, F.apply_symm_apply q⟩
  obtain ⟨e, r, hr, hep, he0, hsource, hinv, hmetric⟩ :=
    exists_pointConformal_analytic_flat_metric_chart ha y hp
  have h0 : (0 : ℂ) ∈ e.target := he0 ▸ e.map_source hep
  have hC1 : ContDiffAt ℂ 1 e.symm 0 := (hinv 0 h0).contDiffAt
  obtain ⟨Ce, t, ht, hCe⟩ := hC1.exists_lipschitzOnWith
  have het : e ⁻¹' t ∈ 𝓝 (F.symm q) :=
    (e.continuousAt hep).preimage_mem_nhds (he0.symm ▸ ht)
  have hboth : ball (F.symm q) r ∩ e ⁻¹' t ∈ 𝓝 (F.symm q) :=
    inter_mem (ball_mem_nhds _ hr) het
  have htarget : F.symm ⁻¹' (ball (F.symm q) r ∩ e ⁻¹' t) ∈ 𝓝 q :=
    F.symm.continuous.continuousAt.preimage_mem_nhds hboth
  obtain ⟨η, hη, hsub⟩ := Metric.mem_nhds_iff.mp htarget
  refine ⟨η, hη, Ce * Real.toNNReal L, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro z hz z' hz'
  have hu := hsub hz
  have hv := hsub hz'
  have hdist : dist (e (F.symm z)) (e (F.symm z')) =
      (pointSmoothConformalEDist a y (F.symm z) (F.symm z')).toReal := by
    rw [hmetric _ hu.1 _ hv.1, ENNReal.toReal_ofReal (norm_nonneg _)]
    exact dist_eq_norm' _ _
  calc
    dist (F.symm z) (F.symm z') =
        dist (e.symm (e (F.symm z))) (e.symm (e (F.symm z'))) := by
      rw [e.left_inv (hsource hu.1), e.left_inv (hsource hv.1)]
    _ ≤ (Ce : ℝ) * dist (e (F.symm z)) (e (F.symm z')) :=
      hCe.dist_le_mul _ hu.2 _ hv.2
    _ = (Ce : ℝ) * (pointSmoothConformalEDist a y (F.symm z) (F.symm z')).toReal := by
      rw [hdist]
    _ ≤ (Ce : ℝ) * (L * dist z z') := by
      apply mul_le_mul_of_nonneg_left _ Ce.coe_nonneg
      simpa only [F.apply_symm_apply] using hlower (F.symm z) (F.symm z')
    _ = ((Ce * Real.toNNReal L : ℝ≥0) : ℝ) * dist z z' := by
      rw [NNReal.coe_mul, Real.coe_toNNReal _ hL, mul_assoc]

/-- Same-map inverse regularity on precisely the complement of the finite
puncture image, with no local inverse regularity assumed as an input. -/
theorem pointMapInverse_locallyLipschitzOn_of_metric_lower
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (y : Fin m → ℂ) (F : ℂ ≃ₜ ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hlower : ∀ u v,
      (pointSmoothConformalEDist a y u v).toReal ≤ L * dist (F u) (F v)) :
    LocallyLipschitzOn (F '' pointPunctures a y)ᶜ F.symm := by
  intro q hq
  obtain ⟨η, hη, C, hC⟩ :=
    pointMapInverse_lipschitzOn_ball_of_metric_lower ha y F hL hlower hq
  exact ⟨C, ball q η, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hη), hC⟩

/-- Any compact target region disjoint from the finite puncture image has an
actual Lipschitz bound for this inverse, without a convexity assumption. -/
theorem pointMapInverse_lipschitzOn_compact_of_metric_lower
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (y : Fin m → ℂ) (F : ℂ ≃ₜ ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hlower : ∀ u v,
      (pointSmoothConformalEDist a y u v).toReal ≤ L * dist (F u) (F v))
    {s : Set ℂ} (hs : IsCompact s) (hdisjoint : s ⊆ (F '' pointPunctures a y)ᶜ) :
    ∃ C : ℝ≥0, LipschitzOnWith C F.symm s :=
  LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hs
    ((pointMapInverse_locallyLipschitzOn_of_metric_lower ha y F hL hlower).mono hdisjoint)

end RepulsiveCoulomb.PaperRoute
