import LeanResearch.RepulsiveCoulomb.PointConformalLipschitzLength
import LeanResearch.RepulsiveCoulomb.PointConformalGeodesicArc

/-! A genuine shortest geodesic attachment to any compact set in the actual
finite-point metric. Its interior misses the old set. This is the geometric
induction step for a finite embedded tree and assumes no global geodesic
uniqueness or triangulation. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem exists_pointConformal_nearest_attachment {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {K : Set ℂ}
    (hK : IsCompact K) (hKne : K.Nonempty) {p : ℂ} (hp : p ∉ K) :
    ∃ q ∈ K, ∃ γ : Icc (0 : ℝ) 1 → ℂ,
      γ ⟨0, by norm_num⟩ = p ∧ γ ⟨1, by norm_num⟩ = q ∧ Continuous γ ∧
      (∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
        |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal) ∧
      Function.Injective γ ∧ range γ ∩ K = {q} := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hsub : K ⊆ closedBall 0 R := by
    intro z hz
    simpa only [mem_closedBall, dist_zero_right] using hR z hz
  have hc : ContinuousOn (fun z ↦ (pointSmoothConformalEDist a y z p).toReal) K :=
    (pointConformalDistance_lipschitzOn_ball ha y p R).continuousOn.mono hsub
  obtain ⟨q, hq, hmin⟩ := hK.exists_isMinOn hKne hc
  have hpq : p ≠ q := by
    intro he
    apply hp
    rwa [he]
  obtain ⟨γ, h0, h1, hγ, hd⟩ := exists_pointConformal_geodesic ha y p q
  have hD : 0 < (pointSmoothConformalEDist a y p q).toReal := by
    apply ENNReal.toReal_pos
    · exact (pointSmoothConformalEDist_eq_zero_iff ha y p q).not.mpr hpq
    · exact (pointSmoothConformalEDist_lt_top ha y p q).ne
  have hlast (t : Icc (0 : ℝ) 1) (ht : γ t ∈ K) : t.1 = 1 := by
    have h := hmin ht
    change (pointSmoothConformalEDist a y q p).toReal ≤
      (pointSmoothConformalEDist a y (γ t) p).toReal at h
    have ht0 := hd t ⟨0, by norm_num⟩
    rw [h0, zero_sub, abs_neg, abs_of_nonneg t.2.1] at ht0
    rw [pointSmoothConformalEDist_comm a y q p, ht0] at h
    nlinarith [t.2.2]
  refine ⟨q, hq, γ, h0, h1, hγ, hd, pointConformal_geodesic_injective ha y hpq γ hd, ?_⟩
  ext z
  constructor
  · rintro ⟨⟨t, rfl⟩, ht⟩
    have he : t = ⟨1, by norm_num⟩ := Subtype.ext (hlast t ht)
    rw [he, h1]
    exact mem_singleton q
  · intro hz
    have hzq : z = q := mem_singleton_iff.mp hz
    subst z
    exact ⟨⟨⟨1, by norm_num⟩, h1⟩, hq⟩

end RepulsiveCoulomb
