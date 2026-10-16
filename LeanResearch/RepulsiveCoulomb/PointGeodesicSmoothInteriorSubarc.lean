import LeanResearch.RepulsiveCoulomb.PointGeodesicJordanBigon
import LeanResearch.RepulsiveCoulomb.PointGeodesicPhysicalSpeed
import LeanResearch.RepulsiveCoulomb.AnalyticArcSmoothExtension

/-! An actual regular smooth representative of every closed interior subarc
which avoids positive punctures. Together with radial endpoint collars, this
is the analytic middle-edge input for finite smooth bigon decomposition. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exists_pointConformal_smooth_interior_subarc {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p q : ℂ} (hpq : p ≠ q)
    (γ : Icc (0 : ℝ) 1 → ℂ)
    (hd : ∀ u v, (pointSmoothConformalEDist a y (γ u) (γ v)).toReal =
      |v.1 - u.1| * (pointSmoothConformalEDist a y p q).toReal)
    (s t : Icc (0 : ℝ) 1) (hst : s < t) (hs0 : 0 < s.1) (ht1 : t.1 < 1)
    (havoid : ∀ u ∈ Icc s t, γ u ∉ pointPunctures a y) :
    ∃ η : ℝ → ℂ, ContDiff ℝ (↑(⊤ : ℕ∞)) η ∧
      InjOn η (Icc (0 : ℝ) 1) ∧
      (∀ u ∈ Icc (0 : ℝ) 1, deriv η u ≠ 0) ∧
      η 0 = γ s ∧ η 1 = γ t ∧
      (∀ u : Icc (0 : ℝ) 1, η u.1 = γ (pointGeodesicIntervalMap s t hst.le u)) ∧
      η '' Icc (0 : ℝ) 1 = γ '' Icc s t := by
  have hc := pointConformal_geodesic_continuous ha y γ hd
  have hinj := pointConformal_geodesic_injective ha y hpq γ hd
  let g := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ
  let φ : ℝ → ℝ := fun u => s.1 + u * (t.1 - s.1)
  let f := g ∘ φ
  let D := (pointSmoothConformalEDist a y p q).toReal
  have hD : 0 < D := by
    apply ENNReal.toReal_pos
    · exact (pointSmoothConformalEDist_eq_zero_iff ha y p q).not.mpr hpq
    · exact (pointSmoothConformalEDist_lt_top ha y p q).ne
  have hst' : s.1 < t.1 := hst
  have hφst (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : φ u ∈ Icc s.1 t.1 := by
    have hlow := mul_nonneg hu.1 (sub_nonneg.mpr hst'.le)
    have hhigh := mul_le_mul_of_nonneg_right hu.2 (sub_nonneg.mpr hst'.le)
    change s.1 ≤ s.1 + u * (t.1 - s.1) ∧ s.1 + u * (t.1 - s.1) ≤ t.1
    constructor <;> nlinarith
  have hφ01 (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : φ u ∈ Ioo (0 : ℝ) 1 :=
    ⟨hs0.trans_le (hφst u hu).1, (hφst u hu).2.trans_lt ht1⟩
  have hpφ (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      γ ⟨φ u, ⟨(hφ01 u hu).1.le, (hφ01 u hu).2.le⟩⟩ ∉ pointPunctures a y :=
    havoid _ (hφst u hu)
  have hgA (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : AnalyticAt ℝ g (φ u) :=
    pointConformal_geodesic_extension_analyticAt ha y γ hc hd (hφ01 u hu) (hpφ u hu)
  have hA : AnalyticOnNhd ℝ f (Icc (0 : ℝ) 1) := by
    intro u hu
    exact (hgA u hu).comp (analyticAt_const.add (analyticAt_id.mul analyticAt_const))
  have hg : Continuous g := continuous_IccExtend_iff.mpr hc
  have hgeo : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (g u) (g v)).toReal = |v - u| * D := by
    intro u hu v hv
    dsimp [g]
    rw [IccExtend_of_mem _ _ hu, IccExtend_of_mem _ _ hv]
    exact hd ⟨u, hu⟩ ⟨v, hv⟩
  have hfparam (u : Icc (0 : ℝ) 1) : f u.1 = γ (pointGeodesicIntervalMap s t hst.le u) := by
    change g (φ u.1) = _
    dsimp [g]
    rw [IccExtend_of_mem _ _ ⟨(hφ01 u.1 u.2).1.le, (hφ01 u.1 u.2).2.le⟩]
    rfl
  have hfreg (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : deriv f u ≠ 0 := by
    have hspeed := pointConformal_geodesic_physical_speed ha y g hg D hgeo
      (hφ01 u hu) (by
        dsimp [g]
        rw [IccExtend_of_mem _ _ ⟨(hφ01 u hu).1.le, (hφ01 u hu).2.le⟩]
        exact hpφ u hu)
    have hgD : deriv g (φ u) ≠ 0 := by
      intro he
      rw [he, norm_zero, mul_zero] at hspeed
      exact hD.ne' hspeed.symm
    have hφD : HasDerivAt φ (t.1 - s.1) u := by
      convert! ((hasDerivAt_id u).mul_const (t.1 - s.1)).const_add s.1 using 1 <;>
        simp [φ]
    have hfD : HasDerivAt f ((t.1 - s.1) • deriv g (φ u)) u :=
      (hgA u hu).differentiableAt.hasDerivAt.scomp u hφD
    rw [hfD.deriv]
    exact smul_ne_zero (sub_ne_zero.mpr hst'.ne') hgD
  have hfi : InjOn f (Icc (0 : ℝ) 1) := by
    intro u hu v hv he
    have heq : γ (pointGeodesicIntervalMap s t hst.le ⟨u, hu⟩) =
        γ (pointGeodesicIntervalMap s t hst.le ⟨v, hv⟩) :=
      (hfparam ⟨u, hu⟩).symm.trans (he.trans (hfparam ⟨v, hv⟩))
    have hφeq := congrArg Subtype.val (hinj heq)
    change s.1 + u * (t.1 - s.1) = s.1 + v * (t.1 - s.1) at hφeq
    nlinarith
  obtain ⟨η, hη, hagree⟩ := analytic_unitInterval_global_smooth_extension f hA
  have heq : EqOn η f (Icc (0 : ℝ) 1) := fun u hu => (hagree u hu).self_of_nhds
  have hparam (u : Icc (0 : ℝ) 1) : η u.1 = γ (pointGeodesicIntervalMap s t hst.le u) :=
    (heq u.2).trans (hfparam u)
  refine ⟨η, hη, ?_, ?_, ?_, ?_, hparam, ?_⟩
  · intro u hu v hv huv
    exact hfi hu hv ((heq hu).symm.trans (huv.trans (heq hv)))
  · intro u hu
    rw [(hagree u hu).deriv_eq]
    exact hfreg u hu
  · exact (hparam ⟨0, by norm_num⟩).trans (congrArg γ (pointGeodesicIntervalMap_zero s t hst.le))
  · exact (hparam ⟨1, by norm_num⟩).trans (congrArg γ (pointGeodesicIntervalMap_one s t hst.le))
  · have himage : η '' Icc (0 : ℝ) 1 = range (γ ∘ pointGeodesicIntervalMap s t hst.le) := by
      ext z
      constructor
      · rintro ⟨u, hu, huz⟩
        exact ⟨⟨u, hu⟩, (hparam ⟨u, hu⟩).symm.trans huz⟩
      · rintro ⟨u, rfl⟩
        exact ⟨u.1, u.2, hparam u⟩
    rw [himage, range_comp, pointGeodesicIntervalMap_range s t hst]

end RepulsiveCoulomb
