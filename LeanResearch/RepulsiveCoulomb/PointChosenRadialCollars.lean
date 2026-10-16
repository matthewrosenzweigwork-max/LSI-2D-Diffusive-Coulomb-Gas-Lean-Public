import LeanResearch.RepulsiveCoulomb.PointChosenSmoothRadialChart
import LeanResearch.RepulsiveCoulomb.PointSmoothArcCollars

/-! Actual collars in the one chart selected per physical vertex. The power
law and exact neighborhood radial formula are retained for later derivative
matching and true-corner smoothing. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem pointEdgeSubparam_val_affine (s t u : Icc (0 : ℝ) 1) :
    (pointEdgeSubparam s t u).1 = s.1 + u.1 * (t.1 - s.1) := by
  simp only [pointEdgeSubparam, AffineMap.lineMap_apply_module', smul_eq_mul]
  ring

theorem exists_pointChosenRadial_start_collar {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p q : ℂ} (hpq : p ≠ q)
    (γ : Icc (0 : ℝ) 1 → ℂ)
    (hd : ∀ u v, (pointSmoothConformalEDist a y (γ u) (γ v)).toReal =
      |v.1 - u.1| * (pointSmoothConformalEDist a y p q).toReal)
    (s : Icc (0 : ℝ) 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : Icc (0 : ℝ) 1, s < t →
      (pointSmoothConformalEDist a y (γ t) (γ s)).toReal ≤ R →
      ∃ L : PointSmoothArcPiece γ, L.start = s ∧ L.finish = t ∧
        (∀ u ∈ Icc (0 : ℝ) 1,
          IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ (s.1 + u * (t.1 - s.1)) =
            L.curve (u ^ (coalescedPointExponent a y (γ s) / 2 + 1)⁻¹)) ∧
        (∀ u ∈ Icc (0 : ℝ) 1, L.curve =ᶠ[𝓝 u] (fun v : ℝ =>
          (pointChosenSmoothRadialChart ha y (γ s)).symm
            (v • (pointChosenSmoothRadialChart ha y (γ s)) (γ t)))) := by
  obtain ⟨R, hR, _, _, _, _, hlocal⟩ := pointChosenSmoothRadialChart_spec ha y (γ s)
  have hi := pointConformal_geodesic_injective ha y hpq γ hd
  refine ⟨R, hR, ?_⟩
  intro t hst hnear
  let δ := γ ∘ pointEdgeSubparam s t
  have h0 : δ ⟨0, by norm_num⟩ = γ s := congrArg γ (pointEdgeSubparam_zero s t)
  have h1 : δ ⟨1, by norm_num⟩ = γ t := congrArg γ (pointEdgeSubparam_one s t)
  have hgeo : ∀ u v : Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (δ u) (δ v)).toReal =
        |v.1 - u.1| * (pointSmoothConformalEDist a y (γ s) (γ t)).toReal := by
    intro u v
    change (pointSmoothConformalEDist a y (γ (pointEdgeSubparam s t u))
      (γ (pointEdgeSubparam s t v))).toReal = _
    rw [hd, hd s t, pointEdgeSubparam_sub, abs_mul, mul_assoc]
  obtain ⟨η, hη, hηi, hηr, hη0, hη1, hgerm, hpower, himage⟩ :=
    hlocal (γ t) hnear (fun he => hst.ne' (hi he)) δ h0 h1 hgeo
  have himage' : η '' Icc (0 : ℝ) 1 = γ '' Icc s t := by
    rw [← himage]
    change range (γ ∘ pointEdgeSubparam s t) = _
    rw [range_comp, pointEdgeSubparam_range hst]
  let L : PointSmoothArcPiece γ := ⟨s, t, hst, η, hη, hηi, hηr, hη0, hη1, himage'⟩
  refine ⟨L, rfl, rfl, ?_, hgerm⟩
  intro u hu
  have he : IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ
      (s.1 + u * (t.1 - s.1)) = δ ⟨u, hu⟩ := by
    rw [← pointEdgeSubparam_val_affine s t ⟨u, hu⟩]
    exact IccExtend_of_mem _ _ (pointEdgeSubparam s t ⟨u, hu⟩).2
  exact he.trans (hpower ⟨u, hu⟩)

theorem exists_pointChosenRadial_finish_collar {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p q : ℂ} (hpq : p ≠ q)
    (γ : Icc (0 : ℝ) 1 → ℂ)
    (hd : ∀ u v, (pointSmoothConformalEDist a y (γ u) (γ v)).toReal =
      |v.1 - u.1| * (pointSmoothConformalEDist a y p q).toReal)
    (t : Icc (0 : ℝ) 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ s : Icc (0 : ℝ) 1, s < t →
      (pointSmoothConformalEDist a y (γ s) (γ t)).toReal ≤ R →
      ∃ L : PointSmoothArcPiece γ, L.start = s ∧ L.finish = t ∧
        (∀ u ∈ Icc (0 : ℝ) 1,
          IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ (t.1 + u * (s.1 - t.1)) =
            L.curve (1 - u ^ (coalescedPointExponent a y (γ t) / 2 + 1)⁻¹)) ∧
        (∀ u ∈ Icc (0 : ℝ) 1, L.curve =ᶠ[𝓝 u] (fun v : ℝ =>
          (pointChosenSmoothRadialChart ha y (γ t)).symm
            ((1 - v) • (pointChosenSmoothRadialChart ha y (γ t)) (γ s)))) := by
  obtain ⟨R, hR, _, _, _, _, hlocal⟩ := pointChosenSmoothRadialChart_spec ha y (γ t)
  have hi := pointConformal_geodesic_injective ha y hpq γ hd
  refine ⟨R, hR, ?_⟩
  intro s hst hnear
  let δ := γ ∘ pointEdgeSubparam t s
  have h0 : δ ⟨0, by norm_num⟩ = γ t := congrArg γ (pointEdgeSubparam_zero t s)
  have h1 : δ ⟨1, by norm_num⟩ = γ s := congrArg γ (pointEdgeSubparam_one t s)
  have hgeo : ∀ u v : Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (δ u) (δ v)).toReal =
        |v.1 - u.1| * (pointSmoothConformalEDist a y (γ t) (γ s)).toReal := by
    intro u v
    change (pointSmoothConformalEDist a y (γ (pointEdgeSubparam t s u))
      (γ (pointEdgeSubparam t s v))).toReal = _
    rw [hd, hd t s, pointEdgeSubparam_sub, abs_mul, mul_assoc]
  obtain ⟨η, hη, hηi, hηr, hη0, hη1, hgerm, hpower, himage⟩ :=
    hlocal (γ s) hnear (fun he => hst.ne (hi he)) δ h0 h1 hgeo
  obtain ⟨hrev, hrevi, hrevr, hrevm⟩ := smooth_regular_arc_reverse η hη hηi hηr
  have himage' : (fun u : ℝ => η (1 - u)) '' Icc (0 : ℝ) 1 = γ '' Icc s t := by
    rw [hrevm, ← himage]
    change range (γ ∘ pointEdgeSubparam t s) = _
    rw [range_comp, pointEdgeSubparam_reverse_range hst]
  have hrev0 : (fun u : ℝ => η (1 - u)) 0 = γ s := by simpa only [sub_zero] using hη1
  have hrev1 : (fun u : ℝ => η (1 - u)) 1 = γ t := by simpa only [sub_self] using hη0
  let L : PointSmoothArcPiece γ :=
    ⟨s, t, hst, (fun u : ℝ => η (1 - u)), hrev, hrevi, hrevr, hrev0, hrev1, himage'⟩
  refine ⟨L, rfl, rfl, ?_, ?_⟩
  · intro u hu
    have he : IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ
        (t.1 + u * (s.1 - t.1)) = δ ⟨u, hu⟩ := by
      rw [← pointEdgeSubparam_val_affine t s ⟨u, hu⟩]
      exact IccExtend_of_mem _ _ (pointEdgeSubparam t s ⟨u, hu⟩).2
    change _ = η (1 - (1 - _))
    rw [sub_sub_cancel]
    exact he.trans (hpower ⟨u, hu⟩)
  · intro u hu
    have hru : 1 - u ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hu.1, hu.2]
    exact (hgerm (1 - u) hru).comp_tendsto ((continuous_const.sub continuous_id).tendsto u)

end RepulsiveCoulomb
