module

public import LeanResearch.RepulsiveCoulomb.PointSmoothArcChain
public import LeanResearch.RepulsiveCoulomb.PointGeodesicJordanBigon
public import LeanResearch.RepulsiveCoulomb.PointGeodesicSubedge

@[expose] public section

/-! Actual short smooth collars at either endpoint of an oriented geodesic
subinterval. Reversal is explicit, so the returned pieces retain the original
parameter order even when the constructed radial chart is centered at the end. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def pointArcReverseParam (u : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨1 - u.1, by constructor <;> linarith [u.2.1, u.2.2]⟩

theorem pointArcReverseParam_involutive : Function.Involutive pointArcReverseParam := by
  intro u
  apply Subtype.ext
  dsimp [pointArcReverseParam]
  ring

theorem pointEdgeSubparam_reverse_range {s t : Icc (0 : ℝ) 1} (hst : s < t) :
    range (pointEdgeSubparam t s) = Icc s t := by
  have he : pointEdgeSubparam t s = pointEdgeSubparam s t ∘ pointArcReverseParam := by
    funext u
    apply Subtype.ext
    simp only [pointEdgeSubparam, pointArcReverseParam, Function.comp_apply,
      AffineMap.lineMap_apply_module', smul_eq_mul]
    ring
  rw [he, range_comp, pointArcReverseParam_involutive.surjective.range_eq, image_univ,
    pointEdgeSubparam_range hst]

theorem smooth_regular_arc_reverse (η : ℝ → ℂ)
    (hη : ContDiff ℝ (↑(⊤ : ℕ∞)) η) (hinj : InjOn η (Icc (0 : ℝ) 1))
    (hreg : ∀ u ∈ Icc (0 : ℝ) 1, deriv η u ≠ 0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun u : ℝ => η (1 - u)) ∧
      InjOn (fun u : ℝ => η (1 - u)) (Icc (0 : ℝ) 1) ∧
      (∀ u ∈ Icc (0 : ℝ) 1, deriv (fun v : ℝ => η (1 - v)) u ≠ 0) ∧
      (fun u : ℝ => η (1 - u)) '' Icc (0 : ℝ) 1 = η '' Icc (0 : ℝ) 1 := by
  have hrev (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : 1 - u ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hu.1, hu.2]
  refine ⟨hη.comp (contDiff_const.sub contDiff_id), ?_, ?_, ?_⟩
  · intro u hu v hv huv
    have he := hinj (hrev u hu) (hrev v hv) huv
    linarith
  · intro u hu
    have hD := (hη.differentiable (by simp) (1 - u)).hasDerivAt.scomp u
      ((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u))
    simp only [Function.comp_def, Pi.sub_apply, id_eq] at hD
    rw [hD.deriv]
    exact smul_ne_zero (by norm_num) (hreg _ (hrev u hu))
  · ext z
    constructor
    · rintro ⟨u, hu, huz⟩
      exact ⟨1 - u, hrev u hu, huz⟩
    · rintro ⟨u, hu, huz⟩
      refine ⟨1 - u, hrev u hu, ?_⟩
      simpa only [sub_sub_cancel] using huz

theorem exists_pointSmoothArcPiece_start_radius {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p q : ℂ} (hpq : p ≠ q)
    (γ : Icc (0 : ℝ) 1 → ℂ)
    (hd : ∀ u v, (pointSmoothConformalEDist a y (γ u) (γ v)).toReal =
      |v.1 - u.1| * (pointSmoothConformalEDist a y p q).toReal)
    (s : Icc (0 : ℝ) 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : Icc (0 : ℝ) 1, s < t →
      (pointSmoothConformalEDist a y (γ t) (γ s)).toReal ≤ R →
      ∃ e : PointSmoothArcPiece γ, e.start = s ∧ e.finish = t := by
  obtain ⟨R, hR, hlocal⟩ := exists_pointConformal_geodesic_smooth_arc_radius ha y (γ s)
  have hi := pointConformal_geodesic_injective ha y hpq γ hd
  refine ⟨R, hR, ?_⟩
  intro t hst hnear
  let δ := γ ∘ pointGeodesicIntervalMap s t hst.le
  have h0 : δ ⟨0, by norm_num⟩ = γ s := congrArg γ (pointGeodesicIntervalMap_zero s t hst.le)
  have h1 : δ ⟨1, by norm_num⟩ = γ t := congrArg γ (pointGeodesicIntervalMap_one s t hst.le)
  have hgeo := pointConformal_geodesic_interval_reparameterization a y γ hd s t hst.le
  obtain ⟨η, hη, hηi, hηr, hη0, hη1, _, himage⟩ :=
    hlocal (γ t) hnear (fun he => hst.ne' (hi he)) δ h0 h1 hgeo
  have himage' : η '' Icc (0 : ℝ) 1 = γ '' Icc s t := by
    rw [← himage]
    change range (γ ∘ pointGeodesicIntervalMap s t hst.le) = _
    rw [range_comp, pointGeodesicIntervalMap_range s t hst]
  exact ⟨⟨s, t, hst, η, hη, hηi, hηr, hη0, hη1, himage'⟩, rfl, rfl⟩

theorem exists_pointSmoothArcPiece_finish_radius {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p q : ℂ} (hpq : p ≠ q)
    (γ : Icc (0 : ℝ) 1 → ℂ)
    (hd : ∀ u v, (pointSmoothConformalEDist a y (γ u) (γ v)).toReal =
      |v.1 - u.1| * (pointSmoothConformalEDist a y p q).toReal)
    (t : Icc (0 : ℝ) 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ s : Icc (0 : ℝ) 1, s < t →
      (pointSmoothConformalEDist a y (γ s) (γ t)).toReal ≤ R →
      ∃ e : PointSmoothArcPiece γ, e.start = s ∧ e.finish = t := by
  obtain ⟨R, hR, hlocal⟩ := exists_pointConformal_geodesic_smooth_arc_radius ha y (γ t)
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
  obtain ⟨η, hη, hηi, hηr, hη0, hη1, _, himage⟩ :=
    hlocal (γ s) hnear (fun he => hst.ne (hi he)) δ h0 h1 hgeo
  obtain ⟨hrev, hrevi, hrevr, hrevm⟩ := smooth_regular_arc_reverse η hη hηi hηr
  have himage' : (fun u : ℝ => η (1 - u)) '' Icc (0 : ℝ) 1 = γ '' Icc s t := by
    rw [hrevm, ← himage]
    change range (γ ∘ pointEdgeSubparam t s) = _
    rw [range_comp, pointEdgeSubparam_reverse_range hst]
  refine ⟨⟨s, t, hst, (fun u : ℝ => η (1 - u)), hrev, hrevi, hrevr,
    ?_, ?_, himage'⟩, rfl, rfl⟩
  · simpa only [sub_zero] using hη1
  · simpa only [sub_self] using hη0

end RepulsiveCoulomb
