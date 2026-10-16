import LeanResearch.RepulsiveCoulomb.PointTranslatedTopPreservesEdge
import LeanResearch.RepulsiveCoulomb.TranslatedRectangleExchange

/-! ISOLATED SOURCE-ONLY DRAFT. Advance the escaping-ray direction while
holding one positive transverse width fixed. This avoids a separate
corner-plus-variable-collar construction for each requested finite length.
The genuine full-chart facts at positive transverse height remain explicit
local geometric inputs, to be derived by the parallel-return obstruction.
-/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

def shearedBottomPoint {v : ℂ} {R s : ℝ} (hs : 0 ≤ s) (r : Icc (0 : ℝ) R) :
    flatShearedRectangle v R s :=
  ⟨flatShearedPoint v r.1 0, r.1, r.2, 0, ⟨le_rfl, hs⟩, rfl⟩

def shearedRightPoint {v : ℂ} {R s : ℝ} (hR : 0 ≤ R) (u : Icc (0 : ℝ) s) :
    flatShearedRectangle v R s :=
  ⟨flatShearedPoint v R u.1, R, ⟨hR, le_rfl⟩, u.1, u.2, rfl⟩

theorem point_exists_translated_longitudinal_extension
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hP : IsClosed P) {stripAngle R s limit : ℝ}
    (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hR : 0 < R) (hs : 0 < s) (hRlimit : R < limit)
    (ρ : NNReal → P)
    (hρ : @Isometry NNReal P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace ρ)
    (f : flatShearedRectangle (conePhase stripAngle) R s → P)
    (hf : @Isometry _ P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace f)
    (hbottom : ∀ r : Icc (0 : ℝ) R,
      f (shearedBottomPoint hs.le r) = ρ ⟨r.1, r.2.1⟩)
    (C : @MetricFlatHalfDiskChart P (pointRegionMetricSpace ha y P) (ρ ⟨R, hR.le⟩))
    (hregular : ∀ u : Icc (0 : ℝ) s, 0 < u.1 →
      Nonempty (@MetricFlatDiskChart P (pointRegionMetricSpace ha y P)
        (f (shearedRightPoint hR.le u)))) :
    ∃ h : ℝ, 0 < h ∧ R + h < limit ∧
      ∃ F : flatShearedRectangle (conePhase stripAngle) (R + h) s → P,
        (∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z) ∧
        (∀ x : flatShearedRectangle (conePhase stripAngle) R s,
          ∀ hx : x.1 ∈ flatShearedRectangle (conePhase stripAngle) (R + h) s, F ⟨x.1, hx⟩ = f x) ∧
        ∀ r : Icc (0 : ℝ) (R + h),
          F (shearedBottomPoint hs.le r) = ρ ⟨r.1, r.2.1⟩ := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  let v := conePhase stripAngle
  let swap := shearedRectangleExchange (conePhase_norm stripAngle) s R
  let g := f ∘ swap
  have hg : Isometry g := hf.comp swap.isometry
  let edge : Icc (0 : ℝ) (R + 1) → P := fun r ↦ ρ ⟨r.1, r.2.1⟩
  have hedge : Isometry edge := by
    apply Isometry.of_dist_eq
    intro r t
    exact hρ.dist_eq ⟨r.1, r.2.1⟩ ⟨t.1, t.2.1⟩
  have hsedge : R < R + 1 := by linarith
  have hgcompact (r : Icc (0 : ℝ) R) :
      g (shearedCompactEdgePoint hs.le r) = edge ⟨r.1, r.2.1, r.2.2.trans hsedge.le⟩ := by
    have he : swap (shearedCompactEdgePoint hs.le r) = shearedBottomPoint hs.le r := by
      apply Subtype.ext
      exact shearedCoordinateExchange_point (conePhase_norm stripAngle) 0 r.1
    change f (swap (shearedCompactEdgePoint hs.le r)) = ρ ⟨r.1, r.2.1⟩
    rw [he]
    exact hbottom r
  have hcenter : g (shearedCompactEdgePoint hs.le ⟨R, hR.le, le_rfl⟩) = ρ ⟨R, hR.le⟩ :=
    hgcompact ⟨R, hR.le, le_rfl⟩
  let C' : MetricFlatHalfDiskChart P
      (g (shearedCompactEdgePoint hs.le ⟨R, hR.le, le_rfl⟩)) := hcenter.symm ▸ C
  have hgregular (u : Icc (0 : ℝ) s) (hu : 0 < u.1) :
      Nonempty (MetricFlatDiskChart P (g (shearedTopPoint v s R hR.le u))) := by
    have he : swap (shearedTopPoint v s R hR.le u) = shearedRightPoint hR.le u := by
      apply Subtype.ext
      exact shearedCoordinateExchange_point (conePhase_norm stripAngle) u.1 R
    change Nonempty (MetricFlatDiskChart P (f (swap (shearedTopPoint v s R hR.le u))))
    rw [he]
    exact hregular u hu
  obtain ⟨h, hh, hhlimit, hnewedge, G, hdG, hGold, hGcompact⟩ :=
    point_exists_closed_translated_top_extension_with_edge ha y hP stripAngle_pos stripAngle_lt_pi hs hR
      hRlimit hsedge g hg edge hedge hgcompact C' hgregular
  let swap' := shearedRectangleExchange (conePhase_norm stripAngle) (R + h) s
  let F := G ∘ swap'
  have hG : Isometry G := Isometry.of_dist_eq hdG
  have hF : Isometry F := hG.comp swap'.isometry
  refine ⟨h, hh, hhlimit, F, fun x z ↦ hF.dist_eq x z, ?_, ?_⟩
  · intro x hx
    let xswap := (shearedRectangleExchange (conePhase_norm stripAngle) R s) x
    have hxswap : xswap.1 ∈ flatShearedRectangle v s (R + h) :=
      flatShearedRectangle_mono le_rfl (by linarith) xswap.2
    have hsource : swap' ⟨x.1, hx⟩ = ⟨xswap.1, hxswap⟩ := Subtype.ext rfl
    change G (swap' ⟨x.1, hx⟩) = f x
    rw [hsource, hGold xswap hxswap]
    change f (swap xswap) = f x
    apply congrArg f
    apply Subtype.ext
    exact (shearedCoordinateExchange v (conePhase_norm stripAngle)).symm_apply_apply x.1
  · intro r
    have he : swap' (shearedBottomPoint hs.le r) = shearedCompactEdgePoint hs.le r := by
      apply Subtype.ext
      exact shearedCoordinateExchange_point (conePhase_norm stripAngle) r.1 0
    change G (swap' (shearedBottomPoint hs.le r)) = ρ ⟨r.1, r.2.1⟩
    rw [he]
    exact hGcompact r

end RepulsiveCoulomb
