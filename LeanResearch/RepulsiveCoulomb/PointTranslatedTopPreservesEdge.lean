import LeanResearch.RepulsiveCoulomb.PointClosedTranslatedTopExtension
import LeanResearch.RepulsiveCoulomb.MetricHalfDiskBoundaryContinuation

/-! ISOLATED SOURCE-ONLY DRAFT. Strengthen the actual closed top extension by
proving that its newly exposed compact-edge values follow the original old
boundary arclength. This fact is needed by a length/width supremum and is not
silently inferred from agreement only on the old rectangle. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem point_exists_closed_translated_top_extension_with_edge
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hP : IsClosed P) {stripAngle R s delta ell : ℝ}
    (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi)
    (hR : 0 < R) (hs : 0 < s) (hsdelta : s < delta) (hsell : s < ell)
    (f : flatShearedRectangle (conePhase stripAngle) R s → P)
    (hf : @Isometry _ P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace f)
    (edge : Icc (0 : ℝ) ell → P)
    (hedge : @Isometry _ P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace edge)
    (hold : ∀ u : Icc (0 : ℝ) s,
      f (shearedCompactEdgePoint hR.le u) = edge ⟨u.1, u.2.1, u.2.2.trans hsell.le⟩)
    (C : @MetricFlatHalfDiskChart P (pointRegionMetricSpace ha y P)
      (f (shearedCompactEdgePoint hR.le ⟨s, hs.le, le_rfl⟩)))
    (hregular : ∀ r : Icc (0 : ℝ) R, 0 < r.1 →
      Nonempty (@MetricFlatDiskChart P (pointRegionMetricSpace ha y P)
        (f (shearedTopPoint (conePhase stripAngle) R s hs.le r)))) :
    ∃ h : ℝ, 0 < h ∧ s + h < delta ∧ ∃ hnewell : s + h < ell,
      ∃ F : flatShearedRectangle (conePhase stripAngle) R (s + h) → P,
        (∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z) ∧
        (∀ x : flatShearedRectangle (conePhase stripAngle) R s,
          ∀ hx : x.1 ∈ flatShearedRectangle (conePhase stripAngle) R (s + h), F ⟨x.1, hx⟩ = f x) ∧
        ∀ u : Icc (0 : ℝ) (s + h),
          F (shearedCompactEdgePoint hR.le u) = edge ⟨u.1, u.2.1, u.2.2.trans hnewell.le⟩ := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  let L := min (s / 2) (min ((ell - s) / 2) (C.radius / 2))
  have hL : 0 < L := lt_min (half_pos hs)
    (lt_min (half_pos (sub_pos.mpr hsell)) (half_pos C.radius_pos))
  have hLs : L < s := (min_le_left _ _).trans_lt (half_lt_self hs)
  have hLell : L < ell - s :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self (sub_pos.mpr hsell))
  have hLC : L < C.radius :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self C.radius_pos)
  let d := min delta (s + L / 2)
  have hsd : s < d := lt_min hsdelta (by linarith)
  obtain ⟨h, hh, hhD, F, hdF, hFold⟩ := point_exists_closed_translated_top_extension
    ha y hP stripAngle_pos stripAngle_lt_pi hR hs hsd hsell f hf edge hedge hold C hregular
  have hnewdelta : s + h < delta := hhD.trans_le (min_le_left _ _)
  have hhL : h < L := by
    have hh' := hhD.trans_le (min_le_right delta (s + L / 2))
    linarith
  have hnewell : s + h < ell := by linarith
  have hF : Isometry F := Isometry.of_dist_eq hdF
  have hinc := flatShearedRectangle_mono (v := conePhase stripAngle) (R := R) le_rfl
    (show s ≤ s + h by linarith)
  let qold := shearedCompactEdgePoint (v := conePhase stripAngle) hR.le ⟨s, hs.le, le_rfl⟩
  let q := shearedCompactEdgePoint (v := conePhase stripAngle) hR.le
    (⟨s, hs.le, by linarith⟩ : Icc (0 : ℝ) (s + h))
  let u₁ : Icc (0 : ℝ) s := ⟨s - L, by constructor <;> linarith⟩
  let q₁old := shearedCompactEdgePoint (v := conePhase stripAngle) hR.le u₁
  let q₁ := shearedCompactEdgePoint (v := conePhase stripAngle) hR.le
    (⟨s - L, u₁.2.1, by linarith [u₁.2.2]⟩ : Icc (0 : ℝ) (s + h))
  have hFq : F q = f qold := hFold qold (hinc qold.2)
  have hFq₁ : F q₁ = f q₁old := hFold q₁old (hinc q₁old.2)
  let C' : MetricFlatHalfDiskChart P (F q) := hFq.symm ▸ C
  have hC'radius : C'.radius = C.radius := by
    have htransport {p q : P} (D : MetricFlatHalfDiskChart P p) (he : p = q) :
        (he ▸ D : MetricFlatHalfDiskChart P q).radius = D.radius := by
      cases he
      rfl
    exact htransport C hFq.symm
  let τ : Icc (-L) L → Icc (0 : ℝ) ell := fun t ↦
    ⟨s - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
  have hτ : Isometry τ := by
    apply Isometry.of_dist_eq
    intro t u
    change |(s - t.1) - (s - u.1)| = |t.1 - u.1|
    rw [show (s - t.1) - (s - u.1) = -(t.1 - u.1) by ring, abs_neg]
  have hρ0 : (edge ∘ τ) (complexSymmetricIntervalZero hL) = F q := by
    rw [hFq, hold]
    apply congrArg edge
    apply Subtype.ext
    simp [τ, complexSymmetricIntervalZero]
  let b : Icc (-L) L := ⟨L, by constructor <;> linarith⟩
  have hρb : (edge ∘ τ) b = F q₁ := by
    rw [hFq₁, hold]
    rfl
  have hqcoord : translatedSupportingRigid stripAngle s q.1 = 0 := translatedSupportingRigid_top_origin stripAngle s
  have hq₁coord : translatedSupportingRigid stripAngle s q₁.1 = (b.1 : ℂ) := by
    change translatedSupportingRigid stripAngle s (flatShearedPoint (conePhase stripAngle) 0 (s - L)) = (L : ℂ)
    rw [translatedSupportingRigid_sheared]
    simp
  refine ⟨h, hh, hnewdelta, hnewell, F, hdF, hFold, ?_⟩
  intro u
  by_cases hus : u.1 ≤ s
  · let uold : Icc (0 : ℝ) s := ⟨u.1, u.2.1, hus⟩
    exact (hFold (shearedCompactEdgePoint hR.le uold)
      (shearedCompactEdgePoint hR.le u).2).trans (hold uold)
  · have hsu : s < u.1 := lt_of_not_ge hus
    let t : Icc (-L) L := ⟨s - u.1, by constructor <;> linarith [u.2.2]⟩
    have hxt : translatedSupportingRigid stripAngle s (shearedCompactEdgePoint (v := conePhase stripAngle) hR.le u).1 =
        (t.1 : ℂ) := by
      rw [show (shearedCompactEdgePoint (v := conePhase stripAngle) hR.le u).1 =
        flatShearedPoint (conePhase stripAngle) 0 u.1 from rfl, translatedSupportingRigid_sheared]
      simp [t]
    have heq := metricHalfDisk_boundary_continuation_unique F hF q q₁
      (translatedSupportingRigid stripAngle s) hqcoord C' hL (by rw [hC'radius]; exact hLC)
      (edge ∘ τ) (hedge.comp hτ) hρ0 b hL.ne' hq₁coord hρb
      (shearedCompactEdgePoint hR.le u) t hxt
    refine heq.trans ?_
    apply congrArg edge
    apply Subtype.ext
    dsimp [τ, t]
    ring

end RepulsiveCoulomb
