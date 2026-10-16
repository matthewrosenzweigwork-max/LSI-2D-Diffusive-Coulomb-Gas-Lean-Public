module

public import LeanResearch.RepulsiveCoulomb.PointTranslatedLongitudinalExtension
public import LeanResearch.RepulsiveCoulomb.PointActualGeodesicContinuation
public import LeanResearch.RepulsiveCoulomb.PointActualMarkedDirection

@[expose] public section

/-! SOURCE-ONLY ASSEMBLY. Construct an actual minimizing finite horizontal
row of a finite translated rectangle and a complete ambient clock preserving
that exact row. The ambient ray is not asserted to remain in P after the row.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem flatShearedPoint_dist_parallel (v : ℂ) (r t u : ℝ) :
    dist (flatShearedPoint v r u) (flatShearedPoint v t u) = dist r t := by
  rw [dist_eq_norm]
  have he : flatShearedPoint v r u - flatShearedPoint v t u = ((r-t : ℝ) : ℂ) := by
    unfold flatShearedPoint
    push_cast
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, Real.dist_eq]

theorem point_exists_translated_row_clock
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {v : ℂ} {R s : ℝ} (hR : 0 < R)
    (f : flatShearedRectangle v R s → P)
    (hf : @Isometry _ P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace f)
    (u : Icc (0 : ℝ) s) :
    ∃ E : PointGeodesicTreeEdge a y,
      E.start = (f (shearedCompactEdgePoint hR.le u)).1 ∧
      E.finish = (f (shearedRightPoint hR.le u)).1 ∧
      pointActualEdgeLength E = R ∧ (∀ t, E.curve t ∈ P) ∧
      ∃ r : ℝ → ℂ, Continuous r ∧ r 0 = E.start ∧
        (∀ t ∈ Ici (0 : ℝ), ∀ w ∈ Ici (0 : ℝ),
          (pointSmoothConformalEDist a y (r t) (r w)).toReal = dist t w) ∧
        (∀ t : unitInterval, E.curve t = r (pointActualEdgeLength E * t.1)) ∧
        ∀ t : Icc (0 : ℝ) R,
          r t.1 = (f ⟨flatShearedPoint v t.1 u.1, t.1, t.2, u.1, u.2, rfl⟩).1 := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  let q : unitInterval → flatShearedRectangle v R s := fun t ↦
    ⟨flatShearedPoint v (R*t.1) u.1, R*t.1,
      ⟨mul_nonneg hR.le t.2.1, mul_le_of_le_one_right hR.le t.2.2⟩, u.1, u.2, rfl⟩
  let c : unitInterval → ℂ := fun t ↦ (f (q t)).1
  have hq0 : q 0 = shearedCompactEdgePoint hR.le u := by
    apply Subtype.ext
    simp [q, shearedCompactEdgePoint]
  have hq1 : q 1 = shearedRightPoint hR.le u := by
    apply Subtype.ext
    simp [q, shearedRightPoint]
  have hd (t w : unitInterval) :
      (pointSmoothConformalEDist a y (c t) (c w)).toReal = |w.1-t.1| * R := by
    change dist (f (q t)) (f (q w)) = _
    rw [hf.dist_eq]
    change dist (flatShearedPoint v (R*t.1) u.1) (flatShearedPoint v (R*w.1) u.1) = _
    rw [flatShearedPoint_dist_parallel, Real.dist_eq, ← mul_sub, abs_mul,
      abs_of_pos hR, abs_sub_comm, mul_comm]
  have hD : (pointSmoothConformalEDist a y (c 0) (c 1)).toReal = R := by
    simpa using hd 0 1
  have hneq : c 0 ≠ c 1 := by
    intro he
    rw [he, pointSmoothConformalEDist_self, ENNReal.toReal_zero] at hD
    exact hR.ne' hD.symm
  have hgeo : ∀ t w : unitInterval,
      (pointSmoothConformalEDist a y (c t) (c w)).toReal =
        |w.1-t.1| * (pointSmoothConformalEDist a y (c 0) (c 1)).toReal := by
    intro t w
    rw [hD]
    exact hd t w
  let E : PointGeodesicTreeEdge a y :=
    ⟨c 0, c 1, hneq, c, rfl, rfl, pointConformal_geodesic_continuous ha y c hgeo, hgeo⟩
  have hE0 : E.start = (f (shearedCompactEdgePoint hR.le u)).1 := congrArg (fun z ↦ (f z).1) hq0
  have hE1 : E.finish = (f (shearedRightPoint hR.le u)).1 := congrArg (fun z ↦ (f z).1) hq1
  have hEL : pointActualEdgeLength E = R := hD
  have hEP : ∀ t, E.curve t ∈ P := fun t ↦ (f (q t)).2
  obtain ⟨γ, hγ0, hγclosed, _, hγd, hpreserve⟩ := exists_pointConformal_prescribed_complete_ray ha y E
  let r : ℝ → ℂ := γ ∘ Real.toNNReal
  have hrc : Continuous r := hγclosed.continuous.comp continuous_real_toNNReal
  have hr0 : r 0 = E.start := by simpa [r] using hγ0
  have hrd : ∀ t ∈ Ici (0 : ℝ), ∀ w ∈ Ici (0 : ℝ),
      (pointSmoothConformalEDist a y (r t) (r w)).toReal = dist t w := by
    intro t ht w hw
    change (pointSmoothConformalEDist a y (γ t.toNNReal) (γ w.toNNReal)).toReal = _
    rw [hγd, NNReal.dist_eq, Real.toNNReal_of_nonneg ht, Real.toNNReal_of_nonneg hw, Real.dist_eq]
    rfl
  have hclock (t : unitInterval) : E.curve t = r (pointActualEdgeLength E * t.1) := by
    have hnn : (pointActualEdgeLength E * t.1).toNNReal =
        (⟨pointActualEdgeLength E * t.1, mul_nonneg (pointActualEdgeLength_pos ha y E).le t.2.1⟩ : NNReal) := by
      exact Real.toNNReal_of_nonneg (mul_nonneg (pointActualEdgeLength_pos ha y E).le t.2.1)
    exact ((congrArg γ hnn).trans (hpreserve t)).symm
  refine ⟨E, hE0, hE1, hEL, hEP, r, hrc, hr0, hrd, hclock, ?_⟩
  intro t
  let τ : unitInterval := ⟨t.1/R, div_nonneg t.2.1 hR.le, (div_le_one hR).mpr t.2.2⟩
  have htR : R*τ.1 = t.1 := mul_div_cancel₀ _ hR.ne'
  have htime : pointActualEdgeLength E * τ.1 = t.1 := by rw [hEL, htR]
  calc
    r t.1 = E.curve τ := (congrArg r htime.symm).trans (hclock τ).symm
    _ = _ := by
      change (f (q τ)).1 = _
      apply congrArg (fun z ↦ (f z).1)
      apply Subtype.ext
      change flatShearedPoint v (R*τ.1) u.1 = flatShearedPoint v t.1 u.1
      rw [htR]

end RepulsiveCoulomb
