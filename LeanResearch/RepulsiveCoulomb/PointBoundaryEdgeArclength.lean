import LeanResearch.RepulsiveCoulomb.PointActualMarkedDirection

/-! SOURCE-ONLY AFTER THE UNIFORM-STRIP FREEZE. Construct the literal
arclength clock of one actual minimizing adjacent boundary edge. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

def pointEdgeArclength {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    (E : PointGeodesicTreeEdge a y) (t : Icc (0 : ℝ) (pointActualEdgeLength E)) : ℂ :=
  E.curve ⟨t.1/pointActualEdgeLength E,
    div_nonneg t.2.1 (pointActualEdgeLength_pos ha y E).le,
    (div_le_one (pointActualEdgeLength_pos ha y E)).mpr t.2.2⟩

theorem pointEdgeArclength_metric {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    (E : PointGeodesicTreeEdge a y) (t u : Icc (0 : ℝ) (pointActualEdgeLength E)) :
    (pointSmoothConformalEDist a y (pointEdgeArclength ha y E t) (pointEdgeArclength ha y E u)).toReal = dist t u := by
  have hL := pointActualEdgeLength_pos ha y E
  rw [pointEdgeArclength,pointEdgeArclength,E.geodesic]
  change |u.1/pointActualEdgeLength E-t.1/pointActualEdgeLength E| * pointActualEdgeLength E = dist t.1 u.1
  rw [← sub_div,abs_div,abs_of_pos hL,div_mul_cancel₀ _ hL.ne',Real.dist_eq,abs_sub_comm]

@[simp] theorem pointEdgeArclength_zero {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    (E : PointGeodesicTreeEdge a y) :
    pointEdgeArclength ha y E ⟨0,le_rfl,(pointActualEdgeLength_pos ha y E).le⟩=E.start := by
  have he : (⟨(0:ℝ)/pointActualEdgeLength E,by simp,
      (div_le_one (pointActualEdgeLength_pos ha y E)).mpr (pointActualEdgeLength_pos ha y E).le⟩ : unitInterval)=⟨0, by norm_num⟩ := by
    apply Subtype.ext
    simp
  change E.curve _=E.start
  rw [he]
  exact E.curve_start

theorem pointEdgeArclength_mem {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    (E : PointGeodesicTreeEdge a y) (t : Icc (0 : ℝ) (pointActualEdgeLength E)) :
    pointEdgeArclength ha y E t∈range E.curve := ⟨_,rfl⟩

/-- The sampled actual initial raw angle is expressed on its actual arclength
interval, rather than an abstract existence of an initial direction. -/
theorem PointRetainedConeNeighborhood.exists_edge_arclength_radial_germ
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p) (hC : C.Admissible)
    (E : PointGeodesicTreeEdge a y) (hE0 : E.start=p) (hEP : ∀ t,E.curve t∈P) :
    ∃ d : ℝ, 0<d ∧ d<C.radius ∧ d<pointActualEdgeLength E ∧
      ∀ t : Icc (0 : ℝ) (pointActualEdgeLength E), t.1≤d →
        C.chart (pointEdgeArclength ha y E t)=pointRadialSectorPoint t.1
          (C.actualInitialRawAngle ha y hC E hE0 hEP) := by
  obtain ⟨d,τ,hd,hdC,hτ,hτ1,hdr,hpolar⟩ := C.actualInitialRawAngle_sample ha y hC E hE0 hEP
  have hlen := pointActualEdgeLength_pos ha y E
  have hdclock : τ.1*pointActualEdgeLength E=d := by
    have h := E.geodesic τ ⟨0, by norm_num⟩
    rw [E.curve_start] at h
    change (pointSmoothConformalEDist a y (E.curve τ) E.start).toReal =
      |0 - τ.1| * pointActualEdgeLength E at h
    rw [hE0,zero_sub,abs_neg,abs_of_nonneg τ.2.1,hdr] at h
    exact h.symm
  have hdlen : d<pointActualEdgeLength E := by
    rw [← hdclock]
    exact mul_lt_of_lt_one_left hlen hτ1
  refine ⟨d,hd,hdC,hdlen,?_⟩
  intro t htd
  let u : unitInterval := ⟨t.1/d,div_nonneg t.2.1 hd.le,(div_le_one hd).mpr htd⟩
  have hq : pointEdgeSubparam 0 τ u =
      (⟨t.1/pointActualEdgeLength E,div_nonneg t.2.1 hlen.le,(div_le_one hlen).mpr t.2.2⟩ : unitInterval) := by
    apply Subtype.ext
    simp only [pointEdgeSubparam,AffineMap.lineMap_apply_module',Set.Icc.coe_zero,sub_zero,smul_eq_mul,add_zero]
    change (t.1/d)*τ.1=t.1/pointActualEdgeLength E
    apply (eq_div_iff hlen.ne').mpr
    calc
      (t.1/d)*τ.1*pointActualEdgeLength E=(t.1/d)*(τ.1*pointActualEdgeLength E) := by ring
      _=t.1 := by rw [hdclock,div_mul_cancel₀ _ hd.ne']
  have h := hpolar u
  rw [hq] at h
  simpa only [pointEdgeArclength, show u.1*d=t.1 from div_mul_cancel₀ _ hd.ne'] using h

end RepulsiveCoulomb
