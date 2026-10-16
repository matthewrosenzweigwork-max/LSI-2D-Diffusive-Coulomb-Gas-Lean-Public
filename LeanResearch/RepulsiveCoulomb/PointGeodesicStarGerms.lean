import LeanResearch.RepulsiveCoulomb.PointGeodesicSubedge
import LeanResearch.RepulsiveCoulomb.PointGeodesicRadialGerms

/-! A finite family of genuine outgoing geodesic edges has one common cone
chart and one common positive intrinsic radius. Endpoint intersections force
its equal-radius direction points to be distinct. This is local star geometry;
no unbounded sector or global developing-map injectivity is asserted. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- A common strictly positive radius is constructed for a finite family. -/
theorem exists_common_positive_radius {ι : Type*} [Finite ι]
    (L : ι → ℝ) (hL : ∀ i, 0 < L i) {R : ℝ} (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ∀ i, r < L i := by
  classical
  letI := Fintype.ofFinite ι
  have aux (S : Finset ι) : ∃ r : ℝ, 0 < r ∧ r < R ∧ ∀ i ∈ S, r < L i := by
    induction S using Finset.induction_on with
    | empty => exact ⟨R / 2, by positivity, by linarith, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨r, hr, hrR, hrS⟩ := ih
      refine ⟨min r (L i / 2), lt_min hr (div_pos (hL i) (by norm_num)),
        (min_le_left _ _).trans_lt hrR, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (min_le_right _ _).trans_lt (by linarith [hL j])
      · exact (min_le_left _ _).trans_lt (hrS j hj)
  obtain ⟨r, hr, hrR, hri⟩ := aux Finset.univ
  exact ⟨r, hr, hrR, fun i ↦ hri i (Finset.mem_univ i)⟩

/-- Reverse an already constructed exact geodesic edge. -/
def pointGeodesicReverseEdge {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (e : PointGeodesicTreeEdge a y) : PointGeodesicTreeEdge a y where
  start := e.finish
  finish := e.start
  distinct := e.distinct.symm
  curve := e.curve ∘ unitInterval.symm
  curve_start := by
    change e.curve (unitInterval.symm (0 : unitInterval)) = e.finish
    rw [unitInterval.symm_zero]
    exact e.curve_finish
  curve_finish := by
    change e.curve (unitInterval.symm (1 : unitInterval)) = e.start
    rw [unitInterval.symm_one]
    exact e.curve_start
  continuous := e.continuous.comp unitInterval.continuous_symm
  geodesic := by
    intro s t
    simp only [Function.comp_apply, e.geodesic, unitInterval.coe_symm_eq,
      pointSmoothConformalEDist_comm a y e.finish e.start]
    rw [show (1 - t.1) - (1 - s.1) = -(t.1 - s.1) by ring, abs_neg]

theorem pointGeodesicReverseEdge_range {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (e : PointGeodesicTreeEdge a y) :
    range (pointGeodesicReverseEdge e).curve = range e.curve := by
  change range (e.curve ∘ unitInterval.symm) = range e.curve
  exact unitInterval.symm_bijective.surjective.range_comp e.curve

/-- The actual full target disk is retained along with uniform radiality. -/
theorem exists_pointConformal_radial_full_disk {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ R : ℝ, 0 < R ∧ e p = 0 ∧
      {u : ℂ | (pointSmoothConformalEDist a y u p).toReal ≤ R} ⊆ e.source ∧
      Set.BijOn e {u : ℂ | (pointSmoothConformalEDist a y u p).toReal ≤ R}
        {w : ℂ | ‖w‖ ≤ R} ∧
      (∀ u, (pointSmoothConformalEDist a y u p).toReal ≤ R →
        ∀ v, (pointSmoothConformalEDist a y v p).toReal ≤ R →
          (pointSmoothConformalEDist a y u v).toReal = pointClassicalConeDist a y p (e u) (e v)) ∧
      ∀ z : ℂ, (pointSmoothConformalEDist a y z p).toReal ≤ R →
        ∀ γ : Icc (0 : ℝ) 1 → ℂ,
          γ ⟨0, by norm_num⟩ = p → γ ⟨1, by norm_num⟩ = z →
          (∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
            |t.1 - s.1| * (pointSmoothConformalEDist a y p z).toReal) →
          ∀ t, e (γ t) = t.1 • e z := by
  obtain ⟨e, R, hR, hep, hsource, hbij, hmetric⟩ :=
    exists_pointConformal_classical_cone_disk ha y p
  have hpp : (pointSmoothConformalEDist a y p p).toReal ≤ R := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact hR.le
  refine ⟨e, R, hR, hep, hsource, hbij, hmetric, ?_⟩
  intro z hz γ h0 h1 hd
  have hL : (pointSmoothConformalEDist a y p z).toReal = ‖e z‖ := by
    rw [pointSmoothConformalEDist_comm a y p z, hmetric z hz p hpp, hep,
      pointClassicalConeDist_apex]
  have hball (t : Icc (0 : ℝ) 1) :
      (pointSmoothConformalEDist a y (γ t) p).toReal ≤ R := by
    have h := hd t ⟨0, by norm_num⟩
    rw [h0, zero_sub, abs_neg, abs_of_nonneg t.2.1] at h
    rw [h]
    have hbound : (pointSmoothConformalEDist a y p z).toReal ≤ R := by
      rwa [pointSmoothConformalEDist_comm a y p z]
    exact (mul_le_of_le_one_left ENNReal.toReal_nonneg t.2.2).trans hbound
  intro t
  apply classicalCone_geodesic_from_apex_nonneg (α := coalescedPointExponent a y p / 2)
    (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num))
    (fun s => e (γ s)) (e z) (by rw [h0, hep]) (by rw [h1])
  intro s u
  change pointClassicalConeDist a y p (e (γ s)) (e (γ u)) = _
  rw [← hmetric (γ s) (hball s) (γ u) (hball u), hd, hL]


/-- All outgoing edges are radial in the same actual cone chart, at the same
positive intrinsic radius. Distinct edges have distinct direction points. -/
theorem exists_pointConformal_finite_star_germs {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {ι : Type*} [Finite ι]
    (E : ι → PointGeodesicTreeEdge a y) (p : ℂ)
    (hstart : ∀ i, (E i).start = p)
    (hpair : ∀ i j, i ≠ j → ∀ z ∈ range (E i).curve, z ∈ range (E j).curve →
      z = (E i).start ∨ z = (E i).finish) {B : ℝ} (hB : 0 < B) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ R r : ℝ,
      0 < r ∧ r < R ∧ r < B ∧ e p = 0 ∧
      {u : ℂ | (pointSmoothConformalEDist a y u p).toReal ≤ R} ⊆ e.source ∧
      Set.BijOn e {u : ℂ | (pointSmoothConformalEDist a y u p).toReal ≤ R}
        {w : ℂ | ‖w‖ ≤ R} ∧
      (∀ u, (pointSmoothConformalEDist a y u p).toReal ≤ R →
        ∀ v, (pointSmoothConformalEDist a y v p).toReal ≤ R →
          (pointSmoothConformalEDist a y u v).toReal = pointClassicalConeDist a y p (e u) (e v)) ∧
      ∃ τ : ι → Icc (0 : ℝ) 1,
        (∀ i, 0 < (τ i).1 ∧ (τ i).1 < 1) ∧
        (∀ i, (pointSmoothConformalEDist a y ((E i).curve (τ i)) p).toReal = r) ∧
        (∀ i, ‖e ((E i).curve (τ i))‖ = r) ∧
        Function.Injective (fun i ↦ e ((E i).curve (τ i))) ∧
        ∀ i s, e ((E i).curve (pointEdgeSubparam ⟨0, by norm_num⟩ (τ i) s)) =
          s.1 • e ((E i).curve (τ i)) := by
  classical
  obtain ⟨e, R, hR, hep, hsource, hbij, hmetric, hradial⟩ :=
    exists_pointConformal_radial_full_disk ha y p
  let L : ι → ℝ := fun i ↦ (pointSmoothConformalEDist a y (E i).start (E i).finish).toReal
  have hL (i : ι) : 0 < L i := ENNReal.toReal_pos
    (pointSmoothConformalEDist_ne_zero ha y (E i).distinct)
    (pointSmoothConformalEDist_lt_top ha y _ _).ne
  obtain ⟨r, hr, hrRB, hrL⟩ := exists_common_positive_radius L hL (lt_min hR hB)
  have hrR : r < R := hrRB.trans_le (min_le_left _ _)
  have hrB : r < B := hrRB.trans_le (min_le_right _ _)
  let τ (i : ι) : Icc (0 : ℝ) 1 := ⟨r / L i,
    (div_pos hr (hL i)).le, ((div_lt_one (hL i)).mpr (hrL i)).le⟩
  have hτ (i : ι) : 0 < (τ i).1 ∧ (τ i).1 < 1 :=
    ⟨div_pos hr (hL i), (div_lt_one (hL i)).mpr (hrL i)⟩
  have hdist (i : ι) :
      (pointSmoothConformalEDist a y ((E i).curve (τ i)) p).toReal = r := by
    have h := (E i).geodesic (τ i) ⟨0, by norm_num⟩
    have h0 : (E i).curve ⟨0, by norm_num⟩ = p := ((E i).curve_start).trans (hstart i)
    rw [h0, zero_sub, abs_neg, abs_of_nonneg (τ i).2.1] at h
    change (pointSmoothConformalEDist a y ((E i).curve (τ i)) p).toReal =
      r / L i * L i at h
    simpa only [div_mul_cancel₀ _ (hL i).ne'] using h
  have hb (i : ι) : (pointSmoothConformalEDist a y ((E i).curve (τ i)) p).toReal ≤ R :=
    (hdist i).le.trans hrR.le
  have hpp : (pointSmoothConformalEDist a y p p).toReal ≤ R := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact hR.le
  have hn (i : ι) : ‖e ((E i).curve (τ i))‖ = r := by
    have h := hdist i
    rw [hmetric _ (hb i) p hpp, hep, pointClassicalConeDist_apex] at h
    exact h
  refine ⟨e, R, r, hr, hrR, hrB, hep, hsource, hbij, hmetric, τ, hτ, hdist, hn, ?_, ?_⟩
  · intro i j hij
    by_contra hne
    have hq : (E i).curve (τ i) = (E j).curve (τ j) :=
      e.injOn (hsource (hb i)) (hsource (hb j)) hij
    have hends := hpair i j hne _ (mem_range_self _) ⟨τ j, hq.symm⟩
    have hi := pointGeodesicTree_edges_injective ha y (E i)
    rcases hends with h0 | h1
    · have ht := congrArg Subtype.val (hi (h0.trans (E i).curve_start.symm))
      change (τ i).1 = 0 at ht
      linarith [(hτ i).1]
    · have ht := congrArg Subtype.val (hi (h1.trans (E i).curve_finish.symm))
      change (τ i).1 = 1 at ht
      linarith [(hτ i).2]
  · intro i s
    let δ := pointGeodesicSubedge ha y (E i) ⟨0, by norm_num⟩ (τ i) (hτ i).1
    have hδ0 : δ.curve ⟨0, by norm_num⟩ = p := by
      rw [δ.curve_start]
      exact ((E i).curve_start).trans (hstart i)
    have hδ1 : δ.curve ⟨1, by norm_num⟩ = (E i).curve (τ i) := δ.curve_finish
    have hd := δ.geodesic
    change ∀ s t, (pointSmoothConformalEDist a y (δ.curve s) (δ.curve t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y ((E i).curve ⟨0, by norm_num⟩)
        ((E i).curve (τ i))).toReal at hd
    rw [(E i).curve_start, hstart i] at hd
    exact hradial _ (hb i) δ.curve hδ0 hδ1 hd s

end RepulsiveCoulomb
