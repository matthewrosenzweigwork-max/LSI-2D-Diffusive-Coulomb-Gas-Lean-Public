import LeanResearch.RepulsiveCoulomb.PointFullLineWidthSupremum
import LeanResearch.RepulsiveCoulomb.DirectedFlatIsometryUnion

/-! The full-line strip is constructed as the union of symmetric finite
normal rectangles, all of the same positive width. Length compatibility is
proved from an actual aligned halfdisk at the central bottom point. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem point_exists_fullLine_uniform_normal_strip_of_clearance
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P S : Set ℂ} (hP : IsClosed P) (line : ℝ → P)
    (hline : @Isometry ℝ P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace line)
    (hboundary : frontier P = range (fun r ↦ (line r).1))
    (H : ∀ r : ℝ, @MetricFlatHalfDiskChart P (pointRegionMetricSpace ha y P) (line r))
    (hmarks : ∀ p ∈ interior P, coalescedPointExponent a y p ≠ 0 → p ∈ S)
    {delta : ℝ} (hdelta : 0 < delta)
    (hclear : ∀ p ∈ S, ∀ r : ℝ,
      delta < (pointSmoothConformalEDist a y p (line r).1).toReal) :
    ∃ F : flatFullNormalStrip delta → P,
      (∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z) ∧
      ∀ r : ℝ, ∀ hr : (r : ℂ) ∈ flatFullNormalStrip delta,
        F ⟨(r : ℂ), hr⟩ = line r := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  let K := fun n : ℕ ↦ flatNormalRectangle (-(n + 1)) (n + 1) delta
  have hex (n : ℕ) : ∃ G : K n → P, Isometry G ∧
      (∀ r : ℝ, ∀ hr : (r : ℂ) ∈ K n, G ⟨(r : ℂ), hr⟩ = line r) ∧
      ∀ z, 0 < z.1.im → Nonempty (MetricFlatDiskChart P (G z)) := by
    let b : ℝ := n + 1
    have hb : 0 < b := by dsimp [b]; positivity
    have hlen : 0 < b - (-b) := by linarith
    obtain ⟨f, hfd, hfb⟩ := point_exists_fullLine_fixed_width_rectangle ha y hP line hline
      hboundary H hmarks hdelta hlen (-b) hclear
    have hfi : Isometry f := Isometry.of_dist_eq hfd
    let incl : K n → flatShearedRectangle Complex.I (b - (-b)) delta := flatNormalRectangleToSheared
    have hinc : Isometry incl := flatNormalRectangleToSheared_isometry
    let G := f ∘ incl
    refine ⟨G, hfi.comp hinc, ?_, ?_⟩
    · intro r hr
      let q := r - (-b)
      have he : (incl ⟨(r : ℂ), hr⟩).1 = (q : ℂ) := by
        simp only [incl, flatNormalRectangleToSheared, q, b, Complex.ofReal_sub]
      have hq : (q : ℂ) ∈ flatShearedRectangle Complex.I (b - (-b)) delta :=
        he ▸ (incl ⟨(r : ℂ), hr⟩).2
      have hi : incl ⟨(r : ℂ), hr⟩ = ⟨(q : ℂ), hq⟩ := Subtype.ext he
      change f (incl ⟨(r : ℂ), hr⟩) = line r
      rw [hi, hfb q hq]
      have hc : -b + q = r := by dsimp [q]; ring
      rw [hc]
    · intro z hz
      have hreg := pointFullLine_normalStage_flatChart ha y (fun r ↦ (line r).1)
        (fun r t ↦ hline.dist_eq r t) hboundary hmarks hlen hdelta.le le_rfl hclear f hfd
        (fun r ↦ congrArg Subtype.val (hfb r.1 (normalRectangleBottom r.2 hdelta.le).2))
      apply hreg (incl z)
      simpa only [incl, flatNormalRectangleToSheared, Complex.sub_im, Complex.ofReal_im, sub_zero] using hz
  choose f hf hfb hreg using hex
  have hmono {i j : ℕ} (hij : i ≤ j) : K i ⊆ K j := by
    have hh : (i : ℝ) + 1 ≤ j + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  have hwindow (n : ℕ) : ∀ r ∈ Icc (0 - ((n : ℝ) + 1) / 2) (0 + ((n : ℝ) + 1) / 2),
      (r : ℂ) ∈ K n := by
    intro r hr
    have hn : (0 : ℝ) < n + 1 := by positivity
    change (r : ℂ).re ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) ∧ (r : ℂ).im ∈ Icc (0 : ℝ) delta
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨⟨by linarith [hr.1], by linarith [hr.2]⟩, le_rfl, hdelta.le⟩
  have hbottom (n : ℕ) : ∀ r : ℝ, ∀ hr : (r : ℂ) ∈ K n,
      f n ⟨(r : ℂ), hr⟩ = line (0 + r) := by
    intro r hr
    simpa only [zero_add] using hfb n r hr
  have hinterior (n : ℕ) (z : K n) (hz : z.1 ∈ interior (K n)) :
      Nonempty (MetricFlatDiskChart P (f n z)) :=
    hreg n z (flatNormalRectangle_interior_im_pos hz)
  have hcompat : ∀ i j : ℕ, ∀ z (hi : z ∈ K i) (hj : z ∈ K j),
      f i ⟨z, hi⟩ = f j ⟨z, hj⟩ := by
    intro i j z hi hj
    rcases le_total i j with hij | hji
    · exact metricFullLine_stages_agree line hline 0 0 (by simpa only [zero_add] using H 0)
        (flatNormalRectangle_convex _ _ _) (flatNormalRectangle_compact _ _ _).isClosed
        (flatNormalRectangle_interior_nonempty (by
          have h : (0 : ℝ) < (i : ℝ) + 1 := by positivity
          linarith) hdelta)
        (hmono hij) (by positivity) (hwindow i)
        (f i) (f j) (hf i) (hf j) (hbottom i) (hbottom j) (hinterior i) ⟨z, hi⟩
    · exact (metricFullLine_stages_agree line hline 0 0 (by simpa only [zero_add] using H 0)
        (flatNormalRectangle_convex _ _ _) (flatNormalRectangle_compact _ _ _).isClosed
        (flatNormalRectangle_interior_nonempty (by
          have h : (0 : ℝ) < (j : ℝ) + 1 := by positivity
          linarith) hdelta)
        (hmono hji) (by positivity) (hwindow j)
        (f j) (f i) (hf j) (hf i) (hbottom j) (hbottom i) (hinterior j) ⟨z, hj⟩).symm
  have hdir : Directed (· ⊆ ·) K := fun i j ↦ ⟨max i j, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩
  have hsource := flatFullNormalStrip_eq_iUnion delta
  let incl : flatFullNormalStrip delta → ⋃ n, K n := fun z ↦ ⟨z.1, hsource ▸ z.2⟩
  have hinc : Isometry incl := fun _ _ ↦ rfl
  let F := directedFlatUnion K f hcompat ∘ incl
  have hF : Isometry F := (directedFlatUnion_isometry K f hdir hcompat hf).comp hinc
  refine ⟨F, fun x z ↦ hF.dist_eq x z, ?_⟩
  intro r hr
  obtain ⟨n, hn⟩ := mem_iUnion.mp (hsource ▸ hr)
  exact (directedFlatUnion_of_mem K f hcompat (incl ⟨(r : ℂ), hr⟩) n hn).trans (hfb n r hn)

end RepulsiveCoulomb
