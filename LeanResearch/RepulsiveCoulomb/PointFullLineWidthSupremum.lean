module

public import LeanResearch.RepulsiveCoulomb.PointFullLineInitialRectangle
public import LeanResearch.RepulsiveCoulomb.PointFullLineStageFlatCharts
public import LeanResearch.RepulsiveCoulomb.PointNormalFullTopExtension
public import LeanResearch.RepulsiveCoulomb.MetricFullLineStageCompatibility
public import LeanResearch.RepulsiveCoulomb.FullNormalStripSourceGeometry
public import LeanResearch.RepulsiveCoulomb.ShearedRectangleWidthSupremum

@[expose] public section

/-! Actual fixed-width construction for each finite portion of a complete
clean boundary line. Initial patches, arbitrary-stage agreement, Cauchy
completion and compact full-top extension are all constructed. The actual
line return obstruction and the one global finite-mark clearance provide all
image regularity; there is no stage-chart or attainment premise. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem point_exists_fullLine_fixed_width_rectangle
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P S : Set ℂ} (hP : IsClosed P) (line : ℝ → P)
    (hline : @Isometry ℝ P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace line)
    (hboundary : frontier P = range (fun r ↦ (line r).1))
    (H : ∀ r : ℝ, @MetricFlatHalfDiskChart P (pointRegionMetricSpace ha y P) (line r))
    (hmarks : ∀ p ∈ interior P, coalescedPointExponent a y p ≠ 0 → p ∈ S)
    {delta R : ℝ} (hdelta : 0 < delta) (hR : 0 < R) (c : ℝ)
    (hclear : ∀ p ∈ S, ∀ r : ℝ,
      delta < (pointSmoothConformalEDist a y p (line r).1).toReal) :
    ∃ F : flatShearedRectangle Complex.I R delta → P,
      (∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z) ∧
      ∀ q : ℝ, ∀ hq : (q : ℂ) ∈ flatShearedRectangle Complex.I R delta,
        F ⟨(q : ℂ), hq⟩ = line (c + q) := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  letI : UniformSpace P := M.toUniformSpace
  letI : CompleteSpace P := pointRegionMetricSpace_complete ha y hP
  let K := fun s : ℝ ↦ flatShearedRectangle Complex.I R s
  let Bottom := fun (s : ℝ) (f : K s → P) ↦
    ∀ q : ℝ, ∀ hq : (q : ℂ) ∈ K s, f ⟨(q : ℂ), hq⟩ = line (c + q)
  let W : Set ℝ := {s | 0 < s ∧ s ≤ delta ∧ ∃ f : K s → P, Isometry f ∧ Bottom s f}
  obtain ⟨s0, hs0, hs0delta, f0, hf0, hfb0⟩ :=
    point_exists_fullLine_initial_rectangle ha y line hline H hR hdelta c
  have hbottom0 : Bottom s0 f0 := by
    intro q hq
    have hqr := (mem_flatShearedRectangle_I_iff.mp hq).1
    exact hfb0 ⟨q, hqr⟩
  have hs0W : s0 ∈ W := ⟨hs0, hs0delta.le, f0, Isometry.of_dist_eq hf0, hbottom0⟩
  have hWne : W.Nonempty := ⟨s0, hs0W⟩
  have hWbound : BddAbove W := ⟨delta, fun s hs ↦ hs.2.1⟩
  have hmaps : ∀ s : W, ∃ f : K s.1 → P, Isometry f ∧ Bottom s.1 f := fun s ↦ s.2.2.2
  choose f hf hfb using hmaps
  have hregAny {s : ℝ} (hs : 0 < s) (hsdelta : s ≤ delta)
      (g : K s → P) (hg : Isometry g) (hgb : Bottom s g) :
      ∀ z, 0 < z.1.im → Nonempty (MetricFlatDiskChart P (g z)) := by
    apply pointFullLine_normalStage_flatChart ha y (fun r ↦ (line r).1)
      (fun r t ↦ hline.dist_eq r t) hboundary hmarks hR hs.le hsdelta hclear g
      (fun x z ↦ hg.dist_eq x z)
    intro r
    exact congrArg Subtype.val (hgb r.1 (normalRectangleBottom r.2 hs.le).2)
  have hreg (s : W) (z : K s.1) (hz : z.1 ∈ interior (K s.1)) :
      Nonempty (MetricFlatDiskChart P (f s z)) :=
    hregAny s.2.1 s.2.2.1 (f s) (hf s) (hfb s) z (flatShearedRectangle_I_interior_im_pos hz)
  have hwindow (s : W) : ∀ q ∈ Icc (R / 2 - R / 2) (R / 2 + R / 2), (q : ℂ) ∈ K s.1 := by
    intro q hq
    apply mem_flatShearedRectangle_I_iff.mpr
    simpa only [Complex.ofReal_re, Complex.ofReal_im] using
      And.intro (show q ∈ Icc (0 : ℝ) R from ⟨by linarith [hq.1], by linarith [hq.2]⟩)
        (show (0 : ℝ) ∈ Icc 0 s.1 from ⟨le_rfl, s.2.1.le⟩)
  have hcompat : ∀ s t : W, ∀ z (hs : z ∈ K s.1) (ht : z ∈ K t.1),
      f s ⟨z, hs⟩ = f t ⟨z, ht⟩ := by
    intro s t z hs ht
    rcases le_total s.1 t.1 with hst | hts
    · exact metricFullLine_stages_agree line hline c (R / 2) (H (c + R / 2))
        (flatShearedRectangle_convex _ _ _) (flatShearedRectangle_compact _ _ _).isClosed
        (flatShearedRectangle_interior_nonempty (by simp) hR s.2.1)
        (flatShearedRectangle_mono le_rfl hst) (half_pos hR) (hwindow s)
        (f s) (f t) (hf s) (hf t) (hfb s) (hfb t) (hreg s) ⟨z, hs⟩
    · exact (metricFullLine_stages_agree line hline c (R / 2) (H (c + R / 2))
        (flatShearedRectangle_convex _ _ _) (flatShearedRectangle_compact _ _ _).isClosed
        (flatShearedRectangle_interior_nonempty (by simp) hR t.2.1)
        (flatShearedRectangle_mono le_rfl hts) (half_pos hR) (hwindow t)
        (f t) (f s) (hf t) (hf s) (hfb t) (hfb s) (hreg t) ⟨z, ht⟩).symm
  obtain ⟨F, hF, hFold⟩ := exists_shearedRectangle_supremum_isometry
    (by simp : ‖Complex.I‖ = 1) R hWne (fun s hs ↦ hs.1) hWbound f hf hcompat
  let Swidth := sSup W
  have hSpos : 0 < Swidth := hs0.trans_le (le_csSup hWbound hs0W)
  have hSdelta : Swidth ≤ delta := csSup_le hWne (fun s hs ↦ hs.2.1)
  have real_mem_of_mem {q s t : ℝ} (ht : 0 ≤ t) (hq : (q : ℂ) ∈ K s) : (q : ℂ) ∈ K t := by
    apply mem_flatShearedRectangle_I_iff.mpr
    exact ⟨(mem_flatShearedRectangle_I_iff.mp hq).1, by simpa using And.intro (le_refl (0 : ℝ)) ht⟩
  have hFb : Bottom Swidth F := by
    intro q hq
    have hq0 := real_mem_of_mem hs0.le hq
    exact (hFold ⟨s0, hs0W⟩ ⟨(q : ℂ), hq0⟩).trans (hfb ⟨s0, hs0W⟩ q hq0)
  have hSequal : Swidth = delta := by
    apply le_antisymm hSdelta
    by_contra hn
    have hSlt : Swidth < delta := lt_of_not_ge hn
    have htop : ∀ r : Icc (0 : ℝ) R,
        Nonempty (MetricFlatDiskChart P (F (shearedTopPoint Complex.I R Swidth hSpos.le r))) := by
      intro r
      apply hregAny hSpos hSdelta F hF hFb
      simpa [shearedTopPoint, flatShearedPoint] using hSpos
    obtain ⟨h, hh, hhdelta, G, hG, hGold⟩ :=
      point_exists_closed_normal_full_top_extension ha y hP hR hSpos hSlt F hF htop
    have hGb : Bottom (Swidth + h) G := by
      intro q hq
      have hqold := real_mem_of_mem hSpos.le hq
      exact (hGold ⟨(q : ℂ), hqold⟩ hq).trans (hFb q hqold)
    have hnew : Swidth + h ∈ W := ⟨add_pos hSpos hh, hhdelta.le, G, Isometry.of_dist_eq hG, hGb⟩
    have hle := le_csSup hWbound hnew
    change Swidth + h ≤ Swidth at hle
    linarith
  let incl : K delta → K Swidth := fun z ↦ ⟨z.1, hSequal.symm ▸ z.2⟩
  have hinc : Isometry incl := fun _ _ ↦ rfl
  refine ⟨F ∘ incl, fun x z ↦ (hF.comp hinc).dist_eq x z, ?_⟩
  intro q hq
  exact hFb q (hSequal.symm ▸ hq)

end RepulsiveCoulomb
