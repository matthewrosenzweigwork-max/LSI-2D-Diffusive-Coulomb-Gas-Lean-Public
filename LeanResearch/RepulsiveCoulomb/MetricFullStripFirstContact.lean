import LeanResearch.RepulsiveCoulomb.MetricFullStripLocalFilling
import LeanResearch.RepulsiveCoulomb.ShearedRectangleWidthSupremum
import Mathlib.Topology.Connected.Clopen

/-! Source-only, uncompiled. A contained minimizing segment of length h
cannot leave a closed strip below its top: the image is locally open there.
This proves top contact before identifying the normal germ. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

def fullStripPoint {h : ℝ} (r : ℝ) (u : Icc (0 : ℝ) h) : flatFullNormalStrip h :=
  ⟨flatShearedPoint Complex.I r u.1, by
    change 0 ≤ (flatShearedPoint Complex.I r u.1).im ∧
      (flatShearedPoint Complex.I r u.1).im ≤ h
    have him : (flatShearedPoint Complex.I r u.1).im = u.1 := by
      simp [flatShearedPoint]
    rw [him]
    exact u.2⟩

theorem fullStripPoint_dist_bottom {h : ℝ} (hh : 0 ≤ h)
    (r : ℝ) (z : flatFullNormalStrip h) :
    z.1.im ≤ dist z (fullStripPoint r ⟨0, le_rfl, hh⟩) := by
  change z.1.im ≤ dist z.1 (flatShearedPoint Complex.I r 0)
  rw [flatShearedPoint_zero, dist_eq_norm]
  have hb := Complex.abs_im_le_norm (z.1 - (r : ℂ))
  simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero,
    abs_of_nonneg z.2.1] using hb

theorem metricFullStrip_nearest_endpoint_on_top
    {Y : Type*} [MetricSpace Y] (line : ℝ → Y)
    {h : ℝ} (hh : 0 < h) (f : flatFullNormalStrip h → Y) (hf : Isometry f)
    (hb : ∀ r : ℝ, ∀ hr : (r : ℂ) ∈ flatFullNormalStrip h,
      f ⟨(r : ℂ), hr⟩ = line r)
    (hfill : ∀ z, z.1.im < h → range f ∈ 𝓝 (f z))
    (r : ℝ) (gamma : unitInterval → Y) (hc : Continuous gamma)
    (h0 : gamma 0 = line r)
    (hd : ∀ s t, dist (gamma s) (gamma t) = |t.1 - s.1| * h)
    (hnearest : ∀ q : ℝ, h ≤ dist (gamma 1) (line q)) :
    f (fullStripPoint r ⟨h, hh.le, le_rfl⟩) = gamma 1 := by
  let b := fullStripPoint (h := h) r ⟨0, le_rfl, hh.le⟩
  have hbval : b.1 = (r : ℂ) := by simp [b, fullStripPoint, flatShearedPoint]
  have hb0 : f b = line r := by
    have hr : (r : ℂ) ∈ flatFullNormalStrip h := by
      simpa [flatFullNormalStrip] using And.intro (le_refl (0 : ℝ)) hh.le
    simpa [b, fullStripPoint, flatShearedPoint] using hb r hr
  have hrad (t : unitInterval) : dist (gamma t) (line r) = t.1 * h := by
    have he := hd t 0
    simpa only [h0, Set.Icc.coe_zero, zero_sub, abs_neg, abs_of_nonneg t.2.1] using he
  have hclosed : IsClosed (range f) := (flatFullNormalStrip_isometry_closed_proper hf).1.isClosed_range
  have hcontact : gamma 1 ∈ range f := by
    by_contra hnot
    let T := gamma ⁻¹' range f
    have hTc : IsClosed T := hclosed.preimage hc
    have hTo : IsOpen T := by
      apply isOpen_iff_mem_nhds.mpr
      intro t ht
      obtain ⟨z, hz⟩ := ht
      have ht1 : t.1 < 1 := by
        by_contra hn
        have he : t.1 = 1 := le_antisymm t.2.2 (le_of_not_gt hn)
        have het : t = 1 := Subtype.ext he
        exact hnot (het ▸ (show gamma t ∈ range f from ⟨z, hz⟩))
      have hzheight : z.1.im < h := by
        have hsource := fullStripPoint_dist_bottom hh.le r z
        have hdist : dist z b = t.1 * h := by
          rw [← hf.dist_eq, hb0, hz, hrad]
        have htlt : t.1 * h < h := by nlinarith
        exact (hsource.trans hdist.le).trans_lt htlt
      have hn := hc.continuousAt.preimage_mem_nhds (show range f ∈ 𝓝 (gamma t) by
        rw [← hz]
        exact hfill z hzheight)
      exact hn
    have hTne : T.Nonempty := ⟨0, by
      change gamma 0 ∈ range f
      rw [h0]
      exact ⟨b, hb0⟩⟩
    have hTu : T = univ := IsClopen.eq_univ ⟨hTc, hTo⟩ hTne
    exact hnot (show 1 ∈ T by rw [hTu]; trivial)
  obtain ⟨z, hz⟩ := hcontact
  have hbz : (z.1.re : ℂ) ∈ flatFullNormalStrip h := by
    simpa [flatFullNormalStrip] using And.intro (le_refl (0 : ℝ)) hh.le
  have hdvertical : dist z (⟨(z.1.re : ℂ), hbz⟩ : flatFullNormalStrip h) = z.1.im := by
    change dist z.1 (z.1.re : ℂ) = z.1.im
    have he : z.1 = flatShearedPoint Complex.I z.1.re z.1.im := by
      apply Complex.ext <;> simp [flatShearedPoint]
    calc
      dist z.1 (z.1.re : ℂ) =
          dist (flatShearedPoint Complex.I z.1.re z.1.im) (z.1.re : ℂ) :=
        congrArg (fun v : ℂ => dist v (z.1.re : ℂ)) he
      _ = z.1.im := by
        simpa only [flatShearedPoint_zero] using
          (flatShearedPoint_dist_bottom (v := Complex.I) (by simp) z.1.re z.2.1)
  have hzim : z.1.im = h := by
    apply le_antisymm z.2.2
    have he := hnearest z.1.re
    rw [← hz, ← hb z.1.re hbz, hf.dist_eq, hdvertical] at he
    exact he
  have hdz : dist z.1 (r : ℂ) = h := by
    calc
      dist z.1 (r : ℂ) = dist z b := by change dist z.1 (r : ℂ) = dist z.1 b.1; rw [hbval]
      _ = h := by rw [← hf.dist_eq, hb0, hz, hrad]; simp
  let top := fullStripPoint r ⟨h, hh.le, le_rfl⟩
  have hdtop : dist top.1 (r : ℂ) = h := by
    change dist (flatShearedPoint Complex.I r h) (r : ℂ) = h
    rw [← flatShearedPoint_zero Complex.I r]
    exact flatShearedPoint_dist_bottom (by simp) r hh.le
  have hsq := complex_normSq_sub_eq_of_dist_eq (hdz.trans hdtop.symm)
  have hzre : z.1.re = r := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, sub_zero, top, fullStripPoint, flatShearedPoint,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, add_zero,
      zero_add, sub_self, hzim] at hsq
    nlinarith [sq_nonneg (z.1.re - r)]
  have he : z = top := by
    apply Subtype.ext
    apply Complex.ext
    · simpa [top, fullStripPoint, flatShearedPoint] using hzre
    · simpa [top, fullStripPoint, flatShearedPoint] using hzim
  exact (congrArg f he).symm.trans hz

end RepulsiveCoulomb
