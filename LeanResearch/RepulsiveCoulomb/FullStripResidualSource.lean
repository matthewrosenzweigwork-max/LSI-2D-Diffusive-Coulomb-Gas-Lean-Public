import LeanResearch.RepulsiveCoulomb.FullNormalStripSourceGeometry
import LeanResearch.RepulsiveCoulomb.PointMetricLineHalfplaneHomeomorphisms
import Mathlib.Analysis.Convex.PathConnected

/-! New source-only residual-strip construction. All source metrics below are
Complex subtype metrics, never the max metric on a product. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

def fullStripBottom {h : ℝ} (hh : 0 ≤ h) (t : ℝ) : flatFullNormalStrip h :=
  ⟨(t : ℂ), by simpa [flatFullNormalStrip] using And.intro (le_refl (0 : ℝ)) hh⟩

def fullStripTop {h : ℝ} (hh : 0 ≤ h) (t : ℝ) : flatFullNormalStrip h :=
  ⟨⟨t, h⟩, hh, le_refl h⟩

@[simp] theorem fullStripBottom_im {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    (fullStripBottom hh t).1.im = 0 := rfl

@[simp] theorem fullStripTop_im {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    (fullStripTop hh t).1.im = h := rfl

theorem fullStripBottom_isometry {h : ℝ} (hh : 0 ≤ h) : Isometry (fullStripBottom hh) := by
  apply Isometry.of_dist_eq
  intro s t
  change dist (s : ℂ) (t : ℂ) = dist s t
  rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Real.dist_eq]

theorem fullStripTop_isometry {h : ℝ} (hh : 0 ≤ h) : Isometry (fullStripTop hh) := by
  apply Isometry.of_dist_eq
  intro s t
  change dist (⟨s, h⟩ : ℂ) (⟨t, h⟩ : ℂ) = dist s t
  rw [dist_eq_norm]
  have he : (⟨s, h⟩ : ℂ) - ⟨t, h⟩ = ((s - t : ℝ) : ℂ) := by apply Complex.ext <;> simp
  rw [he, Complex.norm_real, Real.norm_eq_abs, Real.dist_eq]

theorem fullStrip_mem_top_range_iff {h : ℝ} (hh : 0 ≤ h) (z : flatFullNormalStrip h) :
    z ∈ range (fullStripTop hh) ↔ z.1.im = h := by
  constructor
  · rintro ⟨t, rfl⟩; rfl
  · intro hz
    exact ⟨z.1.re, Subtype.ext (Complex.ext rfl hz.symm)⟩

theorem fullStrip_image_mem_top_iff {Y : Type*} {h : ℝ} (hh : 0 ≤ h)
    {F : flatFullNormalStrip h → Y} (hF : Function.Injective F) (z : flatFullNormalStrip h) :
    F z ∈ range (F ∘ fullStripTop hh) ↔ z.1.im = h := by
  constructor
  · rintro ⟨t, ht⟩
    exact congrArg (fun w : flatFullNormalStrip h ↦ w.1.im) (hF ht).symm
  · intro hz
    obtain ⟨t, ht⟩ := (fullStrip_mem_top_range_iff hh z).mpr hz
    exact ⟨t, congrArg F ht⟩

theorem fullStrip_without_top_connected {Y : Type*} [TopologicalSpace Y]
    {h : ℝ} (hh : 0 < h) (F : flatFullNormalStrip h → Y)
    (hF : Continuous F) (hinj : Function.Injective F) :
    IsConnected (range F \ range (F ∘ fullStripTop hh.le)) := by
  let T : Set ℂ := {z | z.im ∈ Ico (0 : ℝ) h}
  have hTc : Convex ℝ T :=
    (convex_halfSpace_ge (.mk Complex.add_im Complex.smul_im) 0).inter
      (convex_halfSpace_lt (.mk Complex.add_im Complex.smul_im) h)
  have hT : IsConnected T := ⟨⟨0, by simp [T, hh]⟩, hTc.isPreconnected⟩
  letI : ConnectedSpace T := isConnected_iff_connectedSpace.mp hT
  let i : T → flatFullNormalStrip h := fun z ↦ ⟨z.1, z.2.1, z.2.2.le⟩
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  have him : range (F ∘ i) = range F \ range (F ∘ fullStripTop hh.le) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨mem_range_self (i z), ?_⟩
      change F (i z) ∉ range (F ∘ fullStripTop hh.le)
      rw [fullStrip_image_mem_top_iff hh.le hinj]
      exact ne_of_lt z.2.2
    · rintro ⟨⟨z, rfl⟩, hz⟩
      have hzt : z.1.im < h := lt_of_le_of_ne z.2.2
        (fun he ↦ hz ((fullStrip_image_mem_top_iff hh.le hinj z).mpr he))
      exact ⟨⟨z.1, z.2.1, hzt⟩, rfl⟩
  rw [← him]
  exact isConnected_range (hF.comp hi)

/-- Both source edges are actual ambient metric lines; in particular the top
has its own constructed global straightening and two genuine closed sides. -/
theorem pointFullStrip_top_metric_and_sides
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {h : ℝ} (hh : 0 < h) (F : flatFullNormalStrip h → P)
    (hF : ∀ z w, (pointSmoothConformalEDist a y (F z).1 (F w).1).toReal = dist z w) :
    let top : ℝ → ℂ := fun t ↦ (F (fullStripTop hh.le t)).1
    (∀ s t, (pointSmoothConformalEDist a y (top s) (top t)).toReal = dist s t) ∧
    ∃ D : PlanarLineHalfplaneHomeomorphs top,
      (F (fullStripBottom hh.le 0)).1 ∈ D.positive := by
  dsimp only
  have hi : Function.Injective F := by
    intro z w he
    have hd := hF z w
    rw [he, pointSmoothConformalEDist_self, ENNReal.toReal_zero] at hd
    exact dist_eq_zero.mp hd.symm
  have ht : ∀ s t, (pointSmoothConformalEDist a y
      (F (fullStripTop hh.le s)).1 (F (fullStripTop hh.le t)).1).toReal = dist s t := by
    intro s t
    rw [hF]
    exact (fullStripTop_isometry hh.le).dist_eq s t
  have hnot : (F (fullStripBottom hh.le 0)).1 ∉
      range (fun t ↦ (F (fullStripTop hh.le t)).1) := by
    rintro ⟨t, he⟩
    have hs := hi (Subtype.ext he)
    have him := congrArg (fun z : flatFullNormalStrip h ↦ z.1.im) hs
    exact hh.ne' him
  exact ⟨ht, exists_pointMetricLine_halfplaneHomeomorphs_positive_at ha y _ ht hnot⟩

end RepulsiveCoulomb
