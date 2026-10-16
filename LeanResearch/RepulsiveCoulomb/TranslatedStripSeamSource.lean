module

public import LeanResearch.RepulsiveCoulomb.TranslatedStripSourceGeometry
public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Literal source geometry for two successive
translated strips. All metrics below are Euclidean metrics on complex numbers.
No product metric, ambient extension, or seam-chart certificate is used. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Keep the original complex source point in the wider strip. -/
def translatedStripLowerInclusion {v : ℂ} {b h : ℝ} (hh : 0 ≤ h)
    (x : flatShearedStrip v b) : flatShearedStrip v (b+h) := by
  refine ⟨x.1, ?_⟩
  obtain ⟨r,hr,u,hu,hx⟩ := x.2
  exact ⟨r,hr,u,⟨hu.1,by linarith [hu.2]⟩,hx⟩

/-- Translate the second source by the old transverse width. -/
def translatedStripUpperInclusion {v : ℂ} {b h : ℝ} (hb : 0 ≤ b)
    (z : flatShearedStrip v h) : flatShearedStrip v (b+h) := by
  refine ⟨z.1+(b:ℂ)*v, ?_⟩
  obtain ⟨r,hr,u,hu,hz⟩ := z.2
  refine ⟨r,hr,b+u,⟨add_nonneg hb hu.1,by linarith [hu.2]⟩,?_⟩
  rw [hz]
  simp only [flatShearedPoint,Complex.ofReal_add]
  ring

@[simp] theorem translatedStripLowerInclusion_val {v : ℂ} {b h : ℝ}
    (hh : 0 ≤ h) (x : flatShearedStrip v b) :
    (translatedStripLowerInclusion hh x).1=x.1 := rfl

@[simp] theorem translatedStripUpperInclusion_val {v : ℂ} {b h : ℝ}
    (hb : 0 ≤ b) (z : flatShearedStrip v h) :
    (translatedStripUpperInclusion hb z).1=z.1+(b:ℂ)*v := rfl

theorem translatedStripLowerInclusion_injective {v : ℂ} {b h : ℝ} (hh : 0 ≤ h) :
    Function.Injective (@translatedStripLowerInclusion v b h hh) := by
  intro x z he
  exact Subtype.ext (congrArg (fun q : flatShearedStrip v (b+h) ↦ q.1) he)

theorem translatedStripUpperInclusion_injective {v : ℂ} {b h : ℝ} (hb : 0 ≤ b) :
    Function.Injective (@translatedStripUpperInclusion v b h hb) := by
  intro x z he
  exact Subtype.ext (add_right_cancel (congrArg Subtype.val he))

theorem translatedStripLowerInclusion_isometry {v : ℂ} {b h : ℝ} (hh : 0 ≤ h) :
    Isometry (@translatedStripLowerInclusion v b h hh) := by
  apply Isometry.of_dist_eq
  intro x z
  rfl

theorem translatedStripUpperInclusion_isometry {v : ℂ} {b h : ℝ} (hb : 0 ≤ b) :
    Isometry (@translatedStripUpperInclusion v b h hb) := by
  apply Isometry.of_dist_eq
  intro x z
  exact dist_add_right x.1 z.1 ((b:ℂ)*v)

theorem translatedStrip_successive_cover {v : ℂ} {b h : ℝ}
    (hb : 0 ≤ b) (hh : 0 ≤ h) (q : flatShearedStrip v (b+h)) :
    (∃ x : flatShearedStrip v b, translatedStripLowerInclusion hh x=q) ∨
    (∃ z : flatShearedStrip v h, translatedStripUpperInclusion hb z=q) := by
  obtain ⟨r,hr,u,hu,hq⟩ := q.2
  by_cases hub : u≤b
  · exact Or.inl ⟨⟨q.1,r,hr,u,⟨hu.1,hub⟩,hq⟩,Subtype.ext rfl⟩
  · right
    have hbu : b≤u := (lt_of_not_ge hub).le
    let z : flatShearedStrip v h :=
      ⟨flatShearedPoint v r (u-b),r,hr,u-b,⟨sub_nonneg.mpr hbu,by linarith [hu.2]⟩,rfl⟩
    refine ⟨z,Subtype.ext ?_⟩
    change flatShearedPoint v r (u-b)+(b:ℂ)*v=q.1
    rw [hq]
    simp only [flatShearedPoint,Complex.ofReal_sub]
    ring

/-- The only overlap is the old top, identified with the new bottom. -/
theorem translatedStrip_successive_overlap {v : ℂ} (hvi : v.im≠0)
    {b h : ℝ} (hb : 0 ≤ b) (hh : 0 ≤ h)
    (x : flatShearedStrip v b) (z : flatShearedStrip v h)
    (he : translatedStripLowerInclusion hh x=translatedStripUpperInclusion hb z) :
    ∃ r : NNReal, x=translatedStripTop hb r ∧ z=translatedStripBottom hh r := by
  obtain ⟨r,hr,u,hu,hx⟩ := x.2
  obtain ⟨s,hs,w,hw,hz⟩ := z.2
  have he' : flatShearedPoint v r u=flatShearedPoint v s (b+w) := by
    have he' := congrArg Subtype.val he
    change x.1=z.1+(b:ℂ)*v at he'
    rw [hx,hz] at he'
    convert he' using 1 <;> simp only [flatShearedPoint,Complex.ofReal_add] <;> ring
  obtain ⟨hrs,huw⟩ := flatShearedPoint_coordinates_eq hvi he'
  have hw0 : w=0 := by linarith [hu.2,hw.1]
  have hub : u=b := by linarith
  refine ⟨⟨r,hr⟩,Subtype.ext ?_,Subtype.ext ?_⟩
  · change x.1 = flatShearedPoint v r b
    simpa only [hub] using hx
  · change z.1=flatShearedPoint v r 0
    simpa only [← hrs,hw0] using hz

/-- Translation identifies the distance from the old top with distance from
its new-bottom coordinate. -/
theorem translatedStrip_seam_distance {v : ℂ} {b h : ℝ}
    (hb : 0 ≤ b) (hh : 0 ≤ h) (r : NNReal) (z : flatShearedStrip v h) :
    dist (translatedStripTop (v:=v) hb r).1
      (translatedStripUpperInclusion hb z).1 =
      dist (translatedStripBottom (v:=v) hh r) z := by
  change dist (flatShearedPoint v r b) (z.1+(b:ℂ)*v)=
    dist (flatShearedPoint v r 0) z.1
  simpa only [flatShearedPoint,Complex.ofReal_zero,zero_mul,add_zero] using
    dist_add_right (r:ℂ) z.1 ((b:ℂ)*v)

/-- A literal straight source segment crosses the seam at nonnegative r.
The equality is an output of convex interpolation, including the zero-length
transverse interval when both endpoints are already on the seam. -/
theorem translatedStrip_exists_source_seam_split {v : ℂ} {b h : ℝ}
    (hb : 0 ≤ b) (hh : 0 ≤ h)
    (x : flatShearedStrip v b) (z : flatShearedStrip v h) :
    ∃ r : NNReal,
      dist x (translatedStripTop hb r)+dist (translatedStripBottom hh r) z =
        dist (translatedStripLowerInclusion hh x) (translatedStripUpperInclusion hb z) := by
  obtain ⟨r,hr,u,hu,hx⟩ := x.2
  obtain ⟨s,hs,w,hw,hz⟩ := z.2
  have hd0 : 0≤b+w-u := by linarith [hu.2,hw.1]
  by_cases hd : b+w-u=0
  · have hub : u=b := by linarith [hu.2,hw.1]
    have hxt : x=translatedStripTop hb ⟨r,hr⟩ := Subtype.ext (by
      change x.1 = flatShearedPoint v r b
      simpa only [hub] using hx)
    refine ⟨⟨r,hr⟩,?_⟩
    rw [hxt,dist_self,zero_add]
    exact (translatedStrip_seam_distance hb hh ⟨r,hr⟩ z).symm
  · have hdpos : 0<b+w-u := lt_of_le_of_ne hd0 (Ne.symm hd)
    let k : ℝ := (b-u)/(b+w-u)
    have hk0 : 0≤k := div_nonneg (sub_nonneg.mpr hu.2) hd0
    have hk1 : k≤1 := (div_le_one hdpos).mpr (by linarith [hw.1])
    have hkeq : k*(b+w-u)=b-u := by exact div_mul_cancel₀ _ hd
    let R : ℝ := (1-k)*r+k*s
    have hR : 0≤R := add_nonneg (mul_nonneg (sub_nonneg.mpr hk1) hr) (mul_nonneg hk0 hs)
    have htrans : (1-k)*u+k*(b+w)=b := by nlinarith [hkeq]
    have hsource : flatShearedPoint v R b ∈
        segment ℝ x.1 (translatedStripUpperInclusion hb z).1 := by
      refine ⟨1-k,k,sub_nonneg.mpr hk1,hk0,by ring,?_⟩
      change (1-k) • x.1+k • (z.1+(b:ℂ)*v)=flatShearedPoint v R b
      rw [hx,hz]
      have hc : (((1-k)*u+k*(b+w):ℝ):ℂ)=(b:ℂ) := congrArg Complex.ofReal htrans
      simp only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one] at hc
      dsimp [flatShearedPoint,R]
      simp only [Complex.real_smul,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one]
      linear_combination v * hc
    refine ⟨⟨R,hR⟩,?_⟩
    have he := dist_add_dist_of_mem_segment hsource
    change dist x.1 (translatedStripTop hb ⟨R,hR⟩).1 +
      dist (translatedStripTop hb ⟨R,hR⟩).1 (translatedStripUpperInclusion hb z).1 =
      dist x.1 (translatedStripUpperInclusion hb z).1 at he
    rw [translatedStrip_seam_distance hb hh ⟨R,hR⟩ z] at he
    exact he

end RepulsiveCoulomb
