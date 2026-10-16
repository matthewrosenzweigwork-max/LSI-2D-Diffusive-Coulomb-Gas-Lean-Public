module

public import LeanResearch.RepulsiveCoulomb.NormalRectangleSource
public import LeanResearch.RepulsiveCoulomb.ShearedRectangleInteriorGeometry
public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

/-!
NEW implementation of the recovered full-line source geometry contract.
The finite normal rectangle definition is imported from a NEW pure source
module rather than the missing analytic MetricCleanRayCompactCollar. All
closed/open endpoints and all source maps are fixed by the surviving callers.
No historical source hash or historical compiler pass applies to this file.
-/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- The bottom point has literal complex value r; it is not a pair-metric point. -/
def normalRectangleBottom {R s r : ℝ} (hr : r ∈ Icc (0 : ℝ) R) (hs : 0 ≤ s) :
    flatShearedRectangle Complex.I R s :=
  ⟨(r : ℂ), r, hr, 0, ⟨le_rfl, hs⟩, by simp⟩

theorem mem_flatShearedRectangle_I_iff {R s : ℝ} {z : ℂ} :
    z ∈ flatShearedRectangle Complex.I R s ↔
      z.re ∈ Icc (0 : ℝ) R ∧ z.im ∈ Icc (0 : ℝ) s := by
  constructor
  · rintro ⟨r, hr, u, hu, rfl⟩
    simpa [flatShearedPoint] using And.intro hr hu
  · intro hz
    refine ⟨z.re, hz.1, z.im, hz.2, ?_⟩
    apply Complex.ext <;> simp [flatShearedPoint]

theorem flatShearedRectangle_I_interior_im_pos {R s : ℝ} {z : ℂ}
    (hz : z ∈ interior (flatShearedRectangle Complex.I R s)) : 0 < z.im := by
  rw [flatShearedRectangle_interior (by simp : Complex.I.im ≠ 0)] at hz
  obtain ⟨⟨r, u⟩, ⟨hr, hu⟩, rfl⟩ := hz
  simpa [flatShearedPoint] using hu.1

theorem flatNormalRectangle_image (a b s : ℝ) :
    flatNormalRectangle a b s =
      (fun q : ℝ × ℝ ↦ flatShearedPoint Complex.I q.1 q.2) ''
        (Icc a b ×ˢ Icc (0 : ℝ) s) := by
  ext z
  constructor
  · intro hz
    refine ⟨(z.re, z.im), hz, ?_⟩
    apply Complex.ext <;> simp [flatShearedPoint]
  · rintro ⟨⟨r, u⟩, ⟨hr, hu⟩, rfl⟩
    simpa [flatNormalRectangle, flatShearedPoint] using And.intro hr hu

theorem flatNormalRectangle_convex (a b s : ℝ) : Convex ℝ (flatNormalRectangle a b s) := by
  change Convex ℝ ((Complex.reLm ⁻¹' Icc a b) ∩ (Complex.imLm ⁻¹' Icc (0 : ℝ) s))
  exact ((convex_Icc a b).linear_preimage Complex.reLm).inter
    ((convex_Icc (0 : ℝ) s).linear_preimage Complex.imLm)

theorem flatNormalRectangle_compact (a b s : ℝ) : IsCompact (flatNormalRectangle a b s) := by
  rw [flatNormalRectangle_image]
  apply (isCompact_Icc.prod isCompact_Icc).image
  unfold flatShearedPoint
  fun_prop

theorem flatNormalRectangle_interior (a b s : ℝ) :
    interior (flatNormalRectangle a b s) =
      {z : ℂ | z.re ∈ Ioo a b ∧ z.im ∈ Ioo (0 : ℝ) s} := by
  let e : ℂ ≃ₜ ℝ × ℝ := Complex.equivRealProdCLM.toHomeomorph
  change interior (e ⁻¹' (Icc a b ×ˢ Icc (0 : ℝ) s)) =
    e ⁻¹' (Ioo a b ×ˢ Ioo (0 : ℝ) s)
  rw [← e.preimage_interior, interior_prod_eq, interior_Icc, interior_Icc]

theorem flatNormalRectangle_interior_nonempty {a b s : ℝ} (hab : a < b) (hs : 0 < s) :
    (interior (flatNormalRectangle a b s)).Nonempty := by
  refine ⟨flatShearedPoint Complex.I ((a + b) / 2) (s / 2), ?_⟩
  rw [flatNormalRectangle_interior]
  have hr : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hu : s / 2 ∈ Ioo (0 : ℝ) s := ⟨half_pos hs, half_lt_self hs⟩
  simpa [flatShearedPoint] using And.intro hr hu

theorem flatNormalRectangle_interior_im_pos {a b s : ℝ} {z : ℂ}
    (hz : z ∈ interior (flatNormalRectangle a b s)) : 0 < z.im := by
  rw [flatNormalRectangle_interior] at hz
  exact hz.2.1

/-- Translate a literal finite normal rectangle by its left endpoint. -/
def flatNormalRectangleToSheared {a b s : ℝ} :
    flatNormalRectangle a b s → flatShearedRectangle Complex.I (b - a) s := fun z ↦
  ⟨z.1 - (a : ℂ), mem_flatShearedRectangle_I_iff.mpr (by
    change z.1.re - a ∈ Icc (0 : ℝ) (b - a) ∧ z.1.im - 0 ∈ Icc (0 : ℝ) s
    exact ⟨⟨sub_nonneg.mpr z.2.1.1, sub_le_sub_right z.2.1.2 a⟩,
      by simpa only [sub_zero] using z.2.2⟩)⟩

theorem flatNormalRectangleToSheared_isometry {a b s : ℝ} :
    Isometry (@flatNormalRectangleToSheared a b s) := by
  apply Isometry.of_dist_eq
  intro x z
  exact dist_sub_right x.1 z.1 (a : ℂ)

/-- The full source strip is closed at height zero and at height s. -/
def flatFullNormalStrip (s : ℝ) : Set ℂ := {z | z.im ∈ Icc (0 : ℝ) s}

theorem flatFullNormalStrip_isClosed (s : ℝ) : IsClosed (flatFullNormalStrip s) :=
  isClosed_Icc.preimage Complex.continuous_im

/-- Symmetric finite closed rectangles exhaust both real directions. -/
theorem flatFullNormalStrip_eq_iUnion (s : ℝ) :
    flatFullNormalStrip s = ⋃ n : ℕ, flatNormalRectangle (-(n + 1)) (n + 1) s := by
  ext z
  constructor
  · intro hz
    obtain ⟨n, hn⟩ := exists_nat_ge |z.re|
    apply mem_iUnion.mpr
    refine ⟨n, ⟨?_, hz⟩⟩
    exact ⟨by linarith [neg_abs_le z.re], by linarith [le_abs_self z.re]⟩
  · intro hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp hz
    exact hn.2

/-- Completeness comes from the closed Euclidean source. No completeness
assumption on the target is needed for closedness or properness. -/
theorem flatFullNormalStrip_isometry_closed_proper {Y : Type*} [MetricSpace Y]
    {s : ℝ} {f : flatFullNormalStrip s → Y} (hf : Isometry f) :
    IsClosedEmbedding f ∧ IsProperMap f := by
  letI : CompleteSpace (flatFullNormalStrip s) :=
    (flatFullNormalStrip_isClosed s).isComplete.completeSpace_coe
  exact ⟨hf.isClosedEmbedding, hf.isClosedEmbedding.isProperMap⟩

end RepulsiveCoulomb
