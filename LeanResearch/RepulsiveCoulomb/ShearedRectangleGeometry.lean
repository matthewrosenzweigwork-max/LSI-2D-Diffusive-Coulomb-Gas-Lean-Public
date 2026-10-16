module

public import LeanResearch.RepulsiveCoulomb.PointConvexLocalFlatEmbedding
public import LeanResearch.RepulsiveCoulomb.PointMarkedRayClearance
public import LeanResearch.RepulsiveCoulomb.EuclideanSectorContraction
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

/-! Literal Euclidean sheared rectangles and the manuscript's exact transverse
distance. The source metric is the Euclidean metric on C, never the max/product
metric on the coordinate pair (r,u). -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def flatShearedPoint (v : ℂ) (r u : ℝ) : ℂ := (r : ℂ) + (u : ℂ) * v

def flatShearedRectangle (v : ℂ) (R s : ℝ) : Set ℂ :=
  {z | ∃ r ∈ Icc (0 : ℝ) R, ∃ u ∈ Icc (0 : ℝ) s, z = flatShearedPoint v r u}

def flatShearedStrip (v : ℂ) (s : ℝ) : Set ℂ :=
  {z | ∃ r, 0 ≤ r ∧ ∃ u ∈ Icc (0 : ℝ) s, z = flatShearedPoint v r u}

@[simp] theorem flatShearedPoint_zero (v : ℂ) (r : ℝ) :
    flatShearedPoint v r 0 = (r : ℂ) := by simp [flatShearedPoint]

/-- The sheared transverse parameter is arclength, not perpendicular distance. -/
theorem flatShearedPoint_dist_bottom {v : ℂ} (hv : ‖v‖ = 1)
    (r : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    dist (flatShearedPoint v r u) (flatShearedPoint v r 0) = u := by
  rw [dist_eq_norm, flatShearedPoint_zero]
  simp only [flatShearedPoint, add_sub_cancel_left, norm_mul, hv, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]

theorem flatShearedRectangle_convex (v : ℂ) (R s : ℝ) :
    Convex ℝ (flatShearedRectangle v R s) := by
  intro x hx z hz a b ha hb hab
  obtain ⟨r, hr, u, hu, rfl⟩ := hx
  obtain ⟨t, ht, w, hw, rfl⟩ := hz
  have hR : a * r + b * t ≤ R := by
    calc
      a * r + b * t ≤ a * R + b * R :=
        add_le_add (mul_le_mul_of_nonneg_left hr.2 ha) (mul_le_mul_of_nonneg_left ht.2 hb)
      _ = R := by rw [← add_mul, hab, one_mul]
  have hs : a * u + b * w ≤ s := by
    calc
      a * u + b * w ≤ a * s + b * s :=
        add_le_add (mul_le_mul_of_nonneg_left hu.2 ha) (mul_le_mul_of_nonneg_left hw.2 hb)
      _ = s := by rw [← add_mul, hab, one_mul]
  refine ⟨a * r + b * t, ⟨add_nonneg (mul_nonneg ha hr.1) (mul_nonneg hb ht.1), hR⟩,
    a * u + b * w, ⟨add_nonneg (mul_nonneg ha hu.1) (mul_nonneg hb hw.1), hs⟩, ?_⟩
  simp only [flatShearedPoint, Complex.real_smul, Complex.ofReal_add, Complex.ofReal_mul]
  ring

theorem flatShearedRectangle_image (v : ℂ) (R s : ℝ) :
    flatShearedRectangle v R s =
      (fun q : ℝ × ℝ ↦ flatShearedPoint v q.1 q.2) '' (Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) s) := by
  ext z
  constructor
  · rintro ⟨r, hr, u, hu, rfl⟩
    exact ⟨(r, u), ⟨hr, hu⟩, rfl⟩
  · rintro ⟨⟨r, u⟩, ⟨hr, hu⟩, rfl⟩
    exact ⟨r, hr, u, hu, rfl⟩

theorem flatShearedRectangle_compact (v : ℂ) (R s : ℝ) :
    IsCompact (flatShearedRectangle v R s) := by
  rw [flatShearedRectangle_image]
  apply (isCompact_Icc.prod isCompact_Icc).image
  unfold flatShearedPoint
  fun_prop

theorem flatShearedRectangle_mono {v : ℂ} {R T s h : ℝ} (hRT : R ≤ T) (hsh : s ≤ h) :
    flatShearedRectangle v R s ⊆ flatShearedRectangle v T h := by
  rintro z ⟨r, hr, u, hu, rfl⟩
  exact ⟨r, ⟨hr.1, hr.2.trans hRT⟩, u, ⟨hu.1, hu.2.trans hsh⟩, rfl⟩

/-- Integer finite rectangles exhaust the actual unbounded sheared strip. -/
theorem flatShearedStrip_eq_iUnion (v : ℂ) (s : ℝ) :
    flatShearedStrip v s = ⋃ n : ℕ, flatShearedRectangle v n s := by
  ext z
  constructor
  · rintro ⟨r, hr, u, hu, rfl⟩
    obtain ⟨n, hn⟩ := exists_nat_ge r
    exact mem_iUnion.mpr ⟨n, r, ⟨hr, hn⟩, u, hu, rfl⟩
  · intro hz
    obtain ⟨n, r, hr, u, hu, rfl⟩ := mem_iUnion.mp hz
    exact ⟨r, hr.1, u, hu, rfl⟩

/-- A constructed local map on a finite rectangle is globally isometric by
actual local-to-global geometry. Hence a mark cannot arise in its completed
image while the one global transverse cutoff is respected. -/
theorem pointShearedRectangle_unmarked {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {v : ℂ} (hv : ‖v‖ = 1)
    {R s δ : ℝ} (hs : 0 ≤ s) (hsδ : s ≤ δ)
    (ρ : NNReal → ℂ) {S : Set ℂ}
    (hclear : ∀ z ∈ S \ {ρ 0}, ∀ r : NNReal,
      δ < (pointSmoothConformalEDist a y z (ρ r)).toReal)
    (f : flatShearedRectangle v R s → ℂ)
    (hf : PointLocallyDistancePreserving a y f)
    (hbottom : ∀ r (hr : r ∈ Icc (0 : ℝ) R),
      f ⟨flatShearedPoint v r 0, ⟨r, hr, 0, ⟨le_rfl, hs⟩, rfl⟩⟩ = ρ ⟨r, hr.1⟩) :
    ∀ z, f z ∉ S \ {ρ 0} := by
  intro z
  obtain ⟨r, hr, u, hu, hzu⟩ := z.2
  let b : flatShearedRectangle v R s :=
    ⟨flatShearedPoint v r 0, ⟨r, hr, 0, ⟨le_rfl, hs⟩, rfl⟩⟩
  have hd := pointConvexFlat_dist ha y (flatShearedRectangle_convex v R s) hf z b
  have hsource : dist z b = u := by
    change dist z.1 (flatShearedPoint v r 0) = u
    rw [hzu]
    exact flatShearedPoint_dist_bottom hv r hu.1
  rw [hsource, hbottom r hr] at hd
  exact pointMetricRay_uniform_tube_unmarked ha y hclear (hd.le.trans (hu.2.trans hsδ))

end RepulsiveCoulomb
