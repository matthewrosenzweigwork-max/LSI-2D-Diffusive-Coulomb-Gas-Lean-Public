module

public import LeanResearch.RepulsiveCoulomb.PointGeodesicBigonExtraction

@[expose] public section

/-! The disagreement subarcs are reparameterized as actual constant-speed
minimizing geodesics on the standard interval. Their Jordan curve is obtained
from the approved general two-arc theorem, not a polygonal surrogate. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def pointGeodesicIntervalMap (s t : Icc (0 : ℝ) 1) (hst : s ≤ t) :
    Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun u =>
  ⟨s.1 + u.1 * (t.1 - s.1), by
    have hst' : s.1 ≤ t.1 := hst
    have hlow := mul_nonneg u.2.1 (sub_nonneg.mpr hst')
    have hhigh := mul_le_mul_of_nonneg_right u.2.2 (sub_nonneg.mpr hst')
    constructor <;> nlinarith [s.2.1, t.2.2]⟩

@[simp] theorem pointGeodesicIntervalMap_zero (s t : Icc (0 : ℝ) 1) (hst : s ≤ t) :
    pointGeodesicIntervalMap s t hst ⟨0, by norm_num⟩ = s := by
  apply Subtype.ext
  simp [pointGeodesicIntervalMap]

@[simp] theorem pointGeodesicIntervalMap_one (s t : Icc (0 : ℝ) 1) (hst : s ≤ t) :
    pointGeodesicIntervalMap s t hst ⟨1, by norm_num⟩ = t := by
  apply Subtype.ext
  simp [pointGeodesicIntervalMap]

theorem pointGeodesicIntervalMap_continuous (s t : Icc (0 : ℝ) 1) (hst : s ≤ t) :
    Continuous (pointGeodesicIntervalMap s t hst) :=
  (continuous_const.add (continuous_subtype_val.mul continuous_const)).subtype_mk _

theorem pointGeodesicIntervalMap_range (s t : Icc (0 : ℝ) 1) (hst : s < t) :
    range (pointGeodesicIntervalMap s t hst.le) = Icc s t := by
  have hst' : s.1 < t.1 := hst
  have hD : 0 < t.1 - s.1 := sub_pos.mpr hst'
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    change s.1 ≤ s.1 + v.1 * (t.1 - s.1) ∧ s.1 + v.1 * (t.1 - s.1) ≤ t.1
    have hlow := mul_nonneg v.2.1 hD.le
    have hhigh := mul_le_mul_of_nonneg_right v.2.2 hD.le
    constructor <;> nlinarith
  · intro hu
    have hus : s.1 ≤ u.1 := hu.1
    have hut : u.1 ≤ t.1 := hu.2
    let v : Icc (0 : ℝ) 1 := ⟨(u.1 - s.1) / (t.1 - s.1),
      div_nonneg (sub_nonneg.mpr hus) hD.le,
      (div_le_one hD).mpr (by linarith)⟩
    refine ⟨v, Subtype.ext ?_⟩
    change s.1 + (u.1 - s.1) / (t.1 - s.1) * (t.1 - s.1) = u.1
    rw [div_mul_cancel₀ _ hD.ne']
    ring

/-- Restricting and rescaling an exact geodesic preserves the exact geodesic law. -/
theorem pointConformal_geodesic_interval_reparameterization {m : ℕ}
    (a : Fin m → ℝ) (y : Fin m → ℂ) {x z : ℂ}
    (γ : Icc (0 : ℝ) 1 → ℂ)
    (hd : ∀ u v, (pointSmoothConformalEDist a y (γ u) (γ v)).toReal =
      |v.1 - u.1| * (pointSmoothConformalEDist a y x z).toReal)
    (s t : Icc (0 : ℝ) 1) (hst : s ≤ t) :
    ∀ u v, (pointSmoothConformalEDist a y
        (γ (pointGeodesicIntervalMap s t hst u))
        (γ (pointGeodesicIntervalMap s t hst v))).toReal =
      |v.1 - u.1| * (pointSmoothConformalEDist a y (γ s) (γ t)).toReal := by
  intro u v
  rw [hd, hd s t]
  have hdiff : (pointGeodesicIntervalMap s t hst v).1 -
      (pointGeodesicIntervalMap s t hst u).1 = (v.1 - u.1) * (t.1 - s.1) := by
    dsimp [pointGeodesicIntervalMap]
    ring
  rw [hdiff, abs_mul, mul_assoc]

/-- The actual two-arc image of any simple geodesic bigon is Jordan. -/
theorem pointConformal_simple_geodesic_bigon_jordan {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p q : ℂ} (hpq : p ≠ q)
    (γ₁ γ₂ : Icc (0 : ℝ) 1 → ℂ)
    (h10 : γ₁ ⟨0, by norm_num⟩ = p) (h11 : γ₁ ⟨1, by norm_num⟩ = q)
    (h20 : γ₂ ⟨0, by norm_num⟩ = p) (h21 : γ₂ ⟨1, by norm_num⟩ = q)
    (hd₁ : ∀ s t, (pointSmoothConformalEDist a y (γ₁ s) (γ₁ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal)
    (hd₂ : ∀ s t, (pointSmoothConformalEDist a y (γ₂ s) (γ₂ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal)
    (hmeet : range γ₁ ∩ range γ₂ = {p, q}) :
    Schoenflies.IsJordanCurve
      (range (Complex.orthonormalBasisOneI.repr ∘ γ₁) ∪
        range (Complex.orthonormalBasisOneI.repr ∘ γ₂)) := by
  let e := Complex.orthonormalBasisOneI.repr
  have hA := isArcBetween_of_continuous_injective_interval (e ∘ γ₁)
    (e.continuous.comp (pointConformal_geodesic_continuous ha y γ₁ hd₁))
    (e.injective.comp (pointConformal_geodesic_injective ha y hpq γ₁ hd₁))
  have hB := isArcBetween_of_continuous_injective_interval (e ∘ γ₂)
    (e.continuous.comp (pointConformal_geodesic_continuous ha y γ₂ hd₂))
    (e.injective.comp (pointConformal_geodesic_injective ha y hpq γ₂ hd₂))
  simp only [Function.comp_apply, h10, h11, h20, h21] at hA hB
  apply Schoenflies.IsJordanCurve.two_arcs_of_two_arcs hA hB
  ext w
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have he : γ₁ s = γ₂ t := e.injective (hs.trans ht.symm)
    have hmem : γ₁ s ∈ range γ₁ ∩ range γ₂ := ⟨mem_range_self s, ⟨t, he.symm⟩⟩
    rw [hmeet] at hmem
    rcases mem_insert_iff.mp hmem with hp | hq
    · have hw : w = e p := hs.symm.trans (congrArg e hp)
      simp only [hw, mem_insert_iff, mem_singleton_iff, true_or]
    · have hw : w = e q := hs.symm.trans (congrArg e (mem_singleton_iff.mp hq))
      simp only [hw, mem_insert_iff, mem_singleton_iff, or_true]
  · intro hw
    rcases mem_insert_iff.mp hw with hp | hq
    · subst w
      exact ⟨⟨⟨0, by norm_num⟩, congrArg e h10⟩,
        ⟨⟨0, by norm_num⟩, congrArg e h20⟩⟩
    · have hwq : w = e q := mem_singleton_iff.mp hq
      subst w
      exact ⟨⟨⟨1, by norm_num⟩, congrArg e h11⟩,
        ⟨⟨1, by norm_num⟩, congrArg e h21⟩⟩

/-- Every hypothetical failure of global uniqueness yields an actual Jordan
bigon made of two constant-speed minimizing segments, with distinct vertices. -/
theorem exists_pointConformal_jordan_geodesic_bigon {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {x z : ℂ} (hxz : x ≠ z)
    (γ₁ γ₂ : Icc (0 : ℝ) 1 → ℂ)
    (h10 : γ₁ ⟨0, by norm_num⟩ = x) (h11 : γ₁ ⟨1, by norm_num⟩ = z)
    (h20 : γ₂ ⟨0, by norm_num⟩ = x) (h21 : γ₂ ⟨1, by norm_num⟩ = z)
    (hd₁ : ∀ s t, (pointSmoothConformalEDist a y (γ₁ s) (γ₁ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y x z).toReal)
    (hd₂ : ∀ s t, (pointSmoothConformalEDist a y (γ₂ s) (γ₂ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y x z).toReal)
    (hne : γ₁ ≠ γ₂) :
    ∃ p q : ℂ, p ≠ q ∧ ∃ δ₁ δ₂ : Icc (0 : ℝ) 1 → ℂ,
      δ₁ ⟨0, by norm_num⟩ = p ∧ δ₁ ⟨1, by norm_num⟩ = q ∧
      δ₂ ⟨0, by norm_num⟩ = p ∧ δ₂ ⟨1, by norm_num⟩ = q ∧
      (∀ u v, (pointSmoothConformalEDist a y (δ₁ u) (δ₁ v)).toReal =
        |v.1 - u.1| * (pointSmoothConformalEDist a y p q).toReal) ∧
      (∀ u v, (pointSmoothConformalEDist a y (δ₂ u) (δ₂ v)).toReal =
        |v.1 - u.1| * (pointSmoothConformalEDist a y p q).toReal) ∧
      range δ₁ ∩ range δ₂ = {p, q} ∧
      Schoenflies.IsJordanCurve
        (range (Complex.orthonormalBasisOneI.repr ∘ δ₁) ∪
          range (Complex.orthonormalBasisOneI.repr ∘ δ₂)) := by
  obtain ⟨s, t, hst, hs, ht, hpq, _, hmeet⟩ :=
    exists_pointConformal_geodesic_simple_bigon_interval ha y hxz γ₁ γ₂
      h10 h11 h20 h21 hd₁ hd₂ hne
  let φ := pointGeodesicIntervalMap s t hst.le
  let δ₁ := γ₁ ∘ φ
  let δ₂ := γ₂ ∘ φ
  have hφ0 : φ ⟨0, by norm_num⟩ = s := pointGeodesicIntervalMap_zero s t hst.le
  have hφ1 : φ ⟨1, by norm_num⟩ = t := pointGeodesicIntervalMap_one s t hst.le
  have hδ10 : δ₁ ⟨0, by norm_num⟩ = γ₁ s := congrArg γ₁ hφ0
  have hδ11 : δ₁ ⟨1, by norm_num⟩ = γ₁ t := congrArg γ₁ hφ1
  have hδ20 : δ₂ ⟨0, by norm_num⟩ = γ₁ s := (congrArg γ₂ hφ0).trans hs.symm
  have hδ21 : δ₂ ⟨1, by norm_num⟩ = γ₁ t := (congrArg γ₂ hφ1).trans ht.symm
  have hδd₁ := pointConformal_geodesic_interval_reparameterization a y γ₁ hd₁ s t hst.le
  have hδd₂ := pointConformal_geodesic_interval_reparameterization a y γ₂ hd₂ s t hst.le
  rw [← hs, ← ht] at hδd₂
  have hδmeet : range δ₁ ∩ range δ₂ = {γ₁ s, γ₁ t} := by
    change range (γ₁ ∘ φ) ∩ range (γ₂ ∘ φ) = _
    rw [range_comp, range_comp]
    change γ₁ '' range (pointGeodesicIntervalMap s t hst.le) ∩
      γ₂ '' range (pointGeodesicIntervalMap s t hst.le) = _
    rw [pointGeodesicIntervalMap_range s t hst]
    exact hmeet
  exact ⟨γ₁ s, γ₁ t, hpq, δ₁, δ₂, hδ10, hδ11, hδ20, hδ21, hδd₁, hδd₂,
    hδmeet, pointConformal_simple_geodesic_bigon_jordan ha y hpq δ₁ δ₂
      hδ10 hδ11 hδ20 hδ21 hδd₁ hδd₂ hδmeet⟩

end RepulsiveCoulomb
