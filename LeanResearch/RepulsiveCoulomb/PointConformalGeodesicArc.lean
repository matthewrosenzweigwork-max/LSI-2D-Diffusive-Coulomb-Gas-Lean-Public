module

public import LeanResearch.RepulsiveCoulomb.PointConformalGeodesic
public import LeanResearch.RepulsiveCoulomb.PointConformalJordan
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

/-! Geodesics in the actual point metric give simple topological arcs. Two such
arcs meeting only at their endpoints bound a Jordan region, without any polygonality
assumption. This does not assert that arbitrary geodesics intersect only at endpoints. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem isArcBetween_of_continuous_injective_interval
    (γ : Icc (0 : ℝ) 1 → Schoenflies.Plane) (hc : Continuous γ)
    (hi : Function.Injective γ) :
    Schoenflies.IsArcBetween (range γ) (γ ⟨0, by norm_num⟩) (γ ⟨1, by norm_num⟩) := by
  let f := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ
  have hf : Continuous f := continuous_IccExtend_iff.mpr hc
  refine ⟨f, hf.continuousOn, ?_, ?_, ?_, ?_⟩
  · intro s hs t ht he
    have he' : γ ⟨s, hs⟩ = γ ⟨t, ht⟩ := by
      simpa only [f, IccExtend_of_mem _ _ hs, IccExtend_of_mem _ _ ht] using he
    exact congrArg Subtype.val (hi he')
  · ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact mem_range_self _
    · rintro ⟨t, rfl⟩
      exact ⟨t.1, t.2, IccExtend_of_mem _ _ t.2⟩
  · exact IccExtend_of_mem _ _ (by norm_num)
  · exact IccExtend_of_mem _ _ (by norm_num)

theorem pointConformal_geodesic_injective {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {x z : ℂ} (hxz : x ≠ z)
    (γ : Icc (0 : ℝ) 1 → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y x z).toReal) :
    Function.Injective γ := by
  have hp : 0 < (pointSmoothConformalEDist a y x z).toReal := by
    apply ENNReal.toReal_pos
    · exact (pointSmoothConformalEDist_eq_zero_iff ha y x z).not.mpr hxz
    · exact (pointSmoothConformalEDist_lt_top ha y x z).ne
  intro s t he
  have h := hd s t
  rw [he, pointSmoothConformalEDist_self, ENNReal.toReal_zero] at h
  have hz : |t.1 - s.1| = 0 := (mul_eq_zero.mp h.symm).resolve_right hp.ne'
  exact Subtype.ext (sub_eq_zero.mp (abs_eq_zero.mp hz)).symm

theorem exists_pointConformal_geodesic_arc {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {x z : ℂ} (hxz : x ≠ z) :
    ∃ γ : Icc (0 : ℝ) 1 → ℂ,
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = z ∧ Continuous γ ∧
      (∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
        |t.1 - s.1| * (pointSmoothConformalEDist a y x z).toReal) ∧
      Schoenflies.IsArcBetween (range (Complex.orthonormalBasisOneI.repr ∘ γ))
        (Complex.orthonormalBasisOneI.repr x) (Complex.orthonormalBasisOneI.repr z) := by
  obtain ⟨γ, h0, h1, hc, hd⟩ := exists_pointConformal_geodesic ha y x z
  have hi := pointConformal_geodesic_injective ha y hxz γ hd
  have hA := isArcBetween_of_continuous_injective_interval
    (Complex.orthonormalBasisOneI.repr ∘ γ)
    (Complex.orthonormalBasisOneI.repr.continuous.comp hc)
    (Complex.orthonormalBasisOneI.repr.injective.comp hi)
  simp only [Function.comp_apply, h0, h1] at hA
  exact ⟨γ, h0, h1, hc, hd, hA⟩

/-- The general Jordan theorem applies to two arcs, not merely polygonal arcs. -/
theorem two_arcs_separate_plane {A B : Set Schoenflies.Plane} {p q : Schoenflies.Plane}
    (hA : Schoenflies.IsArcBetween A p q) (hB : Schoenflies.IsArcBetween B p q)
    (hmeet : A ∩ B = {p, q}) : Schoenflies.IsSeparating (A ∪ B) :=
  Schoenflies.jordan_curve_theorem
    (Schoenflies.IsJordanCurve.two_arcs_of_two_arcs hA hB hmeet)

end RepulsiveCoulomb
