import LeanResearch.RepulsiveCoulomb.JordanArcArgumentHomotopy

/-! Exact argument bookkeeping across one actual endpoint-fixed corner
replacement. The angle lifts on the homotopy's two end arcs are constructed;
the two physical half-arcs may have independent additive angle constants. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def cornerFirstHalf (t : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨t / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

def cornerSecondHalf (t : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨(t + 1) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

theorem cornerFirstHalf_continuous : Continuous cornerFirstHalf :=
  (continuous_subtype_val.div_const 2).subtype_mk _

theorem cornerSecondHalf_continuous : Continuous cornerSecondHalf :=
  ((continuous_subtype_val.add_const 1).div_const 2).subtype_mk _

/-- The sum of the two actual half-arc increments is the actual whole-arc
increment. This uses covering uniqueness, with no endpoint angle alignment
assumption. -/
theorem two_half_argument_increment
    (θL θR Θ : Icc (0 : ℝ) 1 → ℝ)
    (hθL : Continuous θL) (hθR : Continuous θR) (hΘ : Continuous Θ)
    (hL : ∀ t, Circle.exp (θL t) = Circle.exp (Θ (cornerFirstHalf t)))
    (hR : ∀ t, Circle.exp (θR t) = Circle.exp (Θ (cornerSecondHalf t))) :
    (θL 1 - θL 0) + (θR 1 - θR 0) = Θ 1 - Θ 0 := by
  have hleft := euclidean_angle_lift_increment_eq hθL
    (hΘ.comp cornerFirstHalf_continuous) hL (0 : Icc (0 : ℝ) 1) 1
  have hright := euclidean_angle_lift_increment_eq hθR
    (hΘ.comp cornerSecondHalf_continuous) hR (0 : Icc (0 : ℝ) 1) 1
  have h0 : cornerFirstHalf 0 = 0 := by apply Subtype.ext; norm_num [cornerFirstHalf]
  have h1 : cornerSecondHalf 1 = 1 := by apply Subtype.ext; norm_num [cornerSecondHalf]
  have hm : cornerFirstHalf 1 = cornerSecondHalf 0 := by
    apply Subtype.ext
    norm_num [cornerFirstHalf, cornerSecondHalf]
  simp only [Function.comp_apply] at hleft hright
  rw [h0] at hleft
  rw [h1, ← hm] at hright
  linarith

/-- The endpoint-fixed actual avoiding homotopy forces equality of the sums
of the two actual incident point-argument increments. A single lift on the
old or new corner is not an additional input: both are constructed here. -/
theorem corner_homotopy_preserves_incident_point_increments
    (F : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → ℂ) (hF : Continuous F)
    (hstart : ∀ s, F (s, 0) = F (0, 0))
    (hfinish : ∀ s, F (s, 1) = F (0, 1))
    (w : ℂ) (havoid : ∀ q, F q ≠ w)
    (θL θR ψL ψR : Icc (0 : ℝ) 1 → ℝ)
    (hθL : Continuous θL) (hθR : Continuous θR)
    (hψL : Continuous ψL) (hψR : Continuous ψR)
    (hθLl : ∀ t, Complex.exp ((θL t : ℂ) * Complex.I) =
      (F (0, cornerFirstHalf t) - w) / (‖F (0, cornerFirstHalf t) - w‖ : ℂ))
    (hθRl : ∀ t, Complex.exp ((θR t : ℂ) * Complex.I) =
      (F (0, cornerSecondHalf t) - w) / (‖F (0, cornerSecondHalf t) - w‖ : ℂ))
    (hψLl : ∀ t, Complex.exp ((ψL t : ℂ) * Complex.I) =
      (F (1, cornerFirstHalf t) - w) / (‖F (1, cornerFirstHalf t) - w‖ : ℂ))
    (hψRl : ∀ t, Complex.exp ((ψR t : ℂ) * Complex.I) =
      (F (1, cornerSecondHalf t) - w) / (‖F (1, cornerSecondHalf t) - w‖ : ℂ)) :
    (θL 1 - θL 0) + (θR 1 - θR 0) =
      (ψL 1 - ψL 0) + (ψR 1 - ψR 0) := by
  have hF0 : Continuous (fun t : Icc (0 : ℝ) 1 => F (0, t) - w) :=
    (hF.comp (continuous_const.prodMk continuous_id)).sub continuous_const
  have hF1 : Continuous (fun t : Icc (0 : ℝ) 1 => F (1, t) - w) :=
    (hF.comp (continuous_const.prodMk continuous_id)).sub continuous_const
  obtain ⟨Θ, hΘ, hΘl⟩ := exists_interval_euclidean_angle_lift hF0
    (fun t => sub_ne_zero.mpr (havoid (0, t)))
  obtain ⟨Ψ, hΨ, hΨl⟩ := exists_interval_euclidean_angle_lift hF1
    (fun t => sub_ne_zero.mpr (havoid (1, t)))
  have hinc := endpoint_fixed_arc_point_argument_homotopy F hF hstart hfinish w havoid
    Θ Ψ hΘ hΨ hΘl hΨl
  have hold := two_half_argument_increment θL θR Θ hθL hθR hΘ
    (fun t => by apply Circle.ext; exact (hθLl t).trans (hΘl (cornerFirstHalf t)).symm)
    (fun t => by apply Circle.ext; exact (hθRl t).trans (hΘl (cornerSecondHalf t)).symm)
  have hnew := two_half_argument_increment ψL ψR Ψ hψL hψR hΨ
    (fun t => by apply Circle.ext; exact (hψLl t).trans (hΨl (cornerFirstHalf t)).symm)
    (fun t => by apply Circle.ext; exact (hψRl t).trans (hΨl (cornerSecondHalf t)).symm)
  exact hold.trans (hinc.trans hnew.symm)

end RepulsiveCoulomb
