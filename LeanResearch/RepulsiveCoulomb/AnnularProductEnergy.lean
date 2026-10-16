import LeanResearch.RepulsiveCoulomb.PointScoreAnnularMass

/-! Physical product-gradient control and tunable Young absorption for the
actual score exceptional-annulus estimate. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem physical_gradient_mul {f g : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    gradient (fun x => f x * g x) z =
      f z • gradient g z + g z • gradient f z := by
  apply (InnerProductSpace.toDual ℝ ℂ).injective
  simp only [toDual_gradient, map_add, map_smul]
  exact fderiv_fun_mul hf hg

theorem annular_product_gradient_sq_le {R C : ℝ} (hR : 0 < R)
    (hC : 0 ≤ C) (hbound : ∀ z : ℂ, ‖gradient (annularCutoff R) z‖ ≤ C / R)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ) (z : ℂ) :
    ‖gradient (fun x => annularCutoff R x * ψ x) z‖ ^ 2 ≤
      2 * ‖gradient ψ z‖ ^ 2 + 2 * (C / R) ^ 2 * ψ z ^ 2 := by
  rw [physical_gradient_mul ((annularCutoff_contDiff R).differentiable (by simp) z)
    (hψ.differentiable (by simp) z)]
  have hc := annularCutoff_mem_Icc R z
  have hn := norm_add_le (annularCutoff R z • gradient ψ z)
    (ψ z • gradient (annularCutoff R) z)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hc.1] at hn
  have ht : ‖annularCutoff R z • gradient ψ z + ψ z • gradient (annularCutoff R) z‖ ≤
      ‖gradient ψ z‖ + |ψ z| * (C / R) := by
    calc
      _ ≤ annularCutoff R z * ‖gradient ψ z‖ + |ψ z| * ‖gradient (annularCutoff R) z‖ := hn
      _ ≤ 1 * ‖gradient ψ z‖ + |ψ z| * (C / R) := by
        gcongr
        · exact hc.2
        · exact hbound z
      _ = _ := by ring
  have habs := sq_abs (ψ z)
  have hs := sq_nonneg (‖gradient ψ z‖ - |ψ z| * (C / R))
  have hp : 0 ≤ ‖gradient ψ z‖ + |ψ z| * (C / R) :=
    add_nonneg (norm_nonneg _) (mul_nonneg (abs_nonneg _) (div_nonneg hC hR.le))
  have hsquare := mul_self_le_mul_self (norm_nonneg _) ht
  nlinarith

theorem annular_product_gradient_zero_off {R : ℝ} (hR : 0 < R)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ) {z : ℂ}
    (hz : z ∉ {x : ℂ | R / 2 < ‖x‖ ∧ ‖x‖ < 4 * R}) :
    gradient (fun x => annularCutoff R x * ψ x) z = 0 := by
  have hc : z ∉ tsupport (annularCutoff R) := fun h => hz (annularCutoff_tsupport_strict hR h)
  rw [physical_gradient_mul ((annularCutoff_contDiff R).differentiable (by simp) z)
    (hψ.differentiable (by simp) z), image_eq_zero_of_notMem_tsupport hc,
    TauCeti.gradient_of_notMem_tsupport hc]
  simp

theorem sqrt_product_young {K R A B δ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hδ : 0 < δ) :
    K * R * Real.sqrt A * Real.sqrt B ≤ δ * R ^ 2 * A + K ^ 2 / (4 * δ) * B := by
  have h := sq_nonneg (2 * δ * R * Real.sqrt A - K * Real.sqrt B)
  have ha := Real.sq_sqrt hA
  have hb := Real.sq_sqrt hB
  have hd : 0 < 4 * δ := by positivity
  apply (mul_le_mul_iff_left₀ hd).mp
  have he : K ^ 2 / (4 * δ) * (4 * δ) = K ^ 2 := div_mul_cancel₀ _ (ne_of_gt hd)
  have hh : 0 ≤ 4 * δ ^ 2 * R ^ 2 * A -
      4 * δ * R * K * Real.sqrt A * Real.sqrt B + K ^ 2 * B := by
    calc
      0 ≤ (2 * δ * R * Real.sqrt A - K * Real.sqrt B) ^ 2 := h
      _ = _ := by rw [sub_sq]; simp only [mul_pow, ha, hb]; ring
  have heB := congrArg (fun t : ℝ => t * B) he
  nlinarith only [hh, heB]

theorem pointScore_bad_annulus_mass_young {m : ℕ} {γ Q R δ : ℝ}
    (hγ : 0 < γ) (hR : 0 < R) (hδ : 0 < δ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hQ : ∑ j, a j ≤ Q) (ψ : ℂ → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    R ^ 2 * (∫ x in pointScoreBadAnnulus γ a y R, ψ x ^ 2) ≤
      δ * R ^ 2 * (∫ x : ℂ, (annularCutoff R x * ψ x) ^ 2) +
      pointScoreAnnularMassConstant γ Q ^ 2 / (4 * δ) *
        (∫ x : ℂ, ‖gradient (fun z => annularCutoff R z * ψ z) x‖ ^ 2) := by
  exact (pointScore_bad_annulus_mass_cutoff hγ hR ha y hQ ψ hψ).trans
    (sqrt_product_young (integral_nonneg (fun _ => sq_nonneg _))
      (integral_nonneg (fun _ => sq_nonneg _)) hδ)

end RepulsiveCoulomb
