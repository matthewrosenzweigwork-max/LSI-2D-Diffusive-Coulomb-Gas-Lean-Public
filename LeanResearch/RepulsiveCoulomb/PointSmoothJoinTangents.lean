module

public import LeanResearch.RepulsiveCoulomb.PointSmoothArcCollars
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

/-! Actual derivative alignment at artificial collar/middle joins. Equality
on the closed interval suffices by one-sided derivative uniqueness at its
endpoints; a false full-neighborhood equality is never assumed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem deriv_eq_of_eqOn_unitInterval {f g : ℝ → ℂ} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hf : DifferentiableAt ℝ f t)
    (hg : DifferentiableAt ℝ g t) (heq : EqOn f g (Icc (0 : ℝ) 1)) :
    deriv f t = deriv g t := by
  have hud := uniqueDiffOn_Icc_zero_one t ht
  calc
    deriv f t = derivWithin f (Icc (0 : ℝ) 1) t :=
      (hf.hasDerivAt.hasDerivWithinAt.derivWithin hud).symm
    _ = derivWithin g (Icc (0 : ℝ) 1) t := derivWithin_congr heq (heq ht)
    _ = deriv g t := hg.hasDerivAt.hasDerivWithinAt.derivWithin hud

/-- The actual power law on the closed collar gives the tangent relation at
its positive cutoff, even though metric time can be singular at the vertex. -/
theorem power_collar_tangent_at_one {f η : ℝ → ℂ} (β : ℝ)
    (hf : DifferentiableAt ℝ f 1) (hη : DifferentiableAt ℝ η 1)
    (heq : ∀ u ∈ Icc (0 : ℝ) 1, f u = η (u ^ β)) :
    deriv f 1 = β • deriv η 1 := by
  have hp : HasDerivAt (fun u : ℝ => u ^ β) β 1 := by
    simpa only [Real.one_rpow, mul_one] using
      (Real.hasDerivAt_rpow_const (x := 1) (p := β) (Or.inl one_ne_zero))
  have hη' : HasDerivAt η (deriv η 1) ((1 : ℝ) ^ β) := by
    simpa only [Real.one_rpow] using hη.hasDerivAt
  have hcomp := hη'.scomp (1 : ℝ) hp
  simp only [Function.comp_def] at hcomp
  exact (deriv_eq_of_eqOn_unitInterval (by norm_num) hf hcomp.differentiableAt heq).trans hcomp.deriv

theorem affine_power_collar_tangent {g η : ℝ → ℂ} (s t β : ℝ)
    (hg : DifferentiableAt ℝ g t) (hη : DifferentiableAt ℝ η 1)
    (heq : ∀ u ∈ Icc (0 : ℝ) 1, g (s + u * (t - s)) = η (u ^ β)) :
    (t - s) • deriv g t = β • deriv η 1 := by
  let φ : ℝ → ℝ := fun u => s + u * (t - s)
  have hφ : HasDerivAt φ (t - s) 1 := by
    convert! ((hasDerivAt_id (1 : ℝ)).mul_const (t - s)).const_add s using 1 <;> simp [φ]
  have hg' : HasDerivAt g (deriv g t) (φ 1) := by
    have hφ1 : φ 1 = t := by dsimp [φ]; ring
    rw [hφ1]
    exact hg.hasDerivAt
  have hcomp := hg'.scomp (1 : ℝ) hφ
  have h := power_collar_tangent_at_one β hcomp.differentiableAt hη heq
  rw [hcomp.deriv] at h
  exact h

theorem affine_trace_tangent_at_zero {g η : ℝ → ℂ} (s t : ℝ)
    (hg : DifferentiableAt ℝ g s) (hη : DifferentiableAt ℝ η 0)
    (heq : ∀ u ∈ Icc (0 : ℝ) 1, η u = g (s + u * (t - s))) :
    deriv η 0 = (t - s) • deriv g s := by
  let φ : ℝ → ℝ := fun u => s + u * (t - s)
  have hφ : HasDerivAt φ (t - s) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).mul_const (t - s)).const_add s using 1 <;> simp [φ]
  have hg' : HasDerivAt g (deriv g s) (φ 0) := by
    simpa only [φ, zero_mul, add_zero] using hg.hasDerivAt
  have hcomp := hg'.scomp (0 : ℝ) hφ
  exact (deriv_eq_of_eqOn_unitInterval (by norm_num) hη hcomp.differentiableAt heq).trans hcomp.deriv

/-- The stored collar and middle formulas force positive oriented tangent
alignment at their artificial join. The coefficient is explicitly positive. -/
theorem power_collar_affine_join_positive_tangent {g left middle : ℝ → ℂ}
    {s u v β : ℝ} (hsu : s < u) (huv : u < v) (hβ : 0 < β)
    (hg : DifferentiableAt ℝ g u) (hl : DifferentiableAt ℝ left 1)
    (hm : DifferentiableAt ℝ middle 0)
    (hleft : ∀ t ∈ Icc (0 : ℝ) 1, g (s + t * (u - s)) = left (t ^ β))
    (hmiddle : ∀ t ∈ Icc (0 : ℝ) 1, middle t = g (u + t * (v - u))) :
    ∃ c : ℝ, 0 < c ∧ deriv middle 0 = c • deriv left 1 := by
  have hL := affine_power_collar_tangent s u β hg hl hleft
  have hM := affine_trace_tangent_at_zero u v hg hm hmiddle
  have hscaled := congrArg (fun w : ℂ => ((v - u) / (u - s)) • w) hL
  rw [smul_smul, smul_smul, div_mul_cancel₀ _ (sub_ne_zero.mpr hsu.ne')] at hscaled
  exact ⟨((v - u) / (u - s)) * β,
    mul_pos (div_pos (sub_pos.mpr huv) (sub_pos.mpr hsu)) hβ, hM.trans hscaled⟩

end RepulsiveCoulomb
