import LeanResearch.RepulsiveCoulomb.PointSmoothJoinTangents
import LeanResearch.RepulsiveCoulomb.JordanEndpointReparameterization
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Right-collar derivative alignment and actual middle-only speed matching.
The two analytic radial collars are unchanged. Only the analytic middle is
composed with a constructed strictly increasing polynomial. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem affine_trace_tangent_at_one {g η : ℝ → ℂ} (s t : ℝ)
    (hg : DifferentiableAt ℝ g t) (hη : DifferentiableAt ℝ η 1)
    (heq : ∀ u ∈ Icc (0 : ℝ) 1, η u = g (s + u * (t - s))) :
    deriv η 1 = (t - s) • deriv g t := by
  let φ : ℝ → ℝ := fun u => s + u * (t - s)
  have hφ : HasDerivAt φ (t - s) 1 := by
    convert! ((hasDerivAt_id (1 : ℝ)).mul_const (t - s)).const_add s using 1 <;> simp [φ]
  have hg' : HasDerivAt g (deriv g t) (φ 1) := by
    have hφ1 : φ 1 = t := by dsimp [φ]; ring
    rw [hφ1]
    exact hg.hasDerivAt
  have hcomp := hg'.scomp (1 : ℝ) hφ
  exact (deriv_eq_of_eqOn_unitInterval (by norm_num) hη hcomp.differentiableAt heq).trans hcomp.deriv

/-- The terminal collar is stored in the forward orientation even though its
power law is centered at the terminal vertex. -/
theorem affine_power_finish_collar_tangent {g right : ℝ → ℂ} (v t β : ℝ)
    (hg : DifferentiableAt ℝ g v) (hr : DifferentiableAt ℝ right 0)
    (heq : ∀ u ∈ Icc (0 : ℝ) 1,
      g (t + u * (v - t)) = right (1 - u ^ β)) :
    (t - v) • deriv g v = β • deriv right 0 := by
  have hr' : HasDerivAt right (deriv right 0) ((1 : ℝ) - 1) := by
    simpa only [sub_self] using hr.hasDerivAt
  have hrev : HasDerivAt (fun u : ℝ => right (1 - u)) (-deriv right 0) 1 :=
    hr'.comp_const_sub 1 1
  have h := affine_power_collar_tangent t v β hg hrev.differentiableAt heq
  rw [hrev.deriv] at h
  calc
    (t - v) • deriv g v = -((v - t) • deriv g v) := by
      rw [show t - v = -(v - t) by ring, neg_smul]
    _ = -(β • -deriv right 0) := congrArg Neg.neg h
    _ = β • deriv right 0 := by simp

/-- The actual affine middle and reversed power-law terminal collar have
positively proportional oriented tangents at their artificial join. -/
theorem affine_middle_power_finish_join_positive_tangent {g middle right : ℝ → ℂ}
    {u v t β : ℝ} (huv : u < v) (hvt : v < t) (hβ : 0 < β)
    (hg : DifferentiableAt ℝ g v) (hm : DifferentiableAt ℝ middle 1)
    (hr : DifferentiableAt ℝ right 0)
    (hmiddle : ∀ s ∈ Icc (0 : ℝ) 1, middle s = g (u + s * (v - u)))
    (hright : ∀ s ∈ Icc (0 : ℝ) 1,
      g (t + s * (v - t)) = right (1 - s ^ β)) :
    ∃ c : ℝ, 0 < c ∧ deriv right 0 = c • deriv middle 1 := by
  have hM := affine_trace_tangent_at_one u v hg hm hmiddle
  have hR := affine_power_finish_collar_tangent v t β hg hr hright
  have hscaled := congrArg (fun w : ℂ => β⁻¹ • w) hR
  rw [smul_smul, smul_smul, inv_mul_cancel₀ hβ.ne', one_smul] at hscaled
  refine ⟨β⁻¹ * ((t - v) / (v - u)),
    mul_pos (inv_pos.mpr hβ) (div_pos (sub_pos.mpr hvt) (sub_pos.mpr huv)), ?_⟩
  rw [hM, smul_smul, mul_assoc, div_mul_cancel₀ _ (sub_ne_zero.mpr huv.ne')]
  exact hscaled.symm

/-- Construct a middle-only reparameterization matching both actual collar
velocities. Its positive derivative preserves orientation and regularity, and
its exact interval image preserves all geometric intersection information. -/
theorem exists_middle_only_collar_velocity_reparameterization
    {left middle right : ℝ → ℂ} {cL cR : ℝ}
    (hL : 0 < cL) (hR : 0 < cR)
    (hM : ContDiff ℝ (↑(⊤ : ℕ∞)) middle)
    (hMi : InjOn middle (Icc (0 : ℝ) 1))
    (hMr : ∀ t ∈ Icc (0 : ℝ) 1, deriv middle t ≠ 0)
    (hleft : deriv middle 0 = cL • deriv left 1)
    (hright : deriv right 0 = cR • deriv middle 1) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) φ ∧
      StrictMonoOn φ (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, 0 < deriv φ t) ∧
      φ 0 = 0 ∧ φ 1 = 1 ∧ φ '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (middle ∘ φ) ∧
      InjOn (middle ∘ φ) (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, deriv (middle ∘ φ) t ≠ 0) ∧
      (middle ∘ φ) 0 = middle 0 ∧ (middle ∘ φ) 1 = middle 1 ∧
      deriv (middle ∘ φ) 0 = deriv left 1 ∧
      deriv (middle ∘ φ) 1 = deriv right 0 ∧
      (middle ∘ φ) '' Icc (0 : ℝ) 1 = middle '' Icc (0 : ℝ) 1 := by
  obtain ⟨φ, hφ, hφ0, hφ1, hd0, hd1, hdpos, hmono, himage⟩ :=
    exists_smooth_positive_endpoint_reparameterization (inv_pos.mpr hL) hR
  have hmap : MapsTo φ (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro t ht
    rw [← himage]
    exact mem_image_of_mem φ ht
  have hderiv (t : ℝ) :
      deriv (middle ∘ φ) t = deriv φ t • deriv middle (φ t) :=
    ((hM.differentiable (by simp) (φ t)).hasDerivAt.scomp t
      (hφ.differentiable (by simp) t).hasDerivAt).deriv
  refine ⟨φ, hφ, hmono, hdpos, hφ0, hφ1, himage, hM.comp hφ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs t ht heq
    exact hmono.injOn hs ht (hMi (hmap hs) (hmap ht) heq)
  · intro t ht
    rw [hderiv]
    exact smul_ne_zero (hdpos t ht).ne' (hMr (φ t) (hmap ht))
  · simp only [Function.comp_apply, hφ0]
  · simp only [Function.comp_apply, hφ1]
  · rw [hderiv, hd0, hφ0, hleft, smul_smul, inv_mul_cancel₀ hL.ne', one_smul]
  · rw [hderiv, hd1, hφ1]
    exact hright.symm
  · rw [image_comp, himage]

end RepulsiveCoulomb
