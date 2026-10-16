module

public import LeanResearch.RepulsiveCoulomb.JordanTurnAngleLift
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

@[expose] public section

/-! Differentiate an actual continuous argument lift. The local logarithm is
constructed by dividing by the nonzero base vector; the principal branch is
used only after both arguments have been proved to lie in its injective window.
This supplies the analytic input for point-argument variation in conformal turn. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem hasDerivAt_continuous_argument_lift {η : ℝ → ℂ} {θ : ℝ → ℝ} {t : ℝ}
    (hη : DifferentiableAt ℝ η t) (hne : η t ≠ 0) (hθ : ContinuousAt θ t)
    (hlift : ∀ᶠ s in 𝓝 t,
      Complex.exp ((θ s : ℂ) * Complex.I) = η s / (‖η s‖ : ℂ)) :
    HasDerivAt θ (deriv η t / η t).im t := by
  have hratio : η t / η t ∈ Complex.slitPlane := by
    rw [div_self hne]
    simp
  have hθ0 : Circle.exp (θ t) = euclideanDirection (η t) hne :=
    Subtype.ext hlift.self_of_nhds
  have hθN : ∀ᶠ s in 𝓝 t, θ s - θ t ∈ Ioo (-Real.pi) Real.pi := by
    apply (hθ.sub continuousAt_const).tendsto.eventually
    change Ioo (-Real.pi) Real.pi ∈ 𝓝 (θ t - θ t)
    simpa only [sub_self] using Ioo_mem_nhds (neg_neg_of_pos Real.pi_pos) Real.pi_pos
  have hargC : ContinuousAt (fun s => Complex.arg (η s / η t)) t :=
    (Complex.continuousAt_arg hratio).comp (f := fun s : ℝ => η s / η t)
      (hη.continuousAt.div_const (η t))
  have hargN : ∀ᶠ s in 𝓝 t, Complex.arg (η s / η t) ∈ Ioo (-Real.pi) Real.pi := by
    apply hargC.tendsto.eventually
    change Ioo (-Real.pi) Real.pi ∈ 𝓝 (Complex.arg (η t / η t))
    simpa only [div_self hne, Complex.arg_one] using
      Ioo_mem_nhds (neg_neg_of_pos Real.pi_pos) Real.pi_pos
  have hnonzero : ∀ᶠ s in 𝓝 t, η s ≠ 0 :=
    hη.continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hne)
  have heq : θ =ᶠ[𝓝 t] (fun s => θ t + (Complex.log (η s / η t)).im) := by
    filter_upwards [hθN, hargN, hnonzero, hlift] with s hsθ hsarg hsne hslift
    have hθs : Circle.exp (θ s) = euclideanDirection (η s) hsne := Subtype.ext hslift
    have hexp : Circle.exp (θ s - θ t) = Circle.exp (Complex.arg (η s / η t)) := by
      rw [Circle.exp_sub, hθs, hθ0, circle_exp_arg_vector_ratio (η s) (η t) hsne hne]
    have hargEq := (Circle.exp_injOn_Ico (a := -Real.pi) (b := Real.pi) (by linarith))
      ⟨hsθ.1.le, hsθ.2⟩ ⟨hsarg.1.le, hsarg.2⟩ hexp
    rw [Complex.log_im]
    linarith
  have hlog : HasDerivAt (fun s => Complex.log (η s / η t)) (deriv η t / η t) t := by
    simpa only [div_self hne, div_one] using (hη.hasDerivAt.div_const (η t)).clog_real hratio
  have hderiv : HasDerivAt (fun s => θ t + (Complex.log (η s / η t)).im)
      (deriv η t / η t).im t := by
    convert! (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hlog).const_add (θ t) using 1 <;>
      simp [Function.comp_def]
  exact hderiv.congr_of_eventuallyEq heq

end RepulsiveCoulomb
