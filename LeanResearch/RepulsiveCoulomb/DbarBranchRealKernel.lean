import LeanResearch.RepulsiveCoulomb.DbarBranchWeakKernelRegularity
import LeanResearch.RepulsiveCoulomb.DbarBranchFormAdapter
import Mathlib.Analysis.Calculus.MeanValue

/-! Real-valued consequences of the actual all-N weak-kernel regularity.
Connectedness is an explicit geometric input here, to be discharged separately
for the full collision complement. No coercive or collision-removal estimate is used. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombHolomorphic_im_zero_of_ae_real {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {f : CoulombConfig N → ℝ} {h : CoulombConfig N → ℂ}
    (hh : DifferentiableOn ℂ h (coulombDomain N))
    (hrep : (fun z => (f z : ℂ)) =ᵐ[coulombMeasure N β] h) :
    ∀ z ∈ coulombDomain N, (h z).im = 0 := by
  have hi : (fun z => (h z).im) =ᵐ[volume.restrict (coulombDomain N)] (fun _ => (0 : ℝ)) := by
    filter_upwards [ae_restrict_of_ae ((coulombMeasure_ae_iff hβ).mp hrep)] with z hz
    rw [← hz]
    exact Complex.ofReal_im _
  exact Measure.eqOn_open_of_ae_eq hi (coulombDomain N).isOpen
    (Complex.imCLM.continuous.comp_continuousOn hh.continuousOn) continuousOn_const

theorem coulombHolomorphic_realPart_fderiv_zero {N : ℕ} {h : CoulombConfig N → ℂ}
    (hh : DifferentiableOn ℂ h (coulombDomain N))
    (hi : ∀ z ∈ coulombDomain N, (h z).im = 0) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) : fderiv ℝ (fun x => (h x).re) z = 0 := by
  let g : CoulombConfig N → ℝ := fun x => (h x).re
  have hd : DifferentiableAt ℂ h z := (hh z hz).differentiableAt ((coulombDomain N).isOpen.mem_nhds hz)
  have hg : DifferentiableAt ℝ g z :=
    Complex.reCLM.differentiableAt.comp z (hd.restrictScalars ℝ)
  have he : (fun x => (g x : ℂ)) =ᶠ[𝓝 z] h := by
    filter_upwards [(coulombDomain N).isOpen.mem_nhds hz] with x hx
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (hi x hx).symm
  have hc : DifferentiableAt ℂ (fun x => (g x : ℂ)) z := hd.congr_of_eventuallyEq he
  have hb := coulombDbar_of_complex_differentiable hc
  rw [coulombDbar_real hg] at hb
  have hgrad : gradient g z = 0 := (smul_eq_zero.mp hb).resolve_left (by norm_num)
  ext v
  rw [← inner_gradient_left, hgrad, inner_zero_left]
  rfl

theorem coulombHolomorphic_ae_real_constant {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (hconn : IsPreconnected (coulombDomain N : Set (CoulombConfig N)))
    {f : CoulombConfig N → ℝ} {h : CoulombConfig N → ℂ}
    (hh : DifferentiableOn ℂ h (coulombDomain N))
    (hrep : (fun z => (f z : ℂ)) =ᵐ[coulombMeasure N β] h) :
    ∃ a : ℝ, f =ᵐ[coulombMeasure N β] fun _ => a := by
  have hi := coulombHolomorphic_im_zero_of_ae_real hβ hh hrep
  have hg : DifferentiableOn ℝ (fun x => (h x).re) (coulombDomain N) :=
    Complex.reCLM.differentiable.comp_differentiableOn (hh.restrictScalars ℝ)
  obtain ⟨a, ha⟩ := (coulombDomain N).isOpen.exists_is_const_of_fderiv_eq_zero hconn hg
    (fun x hx => coulombHolomorphic_realPart_fderiv_zero hh hi hx)
  refine ⟨a, ?_⟩
  filter_upwards [hrep, (coulombMeasure_ae_iff hβ).mpr (coulombDomain_ae N)] with z hz hzΩ
  have hre := congrArg Complex.re hz
  simpa only [Complex.ofReal_re, ha z hzΩ] using hre

theorem coulombForm_zero_gradient_constant_of_connected {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (hconn : IsPreconnected (coulombDomain N : Set (CoulombConfig N)))
    (u : CoulombFormDomain N hβ) (hu : coulombFormGradientL N hβ u = 0) :
    ∃ a : ℝ, coulombFormValueL N hβ u =ᵐ[coulombMeasure N β] fun _ => a := by
  obtain ⟨h, hh, hrep⟩ := (coulombDbarWeakKernel_mem_iff_holomorphic hβ _).mp
    (coulombForm_zero_gradient_mem_weakKernel hβ u hu)
  exact coulombHolomorphic_ae_real_constant hβ hconn hh
    ((coulombFormComplexValueL_coe hβ u).symm.trans hrep)

end RepulsiveCoulomb
