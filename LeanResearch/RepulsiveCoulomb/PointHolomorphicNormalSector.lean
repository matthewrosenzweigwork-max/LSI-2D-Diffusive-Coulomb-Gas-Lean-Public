module

public import LeanResearch.RepulsiveCoulomb.PointExteriorSectorObservers
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

/-! A positively directed actual left normal enters the left polar sector
in a holomorphic chart. This supplies the missing local orientation test
needed to select one of the two actual Jordan side alternatives. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem eventually_pos_right_of_hasDerivAt_pos_zero {f : ℝ → ℝ} {c : ℝ}
    (hd : HasDerivAt f c 0) (hf0 : f 0 = 0) (hc : 0 < c) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < f t := by
  have hlim : Tendsto (dslope f 0) (𝓝 0) (𝓝 c) := by
    simpa only [dslope_same, hd.deriv] using
      (continuousAt_dslope_same.mpr hd.differentiableAt).tendsto
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < dslope f 0 t := hlim (Ioi_mem_nhds hc)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hpos, self_mem_nhdsWithin] with t hdt ht
  have ht0 : 0 < t := ht
  rw [dslope_of_ne _ ht0.ne', slope_def_field, hf0, sub_zero, sub_zero] at hdt
  exact (div_pos_iff_of_pos_right ht0).mp hdt

/-- The tangent is genuinely sent to the positive real direction by the
chart differential. Its physical left normal therefore enters the actual
polar sector (0,θ), however small θ is and also when θ is reflex. -/
theorem holomorphic_left_normal_eventually_in_radial_sector {E : ℂ → ℂ}
    {p d : ℂ} {r R c θ : ℝ} (hE : DifferentiableAt ℂ E p)
    (hEp : E p = (r : ℂ)) (hr : 0 < r) (hrR : r < R)
    (hc : 0 < c) (hvelocity : deriv E p * d = (c : ℂ)) (hθ : 0 < θ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      E (p + ε • (Complex.I * d)) ∈ pointOpenRadialSector R 0 θ := by
  let F : ℝ → ℂ := fun ε => E (p + ε • (Complex.I * d))
  have hn : HasDerivAt (fun ε : ℝ => p + ε • (Complex.I * d)) (Complex.I * d) 0 := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (Complex.I * d)).const_add p
  have hEt : HasDerivAt E (deriv E p) (p + (0 : ℝ) • (Complex.I * d)) := by
    simpa only [zero_smul, add_zero] using hE.hasDerivAt
  have hprod : deriv E p * (Complex.I * d) = (c : ℂ) * Complex.I := by
    calc
      deriv E p * (Complex.I * d) = (deriv E p * d) * Complex.I := by ring
      _ = (c : ℂ) * Complex.I := by rw [hvelocity]
  have hDF : HasDerivAt F ((c : ℂ) * Complex.I) 0 := by
    simpa only [F, Function.comp_def, hprod] using hEt.comp 0 hn
  have hF0 : F 0 = (r : ℂ) := by simp only [F, zero_smul, add_zero, hEp]
  have hIm : HasDerivAt (fun ε : ℝ => (F ε).im) c 0 := by
    convert! Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hDF using 1 <;>
      simp [Function.comp_def]
  have hIm0 : (F 0).im = 0 := by rw [hF0, Complex.ofReal_im]
  have hImpos := eventually_pos_right_of_hasDerivAt_pos_zero hIm hIm0 hc
  have hnorm : Tendsto (fun ε : ℝ => ‖F ε‖) (𝓝 0) (𝓝 r) := by
    simpa only [hF0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using
      hDF.continuousAt.norm.tendsto
  have hnormR : ∀ᶠ ε in 𝓝 (0 : ℝ), ‖F ε‖ < R := hnorm (Iio_mem_nhds hrR)
  have hslit : F 0 ∈ Complex.slitPlane := by rw [hF0]; exact Complex.ofReal_mem_slitPlane.mpr hr
  have harg : ContinuousAt (fun ε : ℝ => Complex.arg (F ε)) 0 :=
    (Complex.continuousAt_arg hslit).comp (f := F) hDF.continuousAt
  have harg0 : Complex.arg (F 0) = 0 := by rw [hF0, Complex.arg_ofReal_of_nonneg hr.le]
  have harglim : Tendsto (fun ε : ℝ => Complex.arg (F ε)) (𝓝 0) (𝓝 0) := by
    simpa only [harg0] using harg.tendsto
  have hargθ : ∀ᶠ ε in 𝓝 (0 : ℝ), Complex.arg (F ε) < θ := harglim (Iio_mem_nhds hθ)
  filter_upwards [hImpos, mem_nhdsWithin_of_mem_nhds hnormR,
    mem_nhdsWithin_of_mem_nhds hargθ] with ε him hnormε hargε
  have hne : F ε ≠ 0 := by intro he; rw [he, Complex.zero_im] at him; exact (lt_irrefl 0) him
  have hargpos : 0 < Complex.arg (F ε) := by
    have hnonneg := Complex.arg_nonneg_iff.mpr him.le
    have hargne : Complex.arg (F ε) ≠ 0 := fun he => him.ne' (Complex.arg_eq_zero_iff.mp he).2
    exact lt_of_le_of_ne hnonneg (Ne.symm hargne)
  refine ⟨(‖F ε‖, Complex.arg (F ε)), ⟨⟨norm_pos_iff.mpr hne, hnormε⟩, ⟨hargpos, hargε⟩⟩, ?_⟩
  exact Complex.norm_mul_exp_arg_mul_I (F ε)

end RepulsiveCoulomb
