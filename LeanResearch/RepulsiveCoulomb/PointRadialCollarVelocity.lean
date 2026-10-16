import LeanResearch.RepulsiveCoulomb.PointPositiveWindingSectorChoice
import LeanResearch.RepulsiveCoulomb.PointRadialSectorNormalization

/-! Choose an actual regular point on the outgoing radial collar of the
original loop. Its positive chart velocity is derived by differentiating the
literal inverse-chart formula, not assumed as an orientation certificate. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem exists_outgoing_radial_collar_positive_velocity
    (γ : ℝ → ℂ) (e : OpenPartialHomeomorph ℂ ℂ)
    (he : ∀ z ∈ e.source, AnalyticAt ℂ e z)
    (hinv : AnalyticOnNhd ℂ e.symm e.target)
    {l c R : ℝ} (hl : 0 < l) (hl1 : l < 1) (hc : 0 < c) (hR : 0 < R)
    (hball : ball (0 : ℂ) R ⊆ e.target)
    (hleft : ∀ t ∈ Icc (0 : ℝ) l, γ t = e.symm (pointRadialSectorPoint (c * t) 0)) :
    ∃ a r : ℝ, a ∈ Ioo (0 : ℝ) l ∧ a ∈ Icc (0 : ℝ) 1 ∧
      0 < r ∧ r < R ∧ γ a ∈ e.source ∧ e (γ a) = (r : ℂ) ∧
      DifferentiableAt ℝ γ a ∧ deriv γ a ≠ 0 ∧
      deriv e (γ a) * deriv γ a = (c : ℂ) := by
  let a := min (l / 2) (R / (2 * c))
  let r := c * a
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have hal : a < l := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have haR : r < R := by
    have h := (le_div_iff₀ (show 0 < 2 * c by positivity)).mp (min_le_right (l / 2) (R / (2 * c)))
    dsimp [r]
    nlinarith
  have hr : 0 < r := mul_pos hc ha
  have hrad : pointRadialSectorPoint (c * a) 0 ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right, pointRadialSectorPoint_norm hr.le]
    exact haR
  have hradtarget := hball hrad
  have hγa : γ a = e.symm (pointRadialSectorPoint (c * a) 0) := hleft a ⟨ha.le, hal.le⟩
  have hsource : γ a ∈ e.source := by rw [hγa]; exact e.symm.mapsTo hradtarget
  have hposition : e (γ a) = (r : ℂ) := by
    rw [hγa, e.right_inv hradtarget, pointRadialSectorPoint_angle_zero]
  have hparam : γ =ᶠ[𝓝 a] (fun t => e.symm (pointRadialSectorPoint (c * t) 0)) := by
    filter_upwards [Ioo_mem_nhds ha hal] with t ht
    exact hleft t ⟨ht.1.le, ht.2.le⟩
  have hinput : HasDerivAt (fun t : ℝ => pointRadialSectorPoint (c * t) 0) (c : ℂ) a := by
    convert! ((hasDerivAt_id a).const_mul c).ofReal_comp using 1 <;>
      simp [pointRadialSectorPoint_angle_zero]
  have hγd : DifferentiableAt ℝ γ a :=
    (((hinv _ hradtarget).differentiableAt.hasDerivAt.comp
      (h := fun t : ℝ => pointRadialSectorPoint (c * t) 0) a hinput).congr_of_eventuallyEq hparam).differentiableAt
  have htargetN : ∀ᶠ t in 𝓝 a, pointRadialSectorPoint (c * t) 0 ∈ e.target :=
    hinput.continuousAt.tendsto (e.open_target.mem_nhds hradtarget)
  have hdeveloped : (e ∘ γ) =ᶠ[𝓝 a] (fun t : ℝ => ((c * t : ℝ) : ℂ)) := by
    filter_upwards [hparam, htargetN] with t ht htT
    change e (γ t) = ((c * t : ℝ) : ℂ)
    calc
      e (γ t) = e (e.symm (pointRadialSectorPoint (c * t) 0)) := congrArg e ht
      _ = pointRadialSectorPoint (c * t) 0 := e.right_inv htT
      _ = ((c * t : ℝ) : ℂ) := pointRadialSectorPoint_angle_zero (c * t)
  have hDdev : HasDerivAt (fun t : ℝ => ((c * t : ℝ) : ℂ)) (c : ℂ) a := by
    convert! ((hasDerivAt_id a).const_mul c).ofReal_comp using 1 <;> simp
  have hvelocity : deriv e (γ a) * deriv γ a = (c : ℂ) := by
    have hcD := ((he _ hsource).differentiableAt.hasDerivAt.comp a hγd.hasDerivAt).deriv
    have hdev : deriv (e ∘ γ) a = (c : ℂ) := hdeveloped.deriv_eq.trans hDdev.deriv
    exact hcD.symm.trans hdev
  have hregular : deriv γ a ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hvelocity
    exact (Complex.ofReal_ne_zero.mpr hc.ne') hvelocity.symm
  exact ⟨a, r, ⟨ha, hal⟩, ⟨ha.le, (hal.trans hl1).le⟩, hr, haR,
    hsource, hposition, hγd, hregular, hvelocity⟩

end RepulsiveCoulomb
