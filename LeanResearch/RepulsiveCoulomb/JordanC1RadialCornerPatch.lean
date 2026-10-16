module

public import LeanResearch.RepulsiveCoulomb.JordanC1Joining
public import LeanResearch.RepulsiveCoulomb.JordanHolomorphicBezierArc
public import LeanResearch.RepulsiveCoulomb.JordanSymmetricCornerPatch

@[expose] public section

/-! Construct an actual global C¹ replacement across one radial chart corner.
The collar functions are left unchanged outside the two equal-width cuts.
The replacement matches both actual endpoint jets and is regular between the
cuts. No smooth-gluing certificate is supplied. Records-only draft. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem exists_C1_radial_corner_patch
    {H : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hH : AnalyticOnNhd ℂ H U) (hHreg : ∀ z ∈ U, deriv H z ≠ 0)
    (hHinj : InjOn H U) {δ : ℝ} (hδ : 0 < δ) {u v : ℂ}
    (hu : u ≠ 0) (hc : v / u ∈ Complex.slitPlane)
    (hBU : MapsTo (euclideanBezierCorner (δ • u) (δ • v)) (Icc (0 : ℝ) 1) U)
    {L R : ℝ → ℂ} (hL : ContDiff ℝ 1 L) (hR : ContDiff ℝ 1 R)
    (hLrad : L =ᶠ[𝓝 (-δ)] (fun t : ℝ => H (t • u)))
    (hRrad : R =ᶠ[𝓝 δ] (fun t : ℝ => H (t • v))) :
    ∃ G : ℝ → ℂ, ContDiff ℝ 1 G ∧
      (∀ t, t ≤ -δ → G t = L t) ∧
      (∀ t, δ ≤ t → G t = R t) ∧
      (∀ t ∈ Icc (-δ) δ, G t = H (euclideanSymmetricCornerPatch δ u v t)) ∧
      (∀ t ∈ Icc (-δ) δ, deriv G t ≠ 0) ∧
      (∀ t, t < -δ → G =ᶠ[𝓝 t] L) ∧
      (∀ t, δ < t → G =ᶠ[𝓝 t] R) := by
  have hδu : δ • u ≠ 0 := smul_ne_zero hδ.ne' hu
  have hcδ : (δ • v) / (δ • u) ∈ Complex.slitPlane := by
    have he : (δ • v) / (δ • u) = v / u := by
      have hδc : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
      simp only [Complex.real_smul]
      field_simp [hδc, hu]
    rwa [he]
  obtain ⟨B, hB, hBgerm, _, hBreg, _, _, _, _, _⟩ :=
    exists_holomorphic_bezier_smooth_arc hU hH hHreg hHinj hδu hcδ hBU
  let a : ℝ → ℝ := fun t => (t + δ) / (2 * δ)
  let P : ℝ → ℂ := B ∘ a
  have h2δ : 0 < 2 * δ := by positivity
  have ha : ContDiff ℝ 1 a := by dsimp [a]; fun_prop
  have ha0 : a (-δ) = 0 := by simp [a]
  have ha1 : a δ = 1 := by dsimp [a]; field_simp [hδ.ne']; ring
  have hamap {t : ℝ} (ht : t ∈ Icc (-δ) δ) : a t ∈ Icc (0 : ℝ) 1 := by
    dsimp [a]
    exact ⟨div_nonneg (by linarith [ht.1]) h2δ.le,
      (div_le_one h2δ).mpr (by linarith [ht.2])⟩
  have hP : ContDiff ℝ 1 P := (hB.of_le (by simp)).comp ha
  have hPeq {t : ℝ} (ht : t ∈ Icc (-δ) δ) :
      P t = H (euclideanSymmetricCornerPatch δ u v t) :=
    (hBgerm (a t) (hamap ht)).self_of_nhds
  have hPgl : P =ᶠ[𝓝 (-δ)] (H ∘ euclideanSymmetricCornerPatch δ u v) := by
    have ht : Tendsto a (𝓝 (-δ)) (𝓝 0) := by simpa only [ha0] using ha.continuous.tendsto (-δ)
    exact (hBgerm 0 (by norm_num)).comp_tendsto ht
  have hPgr : P =ᶠ[𝓝 δ] (H ∘ euclideanSymmetricCornerPatch δ u v) := by
    have ht : Tendsto a (𝓝 δ) (𝓝 1) := by simpa only [ha1] using ha.continuous.tendsto δ
    exact (hBgerm 1 (by norm_num)).comp_tendsto ht
  have hleftU : (-δ) • u ∈ U := by
    simpa only [euclideanBezierCorner_zero, neg_smul] using hBU (by norm_num : (0 : ℝ) ∈ Icc 0 1)
  have hrightU : δ • v ∈ U := by
    simpa only [euclideanBezierCorner_one] using hBU (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  have hjets := holomorphic_symmetric_corner_endpoint_jets hδ.ne' u v
    (hH _ hleftU).differentiableAt (hH _ hrightU).differentiableAt
  have hvL : L (-δ) = P (-δ) := by
    rw [hLrad.self_of_nhds, hPeq (show -δ ∈ Icc (-δ) δ by constructor <;> linarith),
      euclideanSymmetricCornerPatch_left hδ.ne']
  have hvR : P δ = R δ := by
    rw [hRrad.self_of_nhds, hPeq (show δ ∈ Icc (-δ) δ by constructor <;> linarith),
      euclideanSymmetricCornerPatch_right hδ.ne']
  have hjL : deriv L (-δ) = deriv P (-δ) :=
    hLrad.deriv_eq.trans (hjets.1.symm.trans hPgl.deriv_eq.symm)
  have hjR : deriv P δ = deriv R δ :=
    hPgr.deriv_eq.trans (hjets.2.trans hRrad.deriv_eq.symm)
  let A := euclideanC1Glue (-δ) L P
  have hA : ContDiff ℝ 1 A := euclideanC1Glue_contDiff hL hP hvL hjL
  have hvA : A δ = R δ := (euclideanC1Glue_eq_right hvL (by linarith)).trans hvR
  have hjA : deriv A δ = deriv R δ := by
    rw [euclideanC1Glue_deriv (hL.differentiable (by norm_num))
      (hP.differentiable (by norm_num)) hvL hjL,
      if_neg (show ¬δ ≤ -δ by linarith), hjR]
  let G := euclideanC1Glue δ A R
  have hG : ContDiff ℝ 1 G := euclideanC1Glue_contDiff hA hR hvA hjA
  have hGL (t : ℝ) (ht : t ≤ -δ) : G t = L t := by
    change euclideanC1Glue δ A R t = L t
    rw [euclideanC1Glue_eq_left δ A R (show t ≤ δ by linarith)]
    exact euclideanC1Glue_eq_left (-δ) L P ht
  have hGR (t : ℝ) (ht : δ ≤ t) : G t = R t := euclideanC1Glue_eq_right hvA ht
  have hGP (t : ℝ) (ht : t ∈ Icc (-δ) δ) : G t = P t := by
    change euclideanC1Glue δ A R t = P t
    rw [euclideanC1Glue_eq_left δ A R ht.2]
    exact euclideanC1Glue_eq_right hvL ht.1
  refine ⟨G, hG, hGL, hGR, fun t ht => (hGP t ht).trans (hPeq ht), ?_, ?_, ?_⟩
  · intro t ht
    have hPD : deriv P t = (2 * δ)⁻¹ • deriv B (a t) := by
      have hinner : HasDerivAt a (2 * δ)⁻¹ t := by
        simpa only [a, one_div, id_eq] using ((hasDerivAt_id t).add_const δ).div_const (2 * δ)
      exact ((((hB.differentiable (by simp)) (a t)).hasDerivAt).scomp t hinner).deriv
    have hPn : deriv P t ≠ 0 := by
      rw [hPD]
      exact smul_ne_zero (inv_ne_zero h2δ.ne') (hBreg _ (hamap ht))
    have hGD : deriv G t = deriv P t := by
      rw [euclideanC1Glue_deriv (hA.differentiable (by norm_num))
        (hR.differentiable (by norm_num)) hvA hjA, if_pos ht.2,
        euclideanC1Glue_deriv (hL.differentiable (by norm_num))
          (hP.differentiable (by norm_num)) hvL hjL]
      split_ifs with hcut
      · have heq : t = -δ := le_antisymm hcut ht.1
        simpa only [heq] using hjL
      · rfl
    rwa [hGD]
  · intro t ht
    filter_upwards [gt_mem_nhds ht] with s hs
    exact hGL s hs.le
  · intro t ht
    filter_upwards [lt_mem_nhds ht] with s hs
    exact hGR s hs.le

end RepulsiveCoulomb
