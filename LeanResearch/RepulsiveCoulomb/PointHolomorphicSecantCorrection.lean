module

public import LeanResearch.RepulsiveCoulomb.PointExteriorTwoRayArgument
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.DSlope

@[expose] public section

/-! An actual uniformly chosen phase correction for all short distinct
holomorphic secants. Strict differentiability constructs a disk on which the
normalized secant has positive real part. The correction has the required
vanishing endpoint limit at the vertex; no phase or secant bound is assumed. -/
noncomputable section
open Set Filter Metric Asymptotics
open scoped Topology
namespace RepulsiveCoulomb

def pointHolomorphicSecantRatio (H : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (H z - H w) / ((z - w) * deriv H 0)

def pointHolomorphicSecantCorrection (H : ℂ → ℂ) (z w : ℂ) : ℝ :=
  Complex.arg (deriv H 0) + Complex.arg (pointHolomorphicSecantRatio H z w)

/-- The uniform short-secant phase branch is constructed from actual
holomorphic regularity, including secants with both endpoints moving. -/
theorem exists_holomorphic_secant_positive_disk {U : Set ℂ} (hU : IsOpen U)
    (h0 : (0 : ℂ) ∈ U) {H : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H U)
    (hD : deriv H 0 ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ ball (0 : ℂ) R ⊆ U ∧
      ∀ z ∈ ball (0 : ℂ) R, ∀ w ∈ ball (0 : ℂ) R, z ≠ w →
        ‖pointHolomorphicSecantRatio H z w - 1‖ ≤ 1 / 2 ∧
        0 < (pointHolomorphicSecantRatio H z w).re := by
  have hstrict := (hH 0 h0).hasStrictDerivAt
  have hlo : (fun p : ℂ × ℂ => H p.1 - H p.2 - (p.1 - p.2) * deriv H 0) =o[𝓝 (0, 0)]
      (fun p : ℂ × ℂ => p.1 - p.2) := by
    simpa only [smul_eq_mul] using (hasDerivAtFilter_iff_isLittleO.mp hstrict)
  have hDn : 0 < ‖deriv H 0‖ := norm_pos_iff.mpr hD
  have hev := isLittleO_iff.mp hlo (show 0 < ‖deriv H 0‖ / 2 by positivity)
  obtain ⟨W, hW, h0W, hbound⟩ := exists_nhds_square hev
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp (hW.inter hU) 0 ⟨h0W, h0⟩
  refine ⟨R, hR, (fun z hz => (hball hz).2), ?_⟩
  intro z hz w hw hzw
  have hzn : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have hnorm : 0 < ‖z - w‖ := norm_pos_iff.mpr hzn
  have hb := hbound (show (z, w) ∈ W ×ˢ W from ⟨(hball hz).1, (hball hw).1⟩)
  change ‖H z - H w - (z - w) * deriv H 0‖ ≤ ‖deriv H 0‖ / 2 * ‖z - w‖ at hb
  have hden : (z - w) * deriv H 0 ≠ 0 := mul_ne_zero hzn hD
  have he : pointHolomorphicSecantRatio H z w - 1 =
      (H z - H w - (z - w) * deriv H 0) / ((z - w) * deriv H 0) := by
    unfold pointHolomorphicSecantRatio
    field_simp [hden]
  have hsmall : ‖pointHolomorphicSecantRatio H z w - 1‖ ≤ 1 / 2 := by
    rw [he, norm_div, norm_mul]
    apply (div_le_iff₀ (mul_pos hnorm hDn)).mpr
    nlinarith [hb]
  refine ⟨hsmall, ?_⟩
  have hre := (abs_le.mp (Complex.abs_re_le_norm (pointHolomorphicSecantRatio H z w - 1))).1
  simp only [Complex.sub_re, Complex.one_re] at hre
  linarith

/-- The correction is an actual factorization of the secant argument. -/
theorem pointHolomorphicSecantCorrection_lift {H : ℂ → ℂ} {z w : ℂ}
    (hD : deriv H 0 ≠ 0) (hzw : z ≠ w)
    (hpos : 0 < (pointHolomorphicSecantRatio H z w).re)
    {θ : ℝ} (hθ : Complex.exp ((θ : ℂ) * Complex.I) =
      (z - w) / (‖z - w‖ : ℂ)) :
    H z - H w ≠ 0 ∧
      Complex.exp (((θ + pointHolomorphicSecantCorrection H z w : ℝ) : ℂ) * Complex.I) =
        (H z - H w) / (‖H z - H w‖ : ℂ) := by
  have hzn : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have hQ : pointHolomorphicSecantRatio H z w ≠ 0 :=
    Complex.slitPlane_ne_zero (Or.inl hpos)
  have hfac : (z - w) * (deriv H 0 * pointHolomorphicSecantRatio H z w) = H z - H w := by
    unfold pointHolomorphicSecantRatio
    field_simp [hzn, hD]
  have hnon : H z - H w ≠ 0 := hfac ▸ mul_ne_zero hzn (mul_ne_zero hD hQ)
  have hθ' : Circle.exp θ = euclideanDirection (z - w) hzn := Circle.ext hθ
  have hχ : Circle.exp (pointHolomorphicSecantCorrection H z w) =
      euclideanDirection (deriv H 0 * pointHolomorphicSecantRatio H z w) (mul_ne_zero hD hQ) := by
    rw [pointHolomorphicSecantCorrection, Circle.exp_add,
      ← euclideanDirection_arg _ hD, Circle.exp_arg,
      ← euclideanDirection_arg _ hQ, Circle.exp_arg, ← euclideanDirection_mul]
  have ht : Circle.exp (θ + pointHolomorphicSecantCorrection H z w) =
      euclideanDirection (H z - H w) hnon := by
    rw [Circle.exp_add, hθ', hχ, ← euclideanDirection_mul]
    apply Circle.ext
    simp only [euclideanDirection_coe, hfac]
  exact ⟨hnon, congrArg (fun u : Circle => (u : ℂ)) ht⟩


/-- On any actual off-diagonal domain with the constructed positive secant
branch, the real correction is continuous. -/
theorem pointHolomorphicSecantCorrection_continuousOn {H : ℂ → ℂ}
    {U : Set ℂ} {S : Set (ℂ × ℂ)} (hc : ContinuousOn H U)
    (hmap : S ⊆ U ×ˢ U) (hD : deriv H 0 ≠ 0)
    (hne : ∀ p ∈ S, p.1 ≠ p.2)
    (hpos : ∀ p ∈ S, 0 < (pointHolomorphicSecantRatio H p.1 p.2).re) :
    ContinuousOn (fun p : ℂ × ℂ => pointHolomorphicSecantCorrection H p.1 p.2) S := by
  have hfst : ContinuousOn (fun p : ℂ × ℂ => H p.1) S :=
    hc.comp continuous_fst.continuousOn (fun p hp => (hmap hp).1)
  have hsnd : ContinuousOn (fun p : ℂ × ℂ => H p.2) S :=
    hc.comp continuous_snd.continuousOn (fun p hp => (hmap hp).2)
  have hq : ContinuousOn (fun p : ℂ × ℂ => pointHolomorphicSecantRatio H p.1 p.2) S := by
    unfold pointHolomorphicSecantRatio
    exact (hfst.sub hsnd).div ((continuous_fst.sub continuous_snd).mul_const _).continuousOn
      (fun p hp => mul_ne_zero (sub_ne_zero.mpr (hne p hp)) hD)
  exact continuousOn_const.add (Complex.continuousOn_arg.comp hq
    (fun p hp => Or.inl (hpos p hp)))

/-- At a fixed nonzero endpoint, moving the observer to the vertex gives an
ordinary continuous endpoint correction, within the explicitly positive disk. -/
theorem pointHolomorphicSecantCorrection_observer_limit {H : ℂ → ℂ} {z : ℂ}
    (hc : ContinuousAt H 0) (hD : deriv H 0 ≠ 0) (hz : z ≠ 0)
    (hpos : 0 < (pointHolomorphicSecantRatio H z 0).re) :
    Tendsto (fun w : ℂ => pointHolomorphicSecantCorrection H z w) (𝓝 0)
      (𝓝 (pointHolomorphicSecantCorrection H z 0)) := by
  have hq : ContinuousAt (fun w : ℂ => pointHolomorphicSecantRatio H z w) 0 := by
    unfold pointHolomorphicSecantRatio
    apply (continuousAt_const.sub hc).div ((continuousAt_const.sub continuousAt_id).mul_const _)
    simpa only [Pi.sub_apply, id_eq, sub_zero] using mul_ne_zero hz hD
  exact (continuousAt_const.add ((Complex.continuousAt_arg (Or.inl hpos)).comp
    (f := fun w : ℂ => pointHolomorphicSecantRatio H z w) hq)).tendsto

/-- The zero-observer correction tends to arg H′(0) along every radial ray.
Thus differences of two endpoint corrections vanish as the cutoff shrinks. -/
theorem pointHolomorphicSecantCorrection_radial_limit {H : ℂ → ℂ}
    (hH : DifferentiableAt ℂ H 0) (hD : deriv H 0 ≠ 0) (A : ℝ) :
    Tendsto (fun r : ℝ => pointHolomorphicSecantCorrection H (pointRadialSectorPoint r A) 0)
      (𝓝[>] 0) (𝓝 (Complex.arg (deriv H 0))) := by
  let ψ : ℂ → ℝ := fun z => Complex.arg (deriv H 0) + Complex.arg (dslope H 0 z / deriv H 0)
  have hq : ContinuousAt (fun z : ℂ => dslope H 0 z / deriv H 0) 0 :=
    (continuousAt_dslope_same.mpr hH).div_const _
  have hq0 : dslope H 0 0 / deriv H 0 = 1 := by rw [dslope_same, div_self hD]
  have hψ : ContinuousAt ψ 0 := continuousAt_const.add
    ((Complex.continuousAt_arg (by rw [hq0]; simp)).comp
      (f := fun z : ℂ => dslope H 0 z / deriv H 0) hq)
  have hψ0 : ψ 0 = Complex.arg (deriv H 0) := by simp [ψ, hq0]
  have hpath : Tendsto (fun r : ℝ => pointRadialSectorPoint r A) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => pointRadialSectorPoint r A) := by
      unfold pointRadialSectorPoint
      fun_prop
    simpa only [pointRadialSectorPoint_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun r : ℝ => ψ (pointRadialSectorPoint r A)) (𝓝[>] 0)
      (𝓝 (Complex.arg (deriv H 0))) := by
    simpa only [hψ0, Function.comp_def] using hψ.tendsto.comp hpath
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : 0 < r := hr
  have hz : pointRadialSectorPoint r A ≠ 0 :=
    norm_pos_iff.mp (by rw [pointRadialSectorPoint_norm hr0.le]; exact hr0)
  unfold pointHolomorphicSecantCorrection ψ
  congr 1
  rw [dslope_of_ne H hz, slope_def_field]
  simp only [sub_zero, pointHolomorphicSecantRatio, div_div]

end RepulsiveCoulomb
