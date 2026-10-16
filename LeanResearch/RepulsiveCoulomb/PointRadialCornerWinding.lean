import LeanResearch.RepulsiveCoulomb.PointRadialBoundaryArgument

/-! The full boundary-point argument is the actual interior sector angle.
The outside observer is geometrically specified, both original radial collars
are retained, and the cutoff is sent to the vertex. Reflex angles are not
replaced by principal arguments. This is the boundary-atom input to the full
cone Gauss–Bonnet formula, independently of whether the edges are geodesic. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- An actual positively oriented two-ray corner has boundary-point argument
increment equal to its full inside sector angle. The only orientation input
is that the constructed observers in the complementary sector lie outside. -/
theorem radial_corner_boundary_argument_eq_sector
    {W : Set ℂ} (hW : IsOpen W) (hW0 : (0 : ℂ) ∈ W)
    {H : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H W) (hD : deriv H 0 ≠ 0)
    {θ φ : ℝ} (hθ : 0 < θ) (hθφ : θ < φ) (hφ2 : φ < 2 * Real.pi)
    (γ : Icc (0 : ℝ) 1 → ℂ) (hγ : Continuous γ) (hclose : γ 0 = γ 1)
    (hinj : InjOn γ {t : Icc (0 : ℝ) 1 | t.1 < 1})
    {U V : Set ℂ} (hK : IsCompact (closure U)) (hV : IsOpen V) (hVc : IsConnected V)
    (hcover : U ∪ V = (range γ)ᶜ)
    (hout : ∀ᶠ ε in 𝓝[>] (0 : ℝ), H (pointRadialSectorPoint ε φ) ∈ V)
    {l r cL cR : ℝ} (hl : 0 < l) (hlr : l < r) (hr : r < 1)
    (hcL : 0 < cL) (hcR : 0 < cR)
    (hleft : ∀ t : Icc (0 : ℝ) 1, t.1 ≤ l →
      γ t = H (pointRadialSectorPoint (cL * t.1) 0))
    (hright : ∀ t : Icc (0 : ℝ) 1, r ≤ t.1 →
      γ t = H (pointRadialSectorPoint (cR * (1 - t.1)) θ))
    (ψ : Icc (0 : ℝ) 1 → ℝ) (hψ : Continuous ψ)
    (hψlift : ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((ψ t : ℂ) * Complex.I) = (γ t - H 0) / (‖γ t - H 0‖ : ℂ)) :
    ψ 1 - ψ 0 = θ := by
  obtain ⟨Rc, hRc, _, hformula⟩ :=
    exists_radial_boundary_remaining_argument_formula hW hW0 hH hD
  let R := min Rc (min (cL * l) (cR * (1 - r)))
  have hR : 0 < R := lt_min hRc (lt_min (mul_pos hcL hl) (mul_pos hcR (sub_pos.mpr hr)))
  have hγ0 : γ 0 = H 0 := by
    simpa [pointRadialSectorPoint] using
      hleft 0 (show (0 : ℝ) ≤ l from hl.le)
  have havoid (t : Icc (0 : ℝ) 1) (ht : t.1 ∈ Ioo (0 : ℝ) 1) : γ t ≠ H 0 := by
    intro heq
    have he : t = 0 := hinj ht.2 (by norm_num) (heq.trans hγ0.symm)
    have hv := congrArg Subtype.val he
    exact ht.1.ne' hv
  let Ψ : ℝ → ℝ := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) ψ
  have hΨ : Continuous Ψ := continuous_IccExtend_iff.mpr hψ
  have hbalance : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      Ψ (1 - ρ / cR) - Ψ (ρ / cL) =
        -(-θ + (pointHolomorphicSecantCorrection H (pointRadialSectorPoint ρ 0) 0 -
          pointHolomorphicSecantCorrection H (pointRadialSectorPoint ρ θ) 0)) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hR)] with ρ hρ hρR
    have hρpos : 0 < ρ := hρ
    have hρRc : ρ < Rc := hρR.trans_le (min_le_left _ _)
    have hρL : ρ < cL * l := hρR.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hρR' : ρ < cR * (1 - r) :=
      hρR.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    let uL := ρ / cL
    let uR := 1 - ρ / cR
    have huL0 : 0 < uL := div_pos hρpos hcL
    have huLl : uL < l := (div_lt_iff₀ hcL).mpr (by simpa only [mul_comm] using hρL)
    have hrRu : r < uR := by
      have hd : ρ / cR < 1 - r := (div_lt_iff₀ hcR).mpr (by simpa only [mul_comm] using hρR')
      dsimp [uR]
      linarith
    have huR1 : uR < 1 := by dsimp [uR]; linarith [div_pos hρpos hcR]
    have huLR : uL < uR := huLl.trans (hlr.trans hrRu)
    have huL1 : uL < 1 := huLR.trans huR1
    have huR0 : 0 < uR := huL0.trans huLR
    let βL : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun t =>
      ⟨uL * t.1, ⟨mul_nonneg huL0.le t.2.1, by nlinarith [t.2.2]⟩⟩
    let βM : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun t =>
      ⟨uL + t.1 * (uR - uL), by
        have hlo := mul_nonneg t.2.1 (sub_nonneg.mpr huLR.le)
        have hhi := mul_le_mul_of_nonneg_right t.2.2 (sub_nonneg.mpr huLR.le)
        constructor <;> linarith⟩
    let βR : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun t =>
      ⟨1 - (ρ / cR) * (1 - t.1), by
        have hq : 0 < ρ / cR := div_pos hρpos hcR
        have hq1 : ρ / cR < 1 := by dsimp [uR] at huR0; linarith
        constructor <;> nlinarith [t.2.1, t.2.2]⟩
    have hcβL : Continuous βL := (continuous_const.mul continuous_subtype_val).subtype_mk _
    have hcβM : Continuous βM :=
      (continuous_const.add (continuous_subtype_val.mul continuous_const)).subtype_mk _
    have hcβR : Continuous βR :=
      (continuous_const.sub (continuous_const.mul
        (continuous_const.sub continuous_subtype_val))).subtype_mk _
    have hβstart : βL 0 = 0 := by apply Subtype.ext; simp [βL]
    have hβLM : βL 1 = βM 0 := by apply Subtype.ext; simp [βL, βM]
    have hβMR : βM 1 = βR 0 := by apply Subtype.ext; dsimp [βM, βR, uR]; ring
    have hβfinish : βR 1 = 1 := by apply Subtype.ext; simp [βR]
    have hβLbound (t : Icc (0 : ℝ) 1) : (βL t).1 ≤ l := by
      dsimp [βL]
      have hle := mul_le_mul_of_nonneg_left t.2.2 huL0.le
      linarith
    have hβRbound (t : Icc (0 : ℝ) 1) : r ≤ (βR t).1 := by
      dsimp [βR]
      have hq : 0 < ρ / cR := div_pos hρpos hcR
      dsimp [uR] at hrRu
      nlinarith [t.2.1]
    have hβMinside (t : Icc (0 : ℝ) 1) : (βM t).1 ∈ Ioo (0 : ℝ) 1 := by
      dsimp [βM]
      have hlo := mul_nonneg t.2.1 (sub_nonneg.mpr huLR.le)
      have hhi := mul_le_mul_of_nonneg_right t.2.2 (sub_nonneg.mpr huLR.le)
      constructor <;> linarith
    have hL (t : Icc (0 : ℝ) 1) :
        γ (βL t) = H (pointRadialSectorPoint (ρ * t.1) 0) := by
      have hradius : cL * (βL t).1 = ρ * t.1 := by
        dsimp [βL, uL]
        field_simp [hcL.ne'] <;> ring
      simpa only [hradius] using hleft (βL t) (hβLbound t)
    have hR' (t : Icc (0 : ℝ) 1) :
        γ (βR t) = H (pointRadialSectorPoint (ρ * (1 - t.1)) θ) := by
      have hradius : cR * (1 - (βR t).1) = ρ * (1 - t.1) := by
        dsimp [βR]
        field_simp [hcR.ne'] <;> ring
      simpa only [hradius] using hright (βR t) (hβRbound t)
    have hturn := hformula ρ θ φ hρpos hρRc hθ hθφ hφ2 γ hγ hclose U V hK hV hVc
      hcover hout βL βM βR hcβL hcβM hcβR hβstart hβLM hβMR hβfinish hL hR'
      (fun t => havoid (βM t) (hβMinside t)) (ψ ∘ βM) (hψ.comp hcβM)
      (fun t => hψlift (βM t) (hβMinside t))
    have hΨL : Ψ (ρ / cL) = ψ (βM 0) := by
      dsimp [Ψ]
      rw [IccExtend_of_mem _ _ ⟨huL0.le, huL1.le⟩]
      congr 1
      apply Subtype.ext
      simp [βM, uL]
    have hΨR : Ψ (1 - ρ / cR) = ψ (βM 1) := by
      dsimp [Ψ]
      rw [IccExtend_of_mem _ _ ⟨huR0.le, huR1.le⟩]
      congr 1
      apply Subtype.ext
      dsimp [βM, uR]
      ring
    rw [hΨL, hΨR]
    dsimp [Function.comp_def] at hturn
    linarith
  have hLlim : Tendsto (fun ρ : ℝ => ρ / cL) (𝓝 0) (𝓝 0) := by
    have h : Continuous (fun ρ : ℝ => ρ / cL) := by fun_prop
    simpa only [zero_div] using h.tendsto 0
  have hRlim : Tendsto (fun ρ : ℝ => 1 - ρ / cR) (𝓝 0) (𝓝 1) := by
    have h : Continuous (fun ρ : ℝ => 1 - ρ / cR) := by fun_prop
    simpa only [zero_div, sub_zero] using h.tendsto 0
  have harglim := ((hΨ.tendsto 1).comp hRlim).sub ((hΨ.tendsto 0).comp hLlim)
  have hsectorlim := (holomorphic_exterior_two_ray_cutoff_limit
    (hH 0 hW0).differentiableAt hD θ).neg
  have hbalance' : (fun ρ => Ψ (1 - ρ / cR) - Ψ (ρ / cL)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ρ => -(-θ +
        (pointHolomorphicSecantCorrection H (pointRadialSectorPoint ρ 0) 0 -
          pointHolomorphicSecantCorrection H (pointRadialSectorPoint ρ θ) 0))) := hbalance
  have heq := tendsto_nhds_unique (harglim.mono_left nhdsWithin_le_nhds)
    (hsectorlim.congr' hbalance'.symm)
  simpa [Ψ, IccExtend] using heq

end RepulsiveCoulomb
