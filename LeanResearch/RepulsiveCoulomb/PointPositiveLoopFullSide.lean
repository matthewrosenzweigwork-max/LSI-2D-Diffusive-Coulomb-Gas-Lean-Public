import LeanResearch.RepulsiveCoulomb.PointRadialCollarVelocity
import LeanResearch.RepulsiveCoulomb.PointRadialLoopBoundary
import LeanResearch.RepulsiveCoulomb.PointRadialBoundaryAtom

/-! Uncompiled records-only accessor. Actual full boundary-sector membership
is retained as the output, including reflex sectors. End-to-end boundary-atom accounting from the actual positively
oriented simple loop. The local whole-boundary equation, regular outgoing
velocity, correct Jordan sector, exterior observers and actual argument lift
are all constructed. Only the original normalized radial collars and an
actual positive inside winding witness are supplied. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- The full boundary angle is determined by actual positive orientation,
without an exterior-observer or two-ray-boundary certificate in the input. -/
theorem exists_positive_loop_full_radial_side
    (γ : ℝ → ℂ) (hγ : Continuous γ) (hper : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1))
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hdisj : Disjoint U V)
    (hK : IsCompact (closure U))
    (hcover : U ∪ V = (γ '' Icc (0 : ℝ) 1)ᶜ)
    (hpU : γ 0 ∈ closure U) (hpV : γ 0 ∈ closure V)
    {w : ℂ} (hw : w ∈ U) (Ξ : Icc (0 : ℝ) 1 → ℝ) (hΞ : Continuous Ξ)
    (hΞlift : ∀ t, Complex.exp ((Ξ t : ℂ) * Complex.I) =
      (γ t - w) / (‖γ t - w‖ : ℂ)) (hΞturn : Ξ 1 - Ξ 0 = 2 * Real.pi)
    (e : OpenPartialHomeomorph ℂ ℂ) (hp : γ 0 ∈ e.source) (hep : e (γ 0) = 0)
    (he : ∀ z ∈ e.source, AnalyticAt ℂ e z)
    (hinv : AnalyticOnNhd ℂ e.symm e.target) (hinvn : deriv e.symm 0 ≠ 0)
    {l r cL cR R θ : ℝ} (hl : 0 < l) (hlr : l < r) (hr : r < 1)
    (hcL : 0 < cL) (hcR : 0 < cR) (hR : 0 < R)
    (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi)
    (hball : ball (0 : ℂ) R ⊆ e.target)
    (hLrad : cL * l < R) (hRrad : cR * (1 - r) < R)
    (hleft : ∀ t ∈ Icc (0 : ℝ) l,
      γ t = e.symm (pointRadialSectorPoint (cL * t) 0))
    (hright : ∀ t ∈ Icc r 1,
      γ t = e.symm (pointRadialSectorPoint (cR * (1 - t)) θ)) :
    ∃ δ : ℝ, 0 < δ ∧ ball (0 : ℂ) δ ⊆ e.target ∧
      (∀ z ∈ ball (0 : ℂ) δ,
        e.symm z ∈ γ '' Icc (0 : ℝ) 1 ↔ z ∈ pointDiskRay δ 0 ∪ pointDiskRay δ θ) ∧
      MapsTo e.symm (pointOpenRadialSector δ 0 θ) U ∧
      MapsTo e.symm (pointOpenRadialSector δ θ (2 * Real.pi)) V := by
  let Γ : Icc (0 : ℝ) 1 → ℂ := fun t => γ t
  have hΓ : Continuous Γ := hγ.comp continuous_subtype_val
  have hΓclose : Γ 0 = Γ 1 := by simpa [Γ] using (hper 0).symm
  have hΓinj : InjOn Γ {t : Icc (0 : ℝ) 1 | t.1 < 1} := by
    intro s hs t ht heq
    exact Subtype.ext (hinj ⟨s.2.1, hs⟩ ⟨t.2.1, ht⟩ heq)
  have hΓimage : range Γ = γ '' Icc (0 : ℝ) 1 := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  have hΓleft (t : Icc (0 : ℝ) 1) (ht : t.1 ≤ l) :
      Γ t = e.symm (pointRadialSectorPoint (cL * t.1) 0) :=
    hleft t ⟨t.2.1, ht⟩
  have hΓright (t : Icc (0 : ℝ) 1) (ht : r ≤ t.1) :
      Γ t = e.symm (pointRadialSectorPoint (cR * (1 - t.1)) θ) :=
    hright t ⟨ht, t.2.2⟩
  obtain ⟨δ, hδ, hδball, hboundary⟩ := exists_simple_loop_exact_radial_boundary
    Γ hΓ hΓinj e hp hep rfl hl hlr hr hcL hcR hR hball hLrad hRrad hΓleft hΓright
  have hboundary' : ∀ z ∈ ball (0 : ℂ) δ,
      e.symm z ∈ γ '' Icc (0 : ℝ) 1 ↔ z ∈ pointDiskRay δ 0 ∪ pointDiskRay δ θ := by
    intro z hz
    simpa only [hΓimage] using hboundary z hz
  obtain ⟨a, ra, ha, ha01, hra, hraδ, hasrc, hapos, hadiff, hareg, havel⟩ :=
    exists_outgoing_radial_collar_positive_velocity γ e he hinv hl (hlr.trans hr)
      hcL hδ hδball hleft
  obtain ⟨hinside, houtside⟩ := positive_inside_argument_selects_radial_chart_sector
    hγ hper hinj ha01 hadiff hareg hU hUc hV hVc hdisj hK hcover hw hΞ hΞlift hΞturn
    hpU hpV e hp hep hδ hθ0 hθ2 hδball hboundary' hasrc
    (he _ hasrc).differentiableAt hapos hra hraδ hcL havel
  exact ⟨δ, hδ, hδball, hboundary', hinside, houtside⟩

end RepulsiveCoulomb
