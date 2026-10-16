module

public import LeanResearch.RepulsiveCoulomb.PointRadialCollarVelocity
public import LeanResearch.RepulsiveCoulomb.PointRadialLoopBoundary
public import LeanResearch.RepulsiveCoulomb.PointRadialBoundaryAtom

@[expose] public section

/-! End-to-end boundary-atom argument accounting from the actual positively
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
theorem exists_positive_loop_radial_boundary_argument
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
    ∃ ψ : Icc (0 : ℝ) 1 → ℝ, Continuous ψ ∧
      (∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
        Complex.exp ((ψ t : ℂ) * Complex.I) = (γ t - γ 0) / (‖γ t - γ 0‖ : ℂ)) ∧
      ψ 1 - ψ 0 = θ := by
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
  obtain ⟨_, houtside⟩ := positive_inside_argument_selects_radial_chart_sector
    hγ hper hinj ha01 hadiff hareg hU hUc hV hVc hdisj hK hcover hw hΞ hΞlift hΞturn
    hpU hpV e hp hep hδ hθ0 hθ2 hδball hboundary' hasrc
    (he _ hasrc).differentiableAt hapos hra hraδ hcL havel
  let φ := (θ + 2 * Real.pi) / 2
  have hθφ : θ < φ := by dsimp [φ]; linarith
  have hφ2 : φ < 2 * Real.pi := by dsimp [φ]; linarith
  have hout : ∀ᶠ ε in 𝓝[>] (0 : ℝ), e.symm (pointRadialSectorPoint ε φ) ∈ V := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with ε hε hεδ
    exact houtside ⟨(ε, φ), ⟨⟨hε, hεδ⟩, ⟨hθφ, hφ2⟩⟩, rfl⟩
  have h0target : (0 : ℂ) ∈ e.target := hep ▸ e.mapsTo hp
  have hcoverΓ : U ∪ V = (range Γ)ᶜ := by rwa [hΓimage]
  obtain ⟨ψ, hψ, hψlift, hψturn⟩ := exists_radial_corner_boundary_argument
    e.open_target h0target hinv hinvn hθ0 hθφ hφ2 Γ hΓ hΓclose hΓinj
    hK hV hVc hcoverΓ hout hl hlr hr hcL hcR hΓleft hΓright
  have he0 : e.symm (0 : ℂ) = γ 0 := by rw [← hep, e.left_inv hp]
  exact ⟨ψ, hψ, by simpa only [Γ, he0] using hψlift, hψturn⟩

end RepulsiveCoulomb
