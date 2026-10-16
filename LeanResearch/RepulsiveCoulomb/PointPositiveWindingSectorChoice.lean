import LeanResearch.RepulsiveCoulomb.PointHolomorphicNormalSector
import LeanResearch.RepulsiveCoulomb.PointPositiveWindingNormalAt

/-! The actual positive inside argument orientation selects the inside
polar sector. The alternative local Jordan side assignment is contradicted
by an actual small physical left normal, mapped to positive chart argument. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem pointRadialChart_side_choice_of_actual_left_normal
    {C U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) (hd : Disjoint U V)
    (hcover : U ∪ V = Cᶜ) {p : ℂ} (hpU : p ∈ closure U) (hpV : p ∈ closure V)
    (e : OpenPartialHomeomorph ℂ ℂ) (hp : p ∈ e.source) (hep : e p = 0)
    {R θ : ℝ} (hR : 0 < R) (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi)
    (hball : ball (0 : ℂ) R ⊆ e.target)
    (hboundary : ∀ z ∈ ball (0 : ℂ) R,
      e.symm z ∈ C ↔ z ∈ pointDiskRay R 0 ∪ pointDiskRay R θ)
    {b d : ℂ} {r c : ℝ} (hb : b ∈ e.source) (hE : DifferentiableAt ℂ e b)
    (heb : e b = (r : ℂ)) (hr : 0 < r) (hrR : r < R)
    (hc : 0 < c) (hvelocity : deriv e b * d = (c : ℂ))
    (hnormal : ∀ᶠ ε in 𝓝[>] (0 : ℝ), b + ε • (Complex.I * d) ∈ U) :
    MapsTo e.symm (pointOpenRadialSector R 0 θ) U ∧
      MapsTo e.symm (pointOpenRadialSector R θ (2 * Real.pi)) V := by
  rcases pointRadialChart_region_side_choice hU hV hd hcover hpU hpV e hp hep
    hR hθ0 hθ2 hball hboundary with hside | hside
  · exact hside
  · have hsector := holomorphic_left_normal_eventually_in_radial_sector hE heb hr hrR hc hvelocity hθ0
    have hn : Continuous (fun ε : ℝ => b + ε • (Complex.I * d)) := by fun_prop
    have hnt : Tendsto (fun ε : ℝ => b + ε • (Complex.I * d)) (𝓝 0) (𝓝 b) := by
      simpa only [zero_smul, add_zero] using hn.tendsto 0
    have hsource : ∀ᶠ ε in 𝓝 (0 : ℝ), b + ε • (Complex.I * d) ∈ e.source :=
      hnt (e.open_source.mem_nhds hb)
    have hfalse : ∀ᶠ ε in 𝓝[>] (0 : ℝ), False := by
      filter_upwards [hsector, hnormal, mem_nhdsWithin_of_mem_nhds hsource] with ε hεS hεU hεsrc
      have hεV := hside.1 hεS
      rw [e.left_inv hεsrc] at hεV
      exact disjoint_left.mp hd hεU hεV
    obtain ⟨ε, hε⟩ := hfalse.exists
    exact hε.elim

/-- Global positive orientation is expressed by an actual inside argument
lift. Its constructed left-normal consequence, not a side certificate,
chooses the polar inside sector at the specified outgoing regular collar. -/
theorem positive_inside_argument_selects_radial_chart_sector
    {γ : ℝ → ℂ} (hγ : Continuous γ) (hper : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hdiff : DifferentiableAt ℝ γ a) (hreg : deriv γ a ≠ 0)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hd : Disjoint U V)
    (hK : IsCompact (closure U)) (hcover : U ∪ V = (γ '' Icc (0 : ℝ) 1)ᶜ)
    {w : ℂ} (hw : w ∈ U) {Ξ : Icc (0 : ℝ) 1 → ℝ} (hΞ : Continuous Ξ)
    (hΞlift : ∀ t, Complex.exp ((Ξ t : ℂ) * Complex.I) =
      (γ t - w) / (‖γ t - w‖ : ℂ)) (hΞturn : Ξ 1 - Ξ 0 = 2 * Real.pi)
    {p : ℂ} (hpU : p ∈ closure U) (hpV : p ∈ closure V)
    (e : OpenPartialHomeomorph ℂ ℂ) (hp : p ∈ e.source) (hep : e p = 0)
    {R θ : ℝ} (hR : 0 < R) (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi)
    (hball : ball (0 : ℂ) R ⊆ e.target)
    (hboundary : ∀ z ∈ ball (0 : ℂ) R,
      e.symm z ∈ γ '' Icc (0 : ℝ) 1 ↔ z ∈ pointDiskRay R 0 ∪ pointDiskRay R θ)
    {r c : ℝ} (hb : γ a ∈ e.source) (hE : DifferentiableAt ℂ e (γ a))
    (heb : e (γ a) = (r : ℂ)) (hr : 0 < r) (hrR : r < R)
    (hc : 0 < c) (hvelocity : deriv e (γ a) * deriv γ a = (c : ℂ)) :
    MapsTo e.symm (pointOpenRadialSector R 0 θ) U ∧
      MapsTo e.symm (pointOpenRadialSector R θ (2 * Real.pi)) V := by
  obtain ⟨δ, hδ, hnormals⟩ := positive_inside_argument_forces_left_normal_at
    hγ hper hinj ha hdiff hreg hU hUc hV hVc hK hcover hw hΞ hΞlift hΞturn
  have hnormal : ∀ᶠ ε in 𝓝[>] (0 : ℝ), γ a + ε • (Complex.I * deriv γ a) ∈ U := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with ε hε hεδ
    have h := (hnormals ε hε hεδ.le).1
    simpa only [Complex.real_smul, mul_assoc] using h
  exact pointRadialChart_side_choice_of_actual_left_normal hU hV hd hcover hpU hpV
    e hp hep hR hθ0 hθ2 hball hboundary hb hE heb hr hrR hc hvelocity hnormal

end RepulsiveCoulomb
