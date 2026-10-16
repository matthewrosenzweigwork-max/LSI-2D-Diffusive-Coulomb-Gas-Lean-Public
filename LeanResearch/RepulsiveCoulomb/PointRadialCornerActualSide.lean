import LeanResearch.RepulsiveCoulomb.PointFiniteRadialCornerGeometry
import LeanResearch.RepulsiveCoulomb.PointFiniteCornerFullSide
import LeanResearch.RepulsiveCoulomb.PointLineFullIntervalWidth

/-! Uncompiled records-only successor. At an actual positive radial vertex,
the full initial sector is proved to be the actual positive Jordan side. -/
noncomputable section
open Set Metric
open scoped BigOperators
namespace RepulsiveCoulomb

theorem PointFiniteRadialCornerAt.actual_full_inside_sector
    {f : ℕ → ℝ → ℂ} {n k : ℕ} {θ : ℝ} (D : PointFiniteRadialCornerAt f n k θ)
    (hf : ∀ i ≤ n, Continuous (f i))
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 → f i s = f j t → i = j ∧ s = t)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hdisj : Disjoint U V)
    (hK : IsCompact (closure U))
    (hcover : U ∪ V = (⋃ i ≤ n, f i '' Icc (0 : ℝ) 1)ᶜ)
    (hpU : f k 0 ∈ closure U) (hpV : f k 0 ∈ closure V)
    {w : ℂ} (hw : w ∈ U) (Ξ : ℕ → Icc (0 : ℝ) 1 → ℝ)
    (hΞ : ∀ i ≤ n, Continuous (Ξ i))
    (hΞlift : ∀ i ≤ n, ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((Ξ i t : ℂ) * Complex.I) = (f i t - w) / (‖f i t - w‖ : ℂ))
    (hΞturn : (∑ i ∈ Finset.range (n + 1), (Ξ i 1 - Ξ i 0)) = 2 * Real.pi)
    : ∃ δ : ℝ, 0 < δ ∧ ball (0 : ℂ) δ ⊆ D.chart.target ∧
      (∀ z ∈ ball (0 : ℂ) δ,
        D.chart.symm z ∈ (⋃ i ≤ n, f i '' Icc (0 : ℝ) 1) ↔
          z ∈ pointDiskRay δ 0 ∪ pointDiskRay δ θ) ∧
      MapsTo D.chart.symm (pointOpenRadialSector δ 0 θ) U ∧
      MapsTo D.chart.symm (pointOpenRadialSector δ θ (2 * Real.pi)) V := by
  let g : ℕ → ℝ → ℂ := fun i => f (D.order i)
  have hgc : ∀ i ≤ n, Continuous (g i) := fun i hi => hf _ (D.order_le i hi)
  have hgi : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 → g i s = g j t → i = j ∧ s = t := by
    intro i j hi hj s t hs ht heq
    obtain ⟨hij, hst⟩ := hinj _ _ (D.order_le i hi) (D.order_le j hj) s t hs ht heq
    exact ⟨D.order_injective i hi j hj hij, hst⟩
  have hcarrier : (⋃ i ≤ n, g i '' Icc (0 : ℝ) 1) = ⋃ i ≤ n, f i '' Icc (0 : ℝ) 1 := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hz⟩ := mem_iUnion.mp hz
      obtain ⟨hi, hz⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨D.order i, mem_iUnion.mpr ⟨D.order_le i hi, hz⟩⟩
    · intro hz
      obtain ⟨j, hz⟩ := mem_iUnion.mp hz
      obtain ⟨hj, hz⟩ := mem_iUnion.mp hz
      obtain ⟨i, hi, hij⟩ := D.order_surjective j hj
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, by simpa only [g, hij] using hz⟩⟩
  have hsum (F : ℕ → ℝ) := finite_range_reenumeration_sum n D.order D.order_le
    D.order_injective D.order_surjective F
  have hzero : g 0 0 = f k 0 := by simp only [g, D.order_zero]
  have hξturn : (∑ i ∈ Finset.range (n + 1), (Ξ (D.order i) 1 - Ξ (D.order i) 0)) =
      2 * Real.pi := (hsum (fun i => Ξ i 1 - Ξ i 0)).trans hΞturn
  obtain ⟨δ, hδ, hball, hboundary, hinside, houtside⟩ := exists_finite_corner_positive_full_radial_side g n hgc D.consecutive D.closing hgi
    hU hUc hV hVc hdisj hK (by rwa [hcarrier]) (by rwa [hzero]) (by rwa [hzero]) hw
    (fun i => Ξ (D.order i)) (fun i hi => hΞ _ (D.order_le i hi))
    (fun i hi => hΞlift _ (D.order_le i hi)) hξturn D.chart
    (by simpa only [hzero] using D.source) (by simpa only [hzero] using D.origin) D.forward_analytic D.inverse_analytic D.inverse_regular
    D.width_pos D.width_half D.leftRate_pos D.rightRate_pos D.radius_pos D.angle_pos D.angle_lt
    D.target_ball D.left_radius D.right_radius
    (by intro s hs hsw; simpa only [g, D.order_zero] using D.left_collar s hs hsw)
    D.right_collar
  exact ⟨δ, hδ, hball, by simpa only [hcarrier] using hboundary, hinside, houtside⟩

end RepulsiveCoulomb
