import LeanResearch.RepulsiveCoulomb.JordanFiniteCornerPositiveBoundaryAtom

/-! A source-retaining geometric interface for a selected corner of an
actual finite family. Only literal cyclic re-enumeration, partial charts and
original radial collars are stored. The boundary argument value is derived
by the positive-winding theorem; it is not a field of this structure. -/
noncomputable section
open Set Metric
open scoped BigOperators
namespace RepulsiveCoulomb

structure PointFiniteRadialCornerAt (f : ℕ → ℝ → ℂ) (n k : ℕ) (θ : ℝ) where
  order : ℕ → ℕ
  order_le : ∀ i ≤ n, order i ≤ n
  order_injective : ∀ i ≤ n, ∀ j ≤ n, order i = order j → i = j
  order_surjective : ∀ j ≤ n, ∃ i ≤ n, order i = j
  order_zero : order 0 = k
  consecutive : ∀ i < n, f (order i) 1 = f (order (i + 1)) 0
  closing : f (order n) 1 = f (order 0) 0
  chart : OpenPartialHomeomorph ℂ ℂ
  source : f k 0 ∈ chart.source
  origin : chart (f k 0) = 0
  forward_analytic : ∀ z ∈ chart.source, AnalyticAt ℂ chart z
  inverse_analytic : AnalyticOnNhd ℂ chart.symm chart.target
  inverse_regular : deriv chart.symm 0 ≠ 0
  width : ℝ
  width_pos : 0 < width
  width_half : width < 1 / 2
  leftRate : ℝ
  rightRate : ℝ
  leftRate_pos : 0 < leftRate
  rightRate_pos : 0 < rightRate
  radius : ℝ
  radius_pos : 0 < radius
  angle_pos : 0 < θ
  angle_lt : θ < 2 * Real.pi
  target_ball : ball (0 : ℂ) radius ⊆ chart.target
  left_radius : leftRate * width < radius
  right_radius : rightRate * width < radius
  left_collar : ∀ t ∈ Icc (0 : ℝ) 1, t ≤ width →
    f k t = chart.symm (pointRadialSectorPoint (leftRate * t) 0)
  right_collar : ∀ t ∈ Icc (0 : ℝ) 1, 1 - width ≤ t →
    f (order n) t = chart.symm (pointRadialSectorPoint (rightRate * (1 - t)) θ)

theorem finite_range_reenumeration_sum (n : ℕ) (q : ℕ → ℕ)
    (hq : ∀ i ≤ n, q i ≤ n)
    (hi : ∀ i ≤ n, ∀ j ≤ n, q i = q j → i = j)
    (hs : ∀ j ≤ n, ∃ i ≤ n, q i = j) (g : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1), g (q i)) = ∑ i ∈ Finset.range (n + 1), g i := by
  classical
  apply Finset.sum_bij (fun i _ => q i)
  · intro i hi
    exact Finset.mem_range.mpr (by have h := hq i (by have := Finset.mem_range.mp hi; omega); omega)
  · intro i hi' j hj' hij
    exact hi i (by have := Finset.mem_range.mp hi'; omega) j
      (by have := Finset.mem_range.mp hj'; omega) hij
  · intro j hj
    obtain ⟨i, hi, hij⟩ := hs j (by have := Finset.mem_range.mp hj; omega)
    exact ⟨i, Finset.mem_range.mpr (by omega), hij⟩
  · intro _ _
    rfl

/-- The genuine local geometry of one corner determines its actual finite
point sum. Cyclic re-enumeration, original carrier and positive witness are
all transported explicitly before applying the boundary-atom theorem. -/
theorem PointFiniteRadialCornerAt.point_sum
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
    (ψ : ℕ → Icc (0 : ℝ) 1 → ℝ) (hψ : ∀ i ≤ n, Continuous (ψ i))
    (hψlift : ∀ i ≤ n, ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((ψ i t : ℂ) * Complex.I) = (f i t - f k 0) / (‖f i t - f k 0‖ : ℂ)) :
    (∑ i ∈ Finset.range (n + 1), (ψ i 1 - ψ i 0)) = θ := by
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
  have hvalue := finite_corner_positive_radial_boundary_point_sum g n hgc D.consecutive D.closing hgi
    hU hUc hV hVc hdisj hK (by rwa [hcarrier]) (by rwa [hzero]) (by rwa [hzero]) hw
    (fun i => Ξ (D.order i)) (fun i hi => hΞ _ (D.order_le i hi))
    (fun i hi => hΞlift _ (D.order_le i hi)) hξturn D.chart
    (by simpa only [hzero] using D.source) (by simpa only [hzero] using D.origin) D.forward_analytic D.inverse_analytic D.inverse_regular
    D.width_pos D.width_half D.leftRate_pos D.rightRate_pos D.radius_pos D.angle_pos D.angle_lt
    D.target_ball D.left_radius D.right_radius
    (by intro s hs hsw; simpa only [g, D.order_zero] using D.left_collar s hs hsw)
    D.right_collar (fun i => ψ (D.order i)) (fun i hi => hψ _ (D.order_le i hi))
    (by intro i hi t ht; simpa only [g, D.order_zero] using hψlift _ (D.order_le i hi) t ht)
  exact (hsum (fun i => ψ i 1 - ψ i 0)).symm.trans hvalue

end RepulsiveCoulomb
