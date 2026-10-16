import LeanResearch.RepulsiveCoulomb.JordanFiniteCornerBoundaryPointSum
import LeanResearch.RepulsiveCoulomb.PointPositiveRadialBoundaryAtom

/-! An original finite family's actual positive inside point-angle sum selects
the actual boundary sector. The unshifted whole-loop inside lift and its +2π
increment are constructed from the family. The full boundary point sum then
follows from the actual normalized radial chart without an outside-observer
or local-boundary-equation hypothesis.
Future records-only successor; excluded from phase9periodic3. -/
noncomputable section
open Set Metric Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

/-- Construct the actual positive inside lift on the unshifted original loop
from any actual finite positive point-angle sum. Open-arc lift identities are
enough, including for endpoint-extended local angle conventions. -/
theorem exists_finite_corner_positive_periodic_point_argument
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    {w : ℂ} (hw : w ∉ ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1)
    (ξ : ℕ → Icc (0 : ℝ) 1 → ℝ) (hξ : ∀ k ≤ n, Continuous (ξ k))
    (hξlift : ∀ k ≤ n, ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((ξ k t : ℂ) * Complex.I) = (f k t - w) / (‖f k t - w‖ : ℂ))
    (hξturn : (∑ k ∈ Finset.range (n + 1), (ξ k 1 - ξ k 0)) = 2 * Real.pi) :
    ∃ Ξ : Icc (0 : ℝ) 1 → ℝ, Continuous Ξ ∧
      (∀ t, Complex.exp ((Ξ t : ℂ) * Complex.I) =
        (pointContinuousPeriodize (euclideanFiniteCornerArc f n) t - w) /
          (‖pointContinuousPeriodize (euclideanFiniteCornerArc f n) t - w‖ : ℂ)) ∧
      Ξ 1 - Ξ 0 = 2 * Real.pi := by
  let P := pointContinuousPeriodize (euclideanFiniteCornerArc f n)
  have hFc := euclideanFiniteCornerArc_closed f n hf hv hclose
  have hP : Continuous P := pointContinuousPeriodize_continuous
    (euclideanFiniteCornerArc_continuous f n hf hv).continuousOn hFc
  have hPF : EqOn P (euclideanFiniteCornerArc f n) (Icc (0 : ℝ) 1) :=
    fun _ ht => pointContinuousPeriodize_eq_Icc hFc ht
  have himage : P '' Icc (0 : ℝ) 1 = ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1 :=
    hPF.image_eq.trans (euclideanFiniteCornerArc_image f n hf hv)
  have havoid (t : Icc (0 : ℝ) 1) : P t - w ≠ 0 := by
    intro hz
    apply hw
    rw [← himage]
    exact ⟨t, t.2, sub_eq_zero.mp hz⟩
  obtain ⟨Ξ, hΞ, hΞlift⟩ := exists_interval_euclidean_angle_lift
    ((hP.comp continuous_subtype_val).sub continuous_const) havoid
  refine ⟨Ξ, hΞ, hΞlift, ?_⟩
  have hsum := finite_corner_punctured_point_increment_sum f n hf hv hclose w
    ξ Ξ hξ hΞ hξlift (fun t _ => hΞlift t)
  exact hsum.symm.trans hξturn

/-- The original finite boundary-point sum equals the full actual sector.
The positive orientation is supplied by an actual finite inside sum and the
exterior observers are then derived geometrically, rather than assumed. -/
theorem finite_corner_positive_radial_boundary_point_sum
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, Continuous (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      f i s = f j t → i = j ∧ s = t)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hdisj : Disjoint U V)
    (hK : IsCompact (closure U))
    (hcover : U ∪ V = (⋃ k ≤ n, f k '' Icc (0 : ℝ) 1)ᶜ)
    (hpU : f 0 0 ∈ closure U) (hpV : f 0 0 ∈ closure V)
    {w : ℂ} (hw : w ∈ U)
    (ξ : ℕ → Icc (0 : ℝ) 1 → ℝ) (hξ : ∀ k ≤ n, Continuous (ξ k))
    (hξlift : ∀ k ≤ n, ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((ξ k t : ℂ) * Complex.I) = (f k t - w) / (‖f k t - w‖ : ℂ))
    (hξturn : (∑ k ∈ Finset.range (n + 1), (ξ k 1 - ξ k 0)) = 2 * Real.pi)
    (e : OpenPartialHomeomorph ℂ ℂ) (hp : f 0 0 ∈ e.source) (hep : e (f 0 0) = 0)
    (he : ∀ z ∈ e.source, AnalyticAt ℂ e z)
    (hinv : AnalyticOnNhd ℂ e.symm e.target) (hinvn : deriv e.symm 0 ≠ 0)
    {δ cL cR R θ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hcL : 0 < cL) (hcR : 0 < cR) (hR : 0 < R)
    (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi)
    (hball : ball (0 : ℂ) R ⊆ e.target)
    (hLrad : cL * δ < R) (hRrad : cR * δ < R)
    (hleft : ∀ s ∈ Icc (0 : ℝ) 1, s ≤ δ →
      f 0 s = e.symm (pointRadialSectorPoint (cL * s) 0))
    (hright : ∀ s ∈ Icc (0 : ℝ) 1, 1 - δ ≤ s →
      f n s = e.symm (pointRadialSectorPoint (cR * (1 - s)) θ))
    (ψ : ℕ → Icc (0 : ℝ) 1 → ℝ) (hψ : ∀ k ≤ n, Continuous (ψ k))
    (hψlift : ∀ k ≤ n, ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((ψ k t : ℂ) * Complex.I) = (f k t - f 0 0) / (‖f k t - f 0 0‖ : ℂ)) :
    (∑ k ∈ Finset.range (n + 1), (ψ k 1 - ψ k 0)) = θ := by
  let P := pointContinuousPeriodize (euclideanFiniteCornerArc f n)
  obtain ⟨hP, hpP, hiP, hP0, himage⟩ := euclideanFiniteCornerPeriodize_properties f n hf hv hclose hinj
  have hbase : P 0 = f 0 0 := hP0
  have hcoverP : U ∪ V = (P '' Icc (0 : ℝ) 1)ᶜ := by rwa [himage]
  have hwC : w ∉ ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1 := by
    have hwUV : w ∈ U ∪ V := Or.inl hw
    rw [hcover] at hwUV
    exact hwUV
  obtain ⟨Ξ, hΞ, hΞlift, hΞturn⟩ := exists_finite_corner_positive_periodic_point_argument
    f n hf hv hclose hwC ξ hξ hξlift hξturn
  obtain ⟨hl, hlr, hr, hcL', hcR', hleft', hright'⟩ :=
    euclideanFiniteCornerPeriodize_radial_collars f n hf hv hclose e.symm θ hδ hδhalf
      hcL hcR hleft hright
  have hm : (n + 1 : ℝ) ≠ 0 := by positivity
  have hLrad' : ((n + 1 : ℝ) * cL) * (δ / (n + 1 : ℝ)) < R := by
    have heq : ((n + 1 : ℝ) * cL) * (δ / (n + 1 : ℝ)) = cL * δ := by
      field_simp [hm] <;> ring
    rw [heq]
    exact hLrad
  have hRrad' : ((n + 1 : ℝ) * cR) * (1 - (1 - δ / (n + 1 : ℝ))) < R := by
    have heq : ((n + 1 : ℝ) * cR) * (1 - (1 - δ / (n + 1 : ℝ))) = cR * δ := by
      field_simp [hm] <;> ring
    rw [heq]
    exact hRrad
  have hleftP : ∀ t ∈ Icc (0 : ℝ) (δ / (n + 1 : ℝ)),
      P t = e.symm (pointRadialSectorPoint (((n + 1 : ℝ) * cL) * t) 0) := by
    intro t ht
    exact hleft' ⟨t, ⟨ht.1, ht.2.trans (hlr.trans hr).le⟩⟩ ht.2
  have hrightP : ∀ t ∈ Icc (1 - δ / (n + 1 : ℝ)) (1 : ℝ),
      P t = e.symm (pointRadialSectorPoint (((n + 1 : ℝ) * cR) * (1 - t)) θ) := by
    intro t ht
    exact hright' ⟨t, ⟨(hl.trans hlr).le.trans ht.1, ht.2⟩⟩ ht.1
  obtain ⟨Ψ, hΨ, hΨlift, hΨturn⟩ := exists_positive_loop_radial_boundary_argument
    P hP hpP hiP hU hUc hV hVc hdisj hK hcoverP
    (by rwa [hbase]) (by rwa [hbase]) hw Ξ hΞ hΞlift hΞturn
    e (by rwa [hbase]) (by rwa [hbase]) he hinv hinvn hl hlr hr hcL' hcR' hR
    hθ0 hθ2 hball hLrad' hRrad' hleftP hrightP
  have hΨlift' : ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((Ψ t : ℂ) * Complex.I) = (P t - f 0 0) / (‖P t - f 0 0‖ : ℂ) := by
    intro t ht
    simpa only [hbase] using hΨlift t ht
  exact (finite_corner_punctured_point_increment_sum f n hf hv hclose (f 0 0)
    ψ Ψ hψ hΨ hψlift hΨlift').trans hΨturn

end RepulsiveCoulomb
