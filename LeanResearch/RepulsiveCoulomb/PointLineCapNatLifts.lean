import LeanResearch.RepulsiveCoulomb.PointLineCapNatGerms
import LeanResearch.RepulsiveCoulomb.PointLineCapNatWinding
import LeanResearch.RepulsiveCoulomb.PointCircleCapCovariantTurn
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order
import Mathlib.Tactic.NormNum

/-! Records-only, uncompiled. Actual tangent and atom lifts for the nat-indexed
cap, with zero geodesic covariant turn on each retained radial piece. Actual
observer lifts and their positive total winding are constructed separately.
No flux value, chosen angle, or winding identity is an input. -/
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators
namespace RepulsiveCoulomb

/-- All finite edge lifts are constructed. Their geodesic covariant increments
vanish at the original line pieces; the circle is left as its actual curved
edge rather than being assigned zero curvature. -/
theorem exists_lineCap_nat_tangent_atom_lifts
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {p q : ℂ} (hpq : p ≠ q) (γ : Icc (0 : ℝ) 1 → ℂ)
    (h0 : γ ⟨0, by norm_num⟩ = p)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal)
    (es : List (PointRadialC1ArcPiece ha y γ)) (f : ℕ → ℝ → ℂ)
    (hpieces : ∀ k (hk : k < es.length), f k = (es.get ⟨k, hk⟩).curve)
    {R α β : ℝ} (hR : 0 < R) (hab : α < β) (hy : ∀ j, ‖y j‖ < R)
    (hcircle : f es.length = pointCircleCapArc R α β) :
    ∃ τ : ℕ → Icc (0 : ℝ) 1 → ℝ, ∃ ψ : Fin m → ℕ → Icc (0 : ℝ) 1 → ℝ,
      (∀ k ≤ es.length, Continuous (τ k)) ∧
      (∀ j k, k ≤ es.length → Continuous (ψ j k)) ∧
      (∀ k ≤ es.length, ∀ t, Complex.exp ((τ k t : ℂ) * Complex.I) =
        deriv (f k) t / (‖deriv (f k) t‖ : ℂ)) ∧
      (∀ j, a j ≠ 0 → ∀ k ≤ es.length, ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
        Complex.exp ((ψ j k t : ℂ) * Complex.I) =
          (f k t - y j) / (‖f k t - y j‖ : ℂ)) ∧
      ∀ k < es.length, (τ k 1 - τ k 0) + ∑ j, (a j / 2) * (ψ j k 1 - ψ j k 0) = 0 := by
  let τC : Icc (0 : ℝ) 1 → ℝ := fun t => α + (β - α) * t.1 + Real.pi / 2
  have hτC : Continuous τC := by fun_prop
  have hτCl (t : Icc (0 : ℝ) 1) : Complex.exp ((τC t : ℂ) * Complex.I) =
      deriv (pointCircleCapArc R α β) t / (‖deriv (pointCircleCapArc R α β) t‖ : ℂ) :=
    pointCircleCapArc_tangent_lift hR hab t
  have hψC (j : Fin m) : ∃ ψ : Icc (0 : ℝ) 1 → ℝ, Continuous ψ ∧
      ∀ t, Complex.exp ((ψ t : ℂ) * Complex.I) =
        (pointCircleCapArc R α β t - y j) / (‖pointCircleCapArc R α β t - y j‖ : ℂ) := by
    apply exists_interval_euclidean_angle_lift
      (((pointCircleCapArc_smooth R α β).continuous.comp continuous_subtype_val).sub continuous_const)
    intro t he
    change pointCircleCapArc R α β t - y j = 0 at he
    have hnorm : ‖y j‖ = R := by
      rw [← sub_eq_zero.mp he]
      exact pointCircleCapArc_norm hR.le α β t
    exact (hy j).ne hnorm
  choose ψC hψC hψCl using hψC
  have hdata (k : ℕ) :
      ∃ τ : Icc (0 : ℝ) 1 → ℝ, ∃ ψ : Fin m → Icc (0 : ℝ) 1 → ℝ,
        Continuous τ ∧ (∀ j, Continuous (ψ j)) ∧
        (k ≤ es.length → ∀ t, Complex.exp ((τ t : ℂ) * Complex.I) =
          deriv (f k) t / (‖deriv (f k) t‖ : ℂ)) ∧
        (k ≤ es.length → ∀ j, a j ≠ 0 → ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
          Complex.exp ((ψ j t : ℂ) * Complex.I) = (f k t - y j) / (‖f k t - y j‖ : ℂ)) ∧
        (k < es.length → (τ 1 - τ 0) + ∑ j, (a j / 2) * (ψ j 1 - ψ j 0) = 0) := by
    by_cases hk : k < es.length
    · obtain ⟨τ, ψ, hτ, hψ, hτl, hψl, hturn⟩ :=
        (es.get ⟨k, hk⟩).exists_argument_turn hpq h0 hd
      refine ⟨τ, ψ, hτ, hψ, ?_, ?_, fun _ => by linarith⟩
      · intro _ t
        simpa only [hpieces k hk] using hτl t
      · intro _ j hj t ht
        simpa only [hpieces k hk] using hψl j hj t ht
    · refine ⟨τC, ψC, hτC, hψC, ?_, ?_, fun h => False.elim (hk h)⟩
      · intro hkn t
        have hke : k = es.length := by omega
        simpa only [hke, hcircle] using hτCl t
      · intro hkn j _ t _
        have hke : k = es.length := by omega
        simpa only [hke, hcircle] using hψCl j t
  choose τ Ψ hτ hΨ hτl hΨl hzero using hdata
  exact ⟨τ, fun j k => Ψ k j, fun k _ => hτ k, fun j k _ => hΨ k j,
    hτl, fun j hj k hk t ht => hΨl k hk j hj t ht, hzero⟩

/-- A genuine inside observer and its finite continuous point lifts are
constructed, and the sign is fixed by the circle normal, not supplied. -/
theorem exists_lineCap_nat_positive_observer_lifts
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hf : ∀ k ≤ n, ContDiff ℝ 1 (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 → f i s = f j t → i = j ∧ s = t)
    {R α β : ℝ} (hR : 0 < R) (hab : α < β)
    (hcircle : f n = pointCircleCapArc R α β)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hK : IsCompact (closure U))
    (hcover : U ∪ V = (⋃ k ≤ n, f k '' Icc (0 : ℝ) 1)ᶜ)
    (hball : U ⊆ ball (0 : ℂ) R) :
    ∃ w ∈ U, ∃ Ξ : ℕ → Icc (0 : ℝ) 1 → ℝ,
      (∀ k ≤ n, Continuous (Ξ k)) ∧
      (∀ k ≤ n, ∀ t, Complex.exp ((Ξ k t : ℂ) * Complex.I) =
        (f k t - w) / (‖f k t - w‖ : ℂ)) ∧
      (∑ k ∈ Finset.range (n + 1), (Ξ k 1 - Ξ k 0)) = 2 * Real.pi := by
  obtain ⟨w, hw⟩ := hUc.nonempty
  have hwC : w ∉ ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1 := by
    have hwUV : w ∈ U ∪ V := Or.inl hw
    rw [hcover] at hwUV
    exact hwUV
  have hdata (k : ℕ) : ∃ Ξ : Icc (0 : ℝ) 1 → ℝ, Continuous Ξ ∧
      (k ≤ n → ∀ t, Complex.exp ((Ξ t : ℂ) * Complex.I) =
        (f k t - w) / (‖f k t - w‖ : ℂ)) := by
    by_cases hk : k ≤ n
    · obtain ⟨Ξ, hΞ, hΞl⟩ := exists_interval_euclidean_angle_lift
        (((hf k hk).continuous.comp continuous_subtype_val).sub continuous_const)
        (fun t he => hwC (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk,
          ⟨t, t.2, sub_eq_zero.mp he⟩⟩⟩))
      exact ⟨Ξ, hΞ, fun _ => hΞl⟩
    · exact ⟨fun _ => 0, continuous_const, fun h => False.elim (hk h)⟩
  choose Ξ hΞ hΞl using hdata
  exact ⟨w, hw, Ξ, fun k _ => hΞ k, hΞl,
    lineCap_nat_positive_point_sum f n hf hv hclose hinj hR hab hcircle
      hU hUc hV hVc hK hcover hball hw Ξ (fun k _ => hΞ k) hΞl⟩

end RepulsiveCoulomb
