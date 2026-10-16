import LeanResearch.RepulsiveCoulomb.JordanFiniteRadialTurnTransport
import LeanResearch.RepulsiveCoulomb.JordanFiniteNonzeroWindingTurn

/-! End-to-end oriented total turn for an actual finite noncuspidal radial-
chart Jordan family. The common rounding width, all disjoint neighborhoods,
actual regular simple rounded family, local avoiding homotopies, global C¹
loop and actual bounded component are constructed inside the proof.

The orientation witness is an ACTUAL point-argument lift on each original
arc, with its exponential identity and nonzero finite increment. It is not a
tangent-turn or Gauss--Bonnet hypothesis. The already established original-
loop winding theorem supplies such a witness; choosing its positive traversal
gives the usual +2π total-turn formula. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

/-- The actual finite signed tangent turn, including every principal corner
turn, equals the actual nonzero inside winding of the original unsmoothed
family. No rounding, global parametrization, sign agreement or inside-
preservation certificate is assumed. -/
theorem finite_radial_jordan_oriented_total_turn
    {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (hσ : ∀ i, σ i ≠ i)
    (n : ℕ) (e : ℕ → ι)
    (heinj : ∀ j ≤ n, ∀ k ≤ n, e j = e k → j = k)
    (hesurj : ∀ i, ∃ k ≤ n, e k = i)
    (henext : ∀ k < n, σ (e k) = e (k + 1)) (heclose : σ (e n) = e 0)
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 1 (f i))
    (hend : ∀ i, f i 1 = f (σ i) 0)
    (hreg : ∀ i t, t ∈ Icc (0 : ℝ) 1 → deriv (f i) t ≠ 0)
    (hinj : ∀ i j s t, s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      f i s = f j t → i = j ∧ s = t)
    (w : ℂ) (hw : w ∉ ⋃ i, f i '' Icc (0 : ℝ) 1)
    (V : ι → Set ℂ) (hV : ∀ i, IsOpen (V i)) (h0V : ∀ i, (0 : ℂ) ∈ V i)
    (H : ι → ℂ → ℂ) (hH : ∀ i, AnalyticOnNhd ℂ (H i) (V i))
    (hHreg : ∀ i z, z ∈ V i → deriv (H i) z ≠ 0)
    (hHinj : ∀ i, InjOn (H i) (V i)) (hH0 : ∀ i, H i 0 = f i 0)
    (u v : ι → ℂ) (hu : ∀ i, u i ≠ 0)
    (hc : ∀ i, v i / u i ∈ Complex.slitPlane)
    (hout : ∀ i, f i =ᶠ[𝓝 (0 : ℝ)] (fun t => H i (t • v i)))
    (hin : ∀ i, (fun t => f i (1 + t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => H (σ i) (t • u (σ i))))
    (θ ψ : ι → Icc (0 : ℝ) 1 → ℝ)
    (hθ : ∀ i, Continuous (θ i)) (hψ : ∀ i, Continuous (ψ i))
    (hθl : ∀ i t, Complex.exp ((θ i t : ℂ) * Complex.I) = deriv (f i) t / (‖deriv (f i) t‖ : ℂ))
    (hψl : ∀ i t, Complex.exp ((ψ i t : ℂ) * Complex.I) = (f i t - w) / (‖f i t - w‖ : ℂ))
    (hpoint : (∑ i, (ψ i 1 - ψ i 0)) ≠ 0) :
    (∑ i, (θ i 1 - θ i 0)) +
        (∑ i, Complex.arg (deriv (f i) 0 / deriv (f (σ.symm i)) 1)) =
      ∑ i, (ψ i 1 - ψ i 0) := by
  classical
  obtain ⟨δ, C, E, hδ, hδq, _, _, _, hCP, _, _, hE, hEr, hEv, hEd,
      hEinj, hmid, hEL, hER, hEa, hrad, ⟨R, hR, hRV, hnorm⟩, hhom⟩ :=
    exists_simultaneous_radial_C1_rounding_with_windows σ hσ f hf hend hreg hinj w hw
      V hV h0V H hH hHreg hHinj hH0 u v hu hc hout hin
  choose F hF hF0 hF1 hFL hFR hFA using hhom
  have hθE (i : ι) := exists_regular_edge_tangent_angle_lift (hE i) (hEr i)
  choose Θ hΘ hΘl using hθE
  have hψE (i : ι) := exists_interval_euclidean_angle_lift
    (((hE i).continuous.comp continuous_subtype_val).sub continuous_const)
    (fun t : Icc (0 : ℝ) 1 => sub_ne_zero.mpr (hEa i t t.2))
  choose Ψ hΨ hΨl using hψE
  have hpointpres : (∑ i, (Ψ i 1 - Ψ i 0)) = ∑ i, (ψ i 1 - ψ i 0) :=
    finite_radial_rounding_preserves_point_argument_sum σ f C E H u v hδ hδq
      hrad hCP hEL hER hmid F hF hF0 hF1
      (fun i s => (hFL i s).trans (hFL i 0).symm)
      (fun i s => (hFR i s).trans (hFR i 0).symm)
      w hFA ψ Ψ hψ hΨ hψl hΨl
  have hturnpres : (∑ i, (Θ i 1 - Θ i 0)) = (∑ i, (θ i 1 - θ i 0)) +
      ∑ i, Complex.arg (deriv (f i) 0 / deriv (f (σ.symm i)) 1) :=
    finite_radial_rounding_preserves_tangent_turn_sum σ f C E hf hE hreg hEr
      V H hH hHreg hHinj u v hu hc hδ hδq hR hRV hnorm
      hrad hCP hEL hER hmid θ Θ hθ hΘ hθl hΘl
  have hnewnonzero : (∑ i, (Ψ i 1 - Ψ i 0)) ≠ 0 := by rwa [hpointpres]
  have horient := enumerated_matched_regular_cycle_nonzero_argument_eq_turn
    σ n e heinj hesurj henext heclose E hE hEv hEd hEr hEinj w hEa
    Θ Ψ hΘ hΨ hΘl hΨl hnewnonzero
  exact hturnpres.symm.trans (horient.symm.trans hpointpres)

end RepulsiveCoulomb
