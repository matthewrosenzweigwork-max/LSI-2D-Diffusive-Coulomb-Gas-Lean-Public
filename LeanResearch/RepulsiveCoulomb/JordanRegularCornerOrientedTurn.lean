import LeanResearch.RepulsiveCoulomb.JordanFinitePhysicalRounding
import LeanResearch.RepulsiveCoulomb.JordanFiniteNonzeroWindingTurn

/-! End-to-end finite regular non-antipodal C1 Jordan turning. The common
physical positive half-planes, actual simple C1 smoothing and avoiding
homotopies are constructed. No common holomorphic collar is assumed.
Records-only, uncompiled candidate. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

/-- The complete original signed tangent and principal-corner turn equals
its actual nonzero point winding. This strictly removes the radial-holomorphic
collar requirement at regular corners. -/
theorem finite_regular_noncuspidal_jordan_oriented_total_turn
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
    (hc : ∀ i, deriv (f i) 0 / deriv (f (σ.symm i)) 1 ∈ Complex.slitPlane)
    (w : ℂ) (hw : w ∉ ⋃ i, f i '' Icc (0 : ℝ) 1)
    (θ ψ : ι → Icc (0 : ℝ) 1 → ℝ)
    (hθ : ∀ i, Continuous (θ i)) (hψ : ∀ i, Continuous (ψ i))
    (hθl : ∀ i t, Complex.exp ((θ i t : ℂ) * Complex.I) = deriv (f i) t / (‖deriv (f i) t‖ : ℂ))
    (hψl : ∀ i t, Complex.exp ((ψ i t : ℂ) * Complex.I) = (f i t - w) / (‖f i t - w‖ : ℂ))
    (hpoint : (∑ i, (ψ i 1 - ψ i 0)) ≠ 0) :
    (∑ i, (θ i 1 - θ i 0)) +
        (∑ i, Complex.arg (deriv (f i) 0 / deriv (f (σ.symm i)) 1)) =
      ∑ i, (ψ i 1 - ψ i 0) := by
  classical
  obtain ⟨δ, c, C, E, hδ, hδq, hC, hE, hEr, hEv, hEd, hEinj,
      hmid, hEL, hER, hCP, hEa, hfpL, hfpR, hEpL, hEpR, hhom⟩ :=
    exists_simultaneous_physical_C1_rounding σ hσ f hf hend hreg hinj hc w hw
  choose F hF hF0 hF1 hFL hFR hFA using hhom
  choose Θ hΘ hΘl using fun i => exists_regular_edge_tangent_angle_lift (hE i) (hEr i)
  choose Ψ hΨ hΨl using fun i => exists_interval_euclidean_angle_lift
    (((hE i).continuous.comp continuous_subtype_val).sub continuous_const)
    (fun t : Icc (0 : ℝ) 1 => sub_ne_zero.mpr (hEa i t t.2))
  have hrad (i : ι) (t : ℝ) (_ : |t| ≤ δ) :
      f (σ.symm i) (1 + t) = finitePhysicalCornerMap σ f i (t • (1 : ℂ)) ∧
        f i t = finitePhysicalCornerMap σ f i (t • Complex.I) :=
    ⟨(finitePhysicalCornerMap_axes σ f hend i t).1.symm,
      (finitePhysicalCornerMap_axes σ f hend i t).2.symm⟩
  have hpointpres : (∑ i, (Ψ i 1 - Ψ i 0)) = ∑ i, (ψ i 1 - ψ i 0) :=
    finite_radial_rounding_preserves_point_argument_sum σ f C E
      (finitePhysicalCornerMap σ f) (fun _ => 1) (fun _ => Complex.I)
      hδ hδq hrad hCP hEL hER hmid F hF hF0 hF1
      (fun i s => (hFL i s).trans (hFL i 0).symm)
      (fun i s => (hFR i s).trans (hFR i 0).symm)
      w hFA ψ Ψ hψ hΨ hψl hΨl
  have hturnpres : (∑ i, (Θ i 1 - Θ i 0)) = (∑ i, (θ i 1 - θ i 0)) +
      ∑ i, Complex.arg (deriv (f i) 0 / deriv (f (σ.symm i)) 1) :=
    finite_physical_rounding_preserves_tangent_turn_sum σ f E hf hE hEd hc hδ hδq c
      hfpL hfpR hEpL hEpR hmid θ Θ hθ hΘ hθl hΘl
  have hnewnonzero : (∑ i, (Ψ i 1 - Ψ i 0)) ≠ 0 := by rwa [hpointpres]
  have horient := enumerated_matched_regular_cycle_nonzero_argument_eq_turn
    σ n e heinj hesurj henext heclose E hE hEv hEd hEr hEinj w hEa
    Θ Ψ hΘ hΨ hΘl hΨl hnewnonzero
  exact hturnpres.symm.trans (horient.symm.trans hpointpres)

/-- Positive actual winding specializes the full original turn to +2π. -/
theorem finite_regular_noncuspidal_jordan_positive_total_turn
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
    (hc : ∀ i, deriv (f i) 0 / deriv (f (σ.symm i)) 1 ∈ Complex.slitPlane)
    (w : ℂ) (hw : w ∉ ⋃ i, f i '' Icc (0 : ℝ) 1)
    (θ ψ : ι → Icc (0 : ℝ) 1 → ℝ)
    (hθ : ∀ i, Continuous (θ i)) (hψ : ∀ i, Continuous (ψ i))
    (hθl : ∀ i t, Complex.exp ((θ i t : ℂ) * Complex.I) = deriv (f i) t / (‖deriv (f i) t‖ : ℂ))
    (hψl : ∀ i t, Complex.exp ((ψ i t : ℂ) * Complex.I) = (f i t - w) / (‖f i t - w‖ : ℂ))
    (hpoint : (∑ i, (ψ i 1 - ψ i 0)) = 2 * Real.pi) :
    (∑ i, (θ i 1 - θ i 0)) +
        (∑ i, Complex.arg (deriv (f i) 0 / deriv (f (σ.symm i)) 1)) = 2 * Real.pi := by
  have hnonzero : (∑ i, (ψ i 1 - ψ i 0)) ≠ 0 := by rw [hpoint]; positivity
  exact (finite_regular_noncuspidal_jordan_oriented_total_turn σ hσ n e
    heinj hesurj henext heclose f hf hend hreg hinj hc w hw θ ψ hθ hψ hθl hψl hnonzero).trans hpoint

end RepulsiveCoulomb
