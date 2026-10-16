import LeanResearch.RepulsiveCoulomb.PointFiniteRegularTurn
import LeanResearch.RepulsiveCoulomb.PointFiniteActualFluxSum
import LeanResearch.RepulsiveCoulomb.PointFiniteCornerTurn
import LeanResearch.RepulsiveCoulomb.PointFiniteCornerPredecessor

/-! Full signed Gauss--Bonnet for a genuine finite regular C1 Jordan family
with radial germs only at positive boundary atoms. Ordinary zero-mass corners
may be arbitrary noncuspidal C1 corners, including transverse circle caps.
The curved-edge covariant turns are retained; no geodesicity or sign is
silently assigned to them. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace RepulsiveCoulomb

/-- Construct the physical full corner angles and derive full finite
Gauss--Bonnet from actual oriented turning and actual coalesced point-flux.
Only positive-atom vertices require the genuine radial geometric records;
their angle is identified with the original physical tangent corner. -/
theorem exists_finite_regular_radial_atom_gauss_bonnet
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hn : 0 < n)
    (hf : ∀ k ≤ n, ContDiff ℝ 1 (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (hreg : ∀ k ≤ n, ∀ t ∈ Icc (0 : ℝ) 1, deriv (f k) t ≠ 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 → f i s = f j t → i = j ∧ s = t)
    (hc : ∀ k ≤ n, deriv (f k) 0 / deriv (f (if k = 0 then n else k - 1)) 1 ∈ Complex.slitPlane)
    (havoid : ∀ k ≤ n, ∀ t ∈ Ioo (0 : ℝ) 1, f k t ∉ pointPunctures a y)
    (hrad : ∀ k ≤ n, 0 < coalescedPointExponent a y (f k 0) →
      ∃ β : ℝ, Nonempty (PointFiniteRadialCornerAt f n k β))
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hdisj : Disjoint U V)
    (hK : IsCompact (closure U))
    (hcover : U ∪ V = (⋃ k ≤ n, f k '' Icc (0 : ℝ) 1)ᶜ)
    (hvertexU : ∀ k ≤ n, f k 0 ∈ closure U) (hvertexV : ∀ k ≤ n, f k 0 ∈ closure V)
    {w : ℂ} (hw : w ∈ U) (Ξ τ : ℕ → Icc (0 : ℝ) 1 → ℝ)
    (hΞ : ∀ k ≤ n, Continuous (Ξ k)) (hτ : ∀ k ≤ n, Continuous (τ k))
    (hΞl : ∀ k ≤ n, ∀ t, Complex.exp ((Ξ k t : ℂ) * Complex.I) =
      (f k t - w) / (‖f k t - w‖ : ℂ))
    (hτl : ∀ k ≤ n, ∀ t, Complex.exp ((τ k t : ℂ) * Complex.I) =
      deriv (f k) t / (‖deriv (f k) t‖ : ℂ))
    (hΞturn : (∑ k ∈ Finset.range (n + 1), (Ξ k 1 - Ξ k 0)) = 2 * Real.pi)
    (ψ : Fin m → ℕ → Icc (0 : ℝ) 1 → ℝ)
    (hψ : ∀ j k, k ≤ n → Continuous (ψ j k))
    (hψlift : ∀ j, a j ≠ 0 → ∀ k ≤ n, ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((ψ j k t : ℂ) * Complex.I) = (f k t - y j) / (‖f k t - y j‖ : ℂ)) :
    ∃ θ : ℕ → ℝ, (∀ k ≤ n, 0 < θ k ∧ θ k < 2 * Real.pi) ∧
      (∀ k ≤ n, Complex.arg (deriv (f k) 0 /
        deriv (f (if k = 0 then n else k - 1)) 1) = Real.pi - θ k) ∧
      (∀ k ≤ n, 0 < coalescedPointExponent a y (f k 0) →
        Nonempty (PointFiniteRadialCornerAt f n k (θ k))) ∧
      (∑ k ∈ Finset.range (n + 1), ((τ k 1 - τ k 0) +
          ∑ j, (a j / 2) * (ψ j k 1 - ψ j k 0))) +
        (∑ k ∈ Finset.range (n + 1), (Real.pi -
          (1 + coalescedPointExponent a y (f k 0) / 2) * θ k)) =
        2 * Real.pi + 2 * Real.pi * (∑ j, if y j ∈ U then a j / 2 else 0) := by
  classical
  let θ : ℕ → ℝ := fun k => Real.pi - Complex.arg
    (deriv (f k) 0 / deriv (f (if k = 0 then n else k - 1)) 1)
  have hθ (k : ℕ) (hk : k ≤ n) : 0 < θ k ∧ θ k < 2 * Real.pi := by
    have hlt := lt_of_le_of_ne (Complex.arg_le_pi
      (deriv (f k) 0 / deriv (f (if k = 0 then n else k - 1)) 1))
      (Complex.slitPlane_arg_ne_pi (hc k hk))
    have hgt := Complex.neg_pi_lt_arg
      (deriv (f k) 0 / deriv (f (if k = 0 then n else k - 1)) 1)
    dsimp [θ]
    constructor <;> linarith
  have hpc (k : ℕ) (_ : k ≤ n) : Complex.arg (deriv (f k) 0 /
      deriv (f (if k = 0 then n else k - 1)) 1) = Real.pi - θ k := by
    dsimp [θ]
    ring
  have hD (k : ℕ) (hk : k ≤ n) (hκ : 0 < coalescedPointExponent a y (f k 0)) :
      Nonempty (PointFiniteRadialCornerAt f n k (θ k)) := by
    obtain ⟨β, ⟨D⟩⟩ := hrad k hk hκ
    have hβ := D.principal_turn_eq hf
    rw [D.incoming_index_eq hv hclose hinj] at hβ
    have heq : β = θ k := by dsimp [θ]; linarith
    rw [← heq]
    exact ⟨D⟩
  have hwC : w ∉ ⋃ k ≤ n, f k '' Icc (0 : ℝ) 1 := by
    have hmem : w ∈ U ∪ V := Or.inl hw
    rw [hcover] at hmem
    exact hmem
  have hnonzero : (∑ k ∈ Finset.range (n + 1), (Ξ k 1 - Ξ k 0)) ≠ 0 := by
    rw [hΞturn]
    exact ne_of_gt (by positivity)
  have hturn := finite_regular_original_family_oriented_total_turn f n hn hf hv hclose hreg hinj hc
    w hwC τ Ξ hτ hΞ hτl hΞl hnonzero
  have hcornersum : (∑ k ∈ Finset.range (n + 1), Complex.arg (deriv (f k) 0 /
      deriv (f (if k = 0 then n else k - 1)) 1)) =
        ∑ k ∈ Finset.range (n + 1), (Real.pi - θ k) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hpc k (by have := Finset.mem_range.mp hk; omega)
  rw [hcornersum, hΞturn] at hturn
  have hflux := finite_actual_radial_boundary_weighted_argument_sum ha y f n hf hv hclose hinj
    (hreg 0 (Nat.zero_le n) (1 / 2) (by norm_num)) havoid
    hU hUc hV hVc hdisj hK hcover hvertexU hvertexV hw Ξ hΞ
    (fun k hk t _ => hΞl k hk t) hΞturn θ (fun k hk hκ => Classical.choice (hD k hk hκ)) ψ hψ hψlift
  refine ⟨θ, hθ, hpc, hD, ?_⟩
  have hcovariant : (∑ k ∈ Finset.range (n + 1), ((τ k 1 - τ k 0) +
      ∑ j, (a j / 2) * (ψ j k 1 - ψ j k 0))) =
        (∑ k ∈ Finset.range (n + 1), (τ k 1 - τ k 0)) +
        (∑ j, (a j / 2) * (∑ k ∈ Finset.range (n + 1), (ψ j k 1 - ψ j k 0))) := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
  have hcornerbudget : (∑ k ∈ Finset.range (n + 1), (Real.pi -
      (1 + coalescedPointExponent a y (f k 0) / 2) * θ k)) =
    (∑ k ∈ Finset.range (n + 1), (Real.pi - θ k)) -
      ∑ k ∈ Finset.range (n + 1), (coalescedPointExponent a y (f k 0) / 2) * θ k := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hcovariant, hcornerbudget]
  linarith

end RepulsiveCoulomb
