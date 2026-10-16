import LeanResearch.RepulsiveCoulomb.PointRadialCyclicTurnCharts
import LeanResearch.RepulsiveCoulomb.PointRadialCyclicListIndex

/-! Actual geodesic macro-list instantiation of finite-corner oriented turn.
Finite indices, cyclic permutation, common charts, noncuspidality and the
full original carrier are derived from the genuine constructed plane chain. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

/-- Every genuine closed radial C¹ macro-list has the oriented total-turn
formula. The nonzero point-angle increment is the actual orientation witness,
not an assumed tangent-turn sum or curvature formula. -/
theorem point_radial_C1_closed_list_oriented_total_turn
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {p : ℂ} (L : List (PointRadialC1PlaneArc ha y))
    (hchain : PointRadialC1PlaneChain ha y p p L) (hlen : 2 ≤ L.length)
    (hpair : L.Pairwise (fun e f => Disjoint
      (e.curve '' Ico (0 : ℝ) 1) (f.curve '' Ico (0 : ℝ) 1)))
    (w : ℂ) (hw : w ∉ pointRadialC1PlaneCarrier L)
    (θ ψ : Fin L.length → Icc (0 : ℝ) 1 → ℝ)
    (hθ : ∀ i, Continuous (θ i)) (hψ : ∀ i, Continuous (ψ i))
    (hθl : ∀ i t, Complex.exp ((θ i t : ℂ) * Complex.I) =
      deriv (L.get i).curve t / (‖deriv (L.get i).curve t‖ : ℂ))
    (hψl : ∀ i t, Complex.exp ((ψ i t : ℂ) * Complex.I) =
      ((L.get i).curve t - w) / (‖(L.get i).curve t - w‖ : ℂ))
    (hpoint : (∑ i, (ψ i 1 - ψ i 0)) ≠ 0) :
    (∑ i, (θ i 1 - θ i 0)) +
      (∑ i, Complex.arg (deriv (L.get i).curve 0 /
        deriv (L.get ((finRotate L.length).symm i)).curve 1)) =
        ∑ i, (ψ i 1 - ψ i 0) := by
  have hpos : 0 < L.length := by omega
  let n := L.length - 1
  let enumeration := pointCyclicListIndex L.length hpos
  have henumeration (k : ℕ) (hk : k ≤ n) : (enumeration k).val = k := by
    have hkn : k < L.length := by dsimp [n] at hk; omega
    exact Nat.mod_eq_of_lt hkn
  have hinjective : ∀ j ≤ n, ∀ k ≤ n, enumeration j = enumeration k → j = k := by
    intro j hj k hk he
    have hv := congrArg Fin.val he
    simpa only [henumeration j hj, henumeration k hk] using hv
  have hsurjective : ∀ i : Fin L.length, ∃ k ≤ n, enumeration k = i := by
    intro i
    have hin : i.val ≤ n := by dsimp [n]; omega
    refine ⟨i.val, hin, ?_⟩
    apply Fin.ext
    exact henumeration _ hin
  have hnext (k : ℕ) (_ : k < n) : finRotate L.length (enumeration k) = enumeration (k + 1) :=
    pointCyclicListIndex_rotate L.length hpos k
  have hwrap : finRotate L.length (enumeration n) = enumeration 0 := by
    rw [pointCyclicListIndex_rotate]
    apply Fin.ext
    change (n + 1) % L.length = 0 % L.length
    have hn : n + 1 = L.length := by dsimp [n]; omega
    rw [hn, Nat.mod_self, Nat.zero_mod]
  exact point_radial_C1_cycle_oriented_total_turn ha y (finRotate L.length)
    (finRotate_ne_self_of_two_le hlen) n enumeration hinjective hsurjective hnext hwrap
    L.get (hchain.cyclic_get_endpoints hpos) (point_radial_list_get_pairwise hpair)
    w (by rwa [point_radial_list_index_carrier]) θ ψ hθ hψ hθl hψl hpoint

/-- A hypothetical genuine simple minimizing bigon produces its actual finite
radial macro-list AND the full oriented total-turn theorem for that original
list. No geometric decomposition, chart or corner-angle certificate is an
input. This does not yet assert bigon exclusion or Gauss--Bonnet. -/
theorem exists_pointConformal_bigon_radial_C1_oriented_turn
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {p q : ℂ} (hpq : p ≠ q) (γ₁ γ₂ : Icc (0 : ℝ) 1 → ℂ)
    (h10 : γ₁ ⟨0, by norm_num⟩ = p) (h11 : γ₁ ⟨1, by norm_num⟩ = q)
    (h20 : γ₂ ⟨0, by norm_num⟩ = p) (h21 : γ₂ ⟨1, by norm_num⟩ = q)
    (hd₁ : ∀ s t, (pointSmoothConformalEDist a y (γ₁ s) (γ₁ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal)
    (hd₂ : ∀ s t, (pointSmoothConformalEDist a y (γ₂ s) (γ₂ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p q).toReal)
    (hmeet : range γ₁ ∩ range γ₂ = {p, q}) :
    ∃ L : List (PointRadialC1PlaneArc ha y),
      PointRadialC1PlaneChain ha y p p L ∧ 2 ≤ L.length ∧
      pointRadialC1PlaneCarrier L = range γ₁ ∪ range γ₂ ∧
      L.Pairwise (fun e f => Disjoint
        (e.curve '' Ico (0 : ℝ) 1) (f.curve '' Ico (0 : ℝ) 1)) ∧
      ∀ (w : ℂ), w ∉ range γ₁ ∪ range γ₂ →
        ∀ (θ ψ : Fin L.length → Icc (0 : ℝ) 1 → ℝ),
          (∀ i, Continuous (θ i)) → (∀ i, Continuous (ψ i)) →
          (∀ i t, Complex.exp ((θ i t : ℂ) * Complex.I) =
            deriv (L.get i).curve t / (‖deriv (L.get i).curve t‖ : ℂ)) →
          (∀ i t, Complex.exp ((ψ i t : ℂ) * Complex.I) =
            ((L.get i).curve t - w) / (‖(L.get i).curve t - w‖ : ℂ)) →
          (∑ i, (ψ i 1 - ψ i 0)) ≠ 0 →
          (∑ i, (θ i 1 - θ i 0)) +
            (∑ i, Complex.arg (deriv (L.get i).curve 0 /
              deriv (L.get ((finRotate L.length).symm i)).curve 1)) =
                ∑ i, (ψ i 1 - ψ i 0) := by
  obtain ⟨L, hchain, hlen, hcarrier, hpair⟩ :=
    exists_pointConformal_simple_radial_C1_cyclic_chain ha y hpq γ₁ γ₂
      h10 h11 h20 h21 hd₁ hd₂ hmeet
  refine ⟨L, hchain, hlen, hcarrier, hpair, ?_⟩
  intro w hw θ ψ hθ hψ hθl hψl hpoint
  exact point_radial_C1_closed_list_oriented_total_turn ha y L hchain hlen hpair
    w (by rwa [hcarrier]) θ ψ hθ hψ hθl hψl hpoint

end RepulsiveCoulomb
