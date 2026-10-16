import LeanResearch.RepulsiveCoulomb.PointRadialFiniteTurn
import LeanResearch.RepulsiveCoulomb.PointRadialFiniteCornerGeometry
import LeanResearch.RepulsiveCoulomb.PointFiniteActualFluxSum
import LeanResearch.RepulsiveCoulomb.PointFiniteCornerTurn

/-! Full Gauss--Bonnet accounting on an actual finite radial C1 Jordan family.
All local corner geometry is constructed from the original macro-arcs; the
actual point sums are classified and coalesced by the proved geometric
accounting theorem. This radial theorem does not cover arbitrary nonradial
regular circle/line cap junctions. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace RepulsiveCoulomb

/-- The actual covariant arc turns plus actual cone-sector corner turns equal
the full interior curvature budget. Geometry, winding and point-flux values
are derived from the literal family and its actual lifts. The local geometric
corner records, full reflex angles, and point-sum decomposition are not inputs. -/
theorem exists_point_radial_finite_gauss_bonnet
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (arcs : ℕ → PointRadialC1PlaneArc ha y) (n : ℕ) (hn : 0 < n)
    (hv : ∀ k < n, (arcs k).curve 1 = (arcs (k + 1)).curve 0)
    (hclose : (arcs n).curve 1 = (arcs 0).curve 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      (arcs i).curve s = (arcs j).curve t → i = j ∧ s = t)
    (havoid : ∀ k ≤ n, ∀ t ∈ Ioo (0 : ℝ) 1, (arcs k).curve t ∉ pointPunctures a y)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hdisj : Disjoint U V)
    (hK : IsCompact (closure U))
    (hcover : U ∪ V = (⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1)ᶜ)
    (hvertexU : ∀ k ≤ n, (arcs k).curve 0 ∈ closure U)
    (hvertexV : ∀ k ≤ n, (arcs k).curve 0 ∈ closure V)
    {w : ℂ} (hw : w ∈ U) (Ξ τ : ℕ → Icc (0 : ℝ) 1 → ℝ)
    (hΞ : ∀ k ≤ n, Continuous (Ξ k)) (hτ : ∀ k ≤ n, Continuous (τ k))
    (hΞl : ∀ k ≤ n, ∀ t, Complex.exp ((Ξ k t : ℂ) * Complex.I) =
      ((arcs k).curve t - w) / (‖(arcs k).curve t - w‖ : ℂ))
    (hτl : ∀ k ≤ n, ∀ t, Complex.exp ((τ k t : ℂ) * Complex.I) =
      deriv (arcs k).curve t / (‖deriv (arcs k).curve t‖ : ℂ))
    (hΞturn : (∑ k ∈ Finset.range (n + 1), (Ξ k 1 - Ξ k 0)) = 2 * Real.pi)
    (ψ : Fin m → ℕ → Icc (0 : ℝ) 1 → ℝ)
    (hψ : ∀ j k, k ≤ n → Continuous (ψ j k))
    (hψlift : ∀ j, a j ≠ 0 → ∀ k ≤ n, ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((ψ j k t : ℂ) * Complex.I) =
        ((arcs k).curve t - y j) / (‖(arcs k).curve t - y j‖ : ℂ)) :
    ∃ θ : ℕ → ℝ, (∀ k ≤ n, 0 < θ k ∧ θ k < 2 * Real.pi) ∧
      (∀ k ≤ n, Nonempty (PointFiniteRadialCornerAt (fun i => (arcs i).curve) n k (θ k))) ∧
      (∀ k ≤ n, Complex.arg (deriv (arcs k).curve 0 /
        deriv (arcs (if k = 0 then n else k - 1)).curve 1) = Real.pi - θ k) ∧
      (∑ k ∈ Finset.range (n + 1), ((τ k 1 - τ k 0) +
          ∑ j, (a j / 2) * (ψ j k 1 - ψ j k 0))) +
        (∑ k ∈ Finset.range (n + 1), (Real.pi -
          (1 + coalescedPointExponent a y ((arcs k).curve 0) / 2) * θ k)) =
        2 * Real.pi + 2 * Real.pi * (∑ j, if y j ∈ U then a j / 2 else 0) := by
  classical
  have hcorners (k : ℕ) (hk : k ≤ n) :=
    exists_point_radial_finite_corner_geometry ha y arcs n hn hv hclose hinj k hk
  choose angle corner horder using hcorners
  let θ : ℕ → ℝ := fun k => if hk : k ≤ n then angle k hk else 0
  have hθ (k : ℕ) (hk : k ≤ n) : θ k = angle k hk := dif_pos hk
  let D (k : ℕ) (hk : k ≤ n) : PointFiniteRadialCornerAt (fun i => (arcs i).curve) n k (θ k) := by
    rw [hθ k hk]
    exact corner k hk
  have hf : ∀ k ≤ n, ContDiff ℝ 1 (arcs k).curve := fun k _ => (arcs k).smooth
  have hpc (k : ℕ) (hk : k ≤ n) : Complex.arg (deriv (arcs k).curve 0 /
      deriv (arcs (if k = 0 then n else k - 1)).curve 1) = Real.pi - θ k := by
    have he := (corner k hk).principal_turn_eq hf
    rw [horder k hk, pointFiniteCyclicCornerOrder_last n k hk] at he
    simpa only [hθ k hk] using he
  have hwC : w ∉ ⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1 := by
    change w ∈ (⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1)ᶜ
    rw [← hcover]
    exact Or.inl hw
  have hnonzero : (∑ k ∈ Finset.range (n + 1), (Ξ k 1 - Ξ k 0)) ≠ 0 := by
    rw [hΞturn]
    exact ne_of_gt (by positivity)
  have hturn := point_radial_finite_family_oriented_total_turn ha y arcs n hn hv hclose hinj
    w hwC τ Ξ hτ hΞ hτl hΞl hnonzero
  have hcornersum : (∑ k ∈ Finset.range (n + 1), Complex.arg (deriv (arcs k).curve 0 /
      deriv (arcs (if k = 0 then n else k - 1)).curve 1)) =
        ∑ k ∈ Finset.range (n + 1), (Real.pi - θ k) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hpc k (by have := Finset.mem_range.mp hk; omega)
  rw [hcornersum, hΞturn] at hturn
  have hflux := finite_actual_radial_boundary_weighted_argument_sum ha y
    (fun k => (arcs k).curve) n hf hv hclose hinj ((arcs 0).regular _ (by norm_num)) havoid
    hU hUc hV hVc hdisj hK hcover hvertexU hvertexV hw Ξ hΞ
    (fun k hk t _ => hΞl k hk t) hΞturn θ (fun k hk _ => D k hk) ψ hψ hψlift
  refine ⟨θ, ?_, (fun k hk => ⟨D k hk⟩), hpc, ?_⟩
  · intro k hk
    rw [hθ k hk]
    exact ⟨(corner k hk).angle_pos, (corner k hk).angle_lt⟩
  · have hcovariant : (∑ k ∈ Finset.range (n + 1), ((τ k 1 - τ k 0) +
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
        (1 + coalescedPointExponent a y ((arcs k).curve 0) / 2) * θ k)) =
      (∑ k ∈ Finset.range (n + 1), (Real.pi - θ k)) -
        ∑ k ∈ Finset.range (n + 1), (coalescedPointExponent a y ((arcs k).curve 0) / 2) * θ k := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hcovariant, hcornerbudget]
    linarith

end RepulsiveCoulomb
