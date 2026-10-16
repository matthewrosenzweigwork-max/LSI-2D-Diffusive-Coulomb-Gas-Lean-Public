import LeanResearch.RepulsiveCoulomb.PointFiniteMixedGaussBonnet
import LeanResearch.RepulsiveCoulomb.PointFiniteLocalRadialCorner

/-! Primitive mixed-family Gauss--Bonnet: actual original radial germs at
positive atoms are enough. Their normalized corner geometry, full angles and
noncuspidality are constructed; no geometric corner record is an input.
Only ordinary zero-mass corners need an explicit physical noncuspidality
condition, supplied for circle joins by actual transversality. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology Classical
namespace RepulsiveCoulomb

/-- The full signed identity for an actual regular finite family with
original radial germs at its positive boundary atoms and arbitrary ordinary
noncuspidal corners. -/
theorem exists_finite_mixed_gauss_bonnet_of_original_germs
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (f : ℕ → ℝ → ℂ) (n : ℕ) (hn : 0 < n)
    (hf : ∀ k ≤ n, ContDiff ℝ 1 (f k))
    (hv : ∀ k < n, f k 1 = f (k + 1) 0) (hclose : f n 1 = f 0 0)
    (hreg : ∀ k ≤ n, ∀ t ∈ Icc (0 : ℝ) 1, deriv (f k) t ≠ 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 → f i s = f j t → i = j ∧ s = t)
    (hregularcorner : ∀ k ≤ n, coalescedPointExponent a y (f k 0) = 0 →
      deriv (f k) 0 / deriv (f (if k = 0 then n else k - 1)) 1 ∈ Complex.slitPlane)
    (havoid : ∀ k ≤ n, ∀ t ∈ Ioo (0 : ℝ) 1, f k t ∉ pointPunctures a y)
    (hgerms : ∀ k ≤ n, 0 < coalescedPointExponent a y (f k 0) →
      ∃ u v : ℂ, u ≠ 0 ∧ v ≠ 0 ∧
        f k =ᶠ[𝓝 (0 : ℝ)]
          (fun t => (pointChosenSmoothRadialChart ha y (f k 0)).symm (t • v)) ∧
        f (if k = 0 then n else k - 1) =ᶠ[𝓝 (1 : ℝ)]
          (fun t => (pointChosenSmoothRadialChart ha y (f k 0)).symm ((1 - t) • u)))
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
  have hrad : ∀ k ≤ n, 0 < coalescedPointExponent a y (f k 0) →
      ∃ β : ℝ, Nonempty (PointFiniteRadialCornerAt f n k β) := by
    intro k hk hκ
    obtain ⟨u, v, hu, hv0, hleft, hright⟩ := hgerms k hk hκ
    obtain ⟨β, D, _⟩ := exists_point_finite_local_radial_corner_geometry ha y f n hn
      hv hclose hinj k hk u v hu hv0 hleft hright
    exact ⟨β, ⟨D⟩⟩
  have hc : ∀ k ≤ n, deriv (f k) 0 /
      deriv (f (if k = 0 then n else k - 1)) 1 ∈ Complex.slitPlane := by
    intro k hk
    by_cases hκ : 0 < coalescedPointExponent a y (f k 0)
    · obtain ⟨β, ⟨D⟩⟩ := hrad k hk hκ
      apply Complex.mem_slitPlane_iff_arg.mpr
      constructor
      · intro he
        have hp := D.principal_turn_eq hf
        rw [D.incoming_index_eq hv hclose hinj, he] at hp
        linarith [D.angle_pos]
      · have hpre : (if k = 0 then n else k - 1) ≤ n := by split_ifs <;> omega
        exact div_ne_zero (hreg k hk 0 (by norm_num)) (hreg _ hpre 1 (by norm_num))
    · exact hregularcorner k hk
        (le_antisymm (le_of_not_gt hκ) (coalescedPointExponent_nonneg a y (f k 0)))
  exact exists_finite_regular_radial_atom_gauss_bonnet ha y f n hn hf hv hclose hreg hinj hc
    havoid hrad hU hUc hV hVc hdisj hK hcover hvertexU hvertexV hw Ξ τ hΞ hτ
    hΞl hτl hΞturn ψ hψ hψlift

end RepulsiveCoulomb
