module

public import LeanResearch.RepulsiveCoulomb.PointFiniteMixedGaussBonnetGerms
public import LeanResearch.RepulsiveCoulomb.PointRadialPositiveFamily
public import LeanResearch.RepulsiveCoulomb.PointRadialCornerActualSide
public import LeanResearch.RepulsiveCoulomb.PointCornerPhysicalChartTransition

@[expose] public section

/-! Source-only draft. General mixed Gauss--Bonnet on the SAME actual cap
supplied by first-return topology. The finite source-derived geodesic family,
its literal radial endpoint germs and its carrier are required. Positive
orientation, all lifts, full all-point corner intervals and zero edge terms
are constructed. This file does not construct the finite family from firstReturn5.
The full GB equation is a theorem output, never an input certificate. -/
noncomputable section
open Set Filter Metric
open scoped BigOperators Topology Classical
namespace RepulsiveCoulomb

/-- Actual finite geodesic cap data retained after invoking true mixed GB.
This output record is built below; it is not an allowed first-return input. -/
structure PointFirstReturnFiniteGBData {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (arcs : ℕ → PointRadialC1PlaneArc ha y) (n : ℕ) (U V : Set ℂ) where
  oriented : ℕ → PointRadialC1PlaneArc ha y
  orientation : oriented = arcs ∨ oriented = fun k => (arcs (n - k)).reverse
  consecutive : ∀ k < n, (oriented k).curve 1 = (oriented (k + 1)).curve 0
  closing : (oriented n).curve 1 = (oriented 0).curve 0
  simple : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
    s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
    (oriented i).curve s = (oriented j).curve t → i = j ∧ s = t
  carrier : (⋃ k ≤ n, (oriented k).curve '' Icc (0 : ℝ) 1) =
    (⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1)
  observer : ℂ
  observer_inside : observer ∈ U
  observerAngle : ℕ → Icc (0 : ℝ) 1 → ℝ
  observer_continuous : ∀ k ≤ n, Continuous (observerAngle k)
  observer_lift : ∀ k ≤ n, ∀ t,
    Complex.exp ((observerAngle k t : ℂ) * Complex.I) =
      ((oriented k).curve t - observer) / (‖(oriented k).curve t - observer‖ : ℂ)
  observer_turn : (∑ k ∈ Finset.range (n + 1), (observerAngle k 1 - observerAngle k 0)) =
    2 * Real.pi
  angle : ℕ → ℝ
  angle_range : ∀ k ≤ n, 0 < angle k ∧ angle k < 2 * Real.pi
  principal_turn : ∀ k ≤ n, Complex.arg (deriv (oriented k).curve 0 /
    deriv (oriented (if k = 0 then n else k - 1)).curve 1) = Real.pi - angle k
  radial_corner : ∀ k ≤ n,
    ∃ G : PointFiniteRadialCornerAt (fun i => (oriented i).curve) n k (angle k),
      ∃ q : ℂ, ‖q‖ = 1 ∧ G.chart.source =
        (pointChosenSmoothRadialChart ha y ((oriented k).curve 0)).source ∧
        ∀ z, G.chart z = q * pointChosenSmoothRadialChart ha y ((oriented k).curve 0) z
  gauss_bonnet : (∑ k ∈ Finset.range (n + 1), (Real.pi -
    (1 + coalescedPointExponent a y ((oriented k).curve 0) / 2) * angle k)) =
    2 * Real.pi + 2 * Real.pi * (∑ j, if y j ∈ U then a j / 2 else 0)

/-- Choose orientation and construct all mixed-GB inputs from the actual radial
geodesic macro-arcs, while retaining the literal supplied Jordan components.
In particular ordinary endpoints also acquire genuine noncuspidal full sectors.
No total turn bound, cap-side angle, or winding certificate is an input. -/
theorem exists_pointFirstReturnFiniteGBData
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (arcs : ℕ → PointRadialC1PlaneArc ha y) (n : ℕ) (hn : 0 < n)
    (hv : ∀ k < n, (arcs k).curve 1 = (arcs (k + 1)).curve 0)
    (hclose : (arcs n).curve 1 = (arcs 0).curve 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      (arcs i).curve s = (arcs j).curve t → i = j ∧ s = t)
    (harg : ∀ k ≤ n, (arcs k).HasArgumentTurn)
    (havoid : ∀ k ≤ n, ∀ t ∈ Ioo (0 : ℝ) 1, (arcs k).curve t ∉ pointPunctures a y)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hdisj : Disjoint U V)
    (hK : IsCompact (closure U))
    (hcover : U ∪ V = (⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1)ᶜ)
    (hfrontU : frontier U = ⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1)
    (hfrontV : frontier V = ⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1) :
    Nonempty (PointFirstReturnFiniteGBData ha y arcs n U V) := by
  obtain ⟨B, hBcase, hBv, hBc, hBi, hBarg, hBavoid, hBcarrier, hBpositive⟩ :=
    exists_point_radial_positive_family ha y arcs n hv hclose hinj harg havoid
      hU hUc hV hVc hK hcover
  have hcoverB : U ∪ V = (⋃ k ≤ n, (B k).curve '' Icc (0 : ℝ) 1)ᶜ := by rwa [hBcarrier]
  have hvertexU (k : ℕ) (hk : k ≤ n) : (B k).curve 0 ∈ closure U := by
    apply frontier_subset_closure
    rw [hfrontU, ← hBcarrier]
    exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, 0, by norm_num, rfl⟩⟩
  have hvertexV (k : ℕ) (hk : k ≤ n) : (B k).curve 0 ∈ closure V := by
    apply frontier_subset_closure
    rw [hfrontV, ← hBcarrier]
    exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, 0, by norm_num, rfl⟩⟩
  let idx := pointCyclicListIndex (n + 1) (Nat.zero_lt_succ n)
  have hidx (k : ℕ) (hk : k ≤ n) : (idx k).val = k := Nat.mod_eq_of_lt (by omega)
  have hlifts (i : Fin (n + 1)) := hBarg i.val (by omega)
  unfold PointRadialC1PlaneArc.HasArgumentTurn at hlifts
  choose T P hT hP hTl hPl htransport using hlifts
  let τ : ℕ → Icc (0 : ℝ) 1 → ℝ := fun k => T (idx k)
  let ψ : Fin m → ℕ → Icc (0 : ℝ) 1 → ℝ := fun j k => P (idx k) j
  have hτ (k : ℕ) (_ : k ≤ n) : Continuous (τ k) := hT (idx k)
  have hψ (j : Fin m) (k : ℕ) (_ : k ≤ n) : Continuous (ψ j k) := hP (idx k) j
  have hτl (k : ℕ) (hk : k ≤ n) (t : Icc (0 : ℝ) 1) :
      Complex.exp ((τ k t : ℂ) * Complex.I) = deriv (B k).curve t / (‖deriv (B k).curve t‖ : ℂ) := by
    simpa only [τ, hidx k hk] using hTl (idx k) t
  have hψl (j : Fin m) (hj : a j ≠ 0) (k : ℕ) (hk : k ≤ n) (t : Icc (0 : ℝ) 1)
      (ht : t.1 ∈ Ioo (0 : ℝ) 1) :
      Complex.exp ((ψ j k t : ℂ) * Complex.I) = ((B k).curve t - y j) / (‖(B k).curve t - y j‖ : ℂ) := by
    simpa only [ψ, hidx k hk] using hPl (idx k) j hj t ht
  obtain ⟨w, hw⟩ := hUc.nonempty
  have hwC : w ∉ ⋃ k ≤ n, (B k).curve '' Icc (0 : ℝ) 1 := by
    change w ∈ (⋃ k ≤ n, (B k).curve '' Icc (0 : ℝ) 1)ᶜ
    rw [← hcoverB]
    exact Or.inl hw
  have hpoint (i : Fin (n + 1)) := exists_interval_euclidean_angle_lift
    ((((B i.val).smooth.continuous).comp continuous_subtype_val).sub continuous_const)
    (show ∀ t : Icc (0 : ℝ) 1, (B i.val).curve t - w ≠ 0 by
      intro t ht
      exact hwC (mem_iUnion.mpr ⟨i.val, mem_iUnion.mpr ⟨by omega, t, t.2, sub_eq_zero.mp ht⟩⟩))
  choose X hX hXl using hpoint
  let Ξ : ℕ → Icc (0 : ℝ) 1 → ℝ := fun k => X (idx k)
  have hΞ (k : ℕ) (_ : k ≤ n) : Continuous (Ξ k) := hX (idx k)
  have hΞl (k : ℕ) (hk : k ≤ n) (t : Icc (0 : ℝ) 1) :
      Complex.exp ((Ξ k t : ℂ) * Complex.I) = ((B k).curve t - w) / (‖(B k).curve t - w‖ : ℂ) := by
    simpa only [Ξ, hidx k hk, Pi.sub_apply, Function.comp_apply] using hXl (idx k) t
  have hΞturn := hBpositive w hw Ξ hΞ hΞl
  have hgerms (k : ℕ) (hk : k ≤ n) :
      ∃ u v : ℂ, u ≠ 0 ∧ v ≠ 0 ∧
        (B k).curve =ᶠ[𝓝 (0 : ℝ)]
          (fun t => (pointChosenSmoothRadialChart ha y ((B k).curve 0)).symm (t • v)) ∧
        (B (if k = 0 then n else k - 1)).curve =ᶠ[𝓝 (1 : ℝ)]
          (fun t => (pointChosenSmoothRadialChart ha y ((B k).curve 0)).symm ((1 - t) • u)) := by
    let j := if k = 0 then n else k - 1
    have hj : (B j).curve 1 = (B k).curve 0 := by
      dsimp [j]
      by_cases hk0 : k = 0
      · subst k
        change (B n).curve 1 = (B 0).curve 0
        exact hBc
      · rw [if_neg hk0]
        have he := hBv (k - 1) (by omega)
        simpa only [Nat.sub_add_cancel (show 1 ≤ k by omega)] using he
    refine ⟨(B j).rightVector, (B k).leftVector, (B j).rightVector_ne,
      (B k).leftVector_ne, (B k).left_radial, ?_⟩
    simpa only [hj] using (B j).right_radial
  have hgeom (k : ℕ) (hk : k ≤ n) :
      ∃ β : ℝ, ∃ G : PointFiniteRadialCornerAt (fun i => (B i).curve) n k β,
        ∃ q : ℂ, ‖q‖ = 1 ∧ G.chart.source =
          (pointChosenSmoothRadialChart ha y ((B k).curve 0)).source ∧
          ∀ z, G.chart z = q * pointChosenSmoothRadialChart ha y ((B k).curve 0) z := by
    obtain ⟨u, v, hu, hv0, hleft, hright⟩ := hgerms k hk
    obtain ⟨β, G, _, q, hq, hsrc, hchart⟩ :=
      exists_point_finite_radial_corner_with_chosen_rotation ha y
        (fun i => (B i).curve) n hn hBv hBc hBi k hk u v hu hv0 hleft hright
    exact ⟨β, G, q, hq, hsrc, hchart⟩
  have hregularcorner (k : ℕ) (hk : k ≤ n)
      (_ : coalescedPointExponent a y ((B k).curve 0) = 0) :
      deriv (B k).curve 0 / deriv (B (if k = 0 then n else k - 1)).curve 1 ∈ Complex.slitPlane := by
    obtain ⟨β, G, _, _, _, _⟩ := hgeom k hk
    apply Complex.mem_slitPlane_iff_arg.mpr
    constructor
    · intro he
      have hp := G.principal_turn_eq (fun i _ => (B i).smooth)
      rw [G.incoming_index_eq hBv hBc hBi, he] at hp
      linarith [G.angle_pos]
    · exact div_ne_zero ((B k).regular 0 (by norm_num))
        ((B (if k = 0 then n else k - 1)).regular 1 (by norm_num))
  obtain ⟨θ, hθ, hprincipal, _, hGB⟩ :=
    exists_finite_mixed_gauss_bonnet_of_original_germs ha y
      (fun i => (B i).curve) n hn (fun i _ => (B i).smooth) hBv hBc
      (fun i _ => (B i).regular) hBi hregularcorner hBavoid
      (fun k hk _ => hgerms k hk) hU hUc hV hVc hdisj hK hcoverB
      hvertexU hvertexV hw Ξ τ hΞ hτ hΞl hτl hΞturn ψ hψ hψl
  have hzero : (∑ k ∈ Finset.range (n + 1), ((τ k 1 - τ k 0) +
      ∑ j, (a j / 2) * (ψ j k 1 - ψ j k 0))) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have he : τ k 1 - τ k 0 = -(∑ j, (a j / 2) * (ψ j k 1 - ψ j k 0)) :=
      htransport (idx k)
    linarith
  rw [hzero, zero_add] at hGB
  have hgeomθ (k : ℕ) (hk : k ≤ n) :
      ∃ G : PointFiniteRadialCornerAt (fun i => (B i).curve) n k (θ k),
        ∃ q : ℂ, ‖q‖ = 1 ∧ G.chart.source =
          (pointChosenSmoothRadialChart ha y ((B k).curve 0)).source ∧
          ∀ z, G.chart z = q * pointChosenSmoothRadialChart ha y ((B k).curve 0) z := by
    obtain ⟨β, G, q, hq, hsrc, hchart⟩ := hgeom k hk
    have hp := G.principal_turn_eq (fun i _ => (B i).smooth)
    rw [G.incoming_index_eq hBv hBc hBi] at hp
    have heq : β = θ k := by linarith [hprincipal k hk]
    subst β
    exact ⟨G, q, hq, hsrc, hchart⟩
  exact ⟨⟨B, hBcase, hBv, hBc, hBi, hBcarrier, w, hw, Ξ, hΞ, hΞl,
    hΞturn, θ, hθ, hprincipal, hgeomθ, hGB⟩⟩

/-- Every vertex, including an unmarked initial point or far return, has a
strictly positive physical full angle, hence signed turn strictly below pi.
This is derived from the actual original radial germs and mixed GB geometry. -/
theorem PointFirstReturnFiniteGBData.physical_angle_pos_and_turn_lt_pi
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {arcs : ℕ → PointRadialC1PlaneArc ha y} {n : ℕ} {U V : Set ℂ}
    (H : PointFirstReturnFiniteGBData ha y arcs n U V) {k : ℕ} (hk : k ≤ n) :
    0 < (1 + coalescedPointExponent a y ((H.oriented k).curve 0) / 2) * H.angle k ∧
      Real.pi - (1 + coalescedPointExponent a y ((H.oriented k).curve 0) / 2) * H.angle k < Real.pi := by
  have hκ := coalescedPointExponent_nonneg a y ((H.oriented k).curve 0)
  have hpos : 0 < (1 + coalescedPointExponent a y ((H.oriented k).curve 0) / 2) * H.angle k :=
    mul_pos (by positivity) (H.angle_range k hk).1
  exact ⟨hpos, sub_lt_self _ hpos⟩

end RepulsiveCoulomb
