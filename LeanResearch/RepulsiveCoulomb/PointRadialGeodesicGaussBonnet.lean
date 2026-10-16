import LeanResearch.RepulsiveCoulomb.PointRadialFiniteGaussBonnet
import LeanResearch.RepulsiveCoulomb.PointRadialPositiveFamily
import LeanResearch.RepulsiveCoulomb.PlaneJordanSeparation

/-! Geodesic Gauss--Bonnet for an actual source-derived finite radial family.
The actual Jordan components, positive traversal, inside witness and every
point/tangent lift are constructed. Per-edge geodesic transport sets the
covariant arc contribution to zero. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace RepulsiveCoulomb

theorem exists_point_radial_geodesic_gauss_bonnet
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (arcs : ℕ → PointRadialC1PlaneArc ha y) (n : ℕ) (hn : 0 < n)
    (hv : ∀ k < n, (arcs k).curve 1 = (arcs (k + 1)).curve 0)
    (hclose : (arcs n).curve 1 = (arcs 0).curve 0)
    (hinj : ∀ i j, i ≤ n → j ≤ n → ∀ s t,
      s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      (arcs i).curve s = (arcs j).curve t → i = j ∧ s = t)
    (harg : ∀ k ≤ n, (arcs k).HasArgumentTurn)
    (havoid : ∀ k ≤ n, ∀ t ∈ Ioo (0 : ℝ) 1, (arcs k).curve t ∉ pointPunctures a y) :
    ∃ B : ℕ → PointRadialC1PlaneArc ha y,
      (B = arcs ∨ B = fun k => (arcs (n - k)).reverse) ∧
      (∀ k < n, (B k).curve 1 = (B (k + 1)).curve 0) ∧
      (B n).curve 1 = (B 0).curve 0 ∧
      (∀ i j, i ≤ n → j ≤ n → ∀ s t,
        s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
        (B i).curve s = (B j).curve t → i = j ∧ s = t) ∧
      (⋃ k ≤ n, (B k).curve '' Icc (0 : ℝ) 1) = (⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1) ∧
      ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
        Disjoint U V ∧ IsCompact (closure U) ∧
        U ∪ V = (⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1)ᶜ ∧
        frontier U = (⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1) ∧
        frontier V = (⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1) ∧
        ∃ θ : ℕ → ℝ, (∀ k ≤ n, 0 < θ k ∧ θ k < 2 * Real.pi) ∧
          (∀ k ≤ n, Nonempty (PointFiniteRadialCornerAt (fun i => (B i).curve) n k (θ k))) ∧
          (∀ k ≤ n, Complex.arg (deriv (B k).curve 0 /
            deriv (B (if k = 0 then n else k - 1)).curve 1) = Real.pi - θ k) ∧
          (∑ k ∈ Finset.range (n + 1), (Real.pi -
            (1 + coalescedPointExponent a y ((B k).curve 0) / 2) * θ k)) =
            2 * Real.pi + 2 * Real.pi * (∑ j, if y j ∈ U then a j / 2 else 0) := by
  classical
  let f : ℕ → ℝ → ℂ := fun k => (arcs k).curve
  have hfc : ∀ k ≤ n, Continuous (f k) := fun k _ => (arcs k).smooth.continuous
  obtain ⟨hF, hpF, hiF, _, himage⟩ := euclideanFiniteCornerPeriodize_properties f n hfc hv hclose hinj
  have hFclose : pointContinuousPeriodize (euclideanFiniteCornerArc f n) 0 =
      pointContinuousPeriodize (euclideanFiniteCornerArc f n) 1 := by simpa only [zero_add] using (hpF 0).symm
  obtain ⟨U, V, hU, hV, hUc, hVc, hdisj, hcover, hfrontU, hfrontV, hK, _, _⟩ :=
    jordan_separation_of_homeomorph Complex.orthonormalBasisOneI.repr.toHomeomorph
      _ hF.continuousOn hFclose hiF
  rw [himage] at hcover hfrontU hfrontV
  change U ∪ V = (⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1)ᶜ at hcover
  change frontier U = (⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1) at hfrontU
  change frontier V = (⋃ k ≤ n, (arcs k).curve '' Icc (0 : ℝ) 1) at hfrontV
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
  obtain ⟨θ, hθ, hD, hprincipal, hGB⟩ := exists_point_radial_finite_gauss_bonnet ha y B n hn hBv hBc hBi hBavoid
    hU hUc hV hVc hdisj hK hcoverB hvertexU hvertexV hw Ξ τ hΞ hτ hΞl hτl hΞturn ψ hψ hψl
  have hzero : (∑ k ∈ Finset.range (n + 1), ((τ k 1 - τ k 0) +
      ∑ j, (a j / 2) * (ψ j k 1 - ψ j k 0))) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have he : τ k 1 - τ k 0 = -(∑ j, (a j / 2) * (ψ j k 1 - ψ j k 0)) := htransport (idx k)
    linarith
  rw [hzero, zero_add] at hGB
  exact ⟨B, hBcase, hBv, hBc, hBi, hBcarrier, U, V, hU, hV, hUc, hVc, hdisj, hK,
    hcover, hfrontU, hfrontV, θ, hθ, hD, hprincipal, hGB⟩

end RepulsiveCoulomb
