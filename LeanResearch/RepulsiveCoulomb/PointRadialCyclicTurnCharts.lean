module

public import LeanResearch.RepulsiveCoulomb.JordanFiniteCornerOrientedTurn
public import LeanResearch.RepulsiveCoulomb.PointRadialC1HalfOpenCorners

@[expose] public section

/-! Instantiate the original finite-corner oriented-turn theorem with the
actual chosen physical charts carried by point-metric radial C¹ macro-arcs.
Common charts, inverse noncriticality and noncuspidality are proved from the
constructed arc data and actual half-open simplicity. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

/-- The actual inverse chosen chart has nonzero complex derivative everywhere
on its actual target. Differentiate the literal local inverse identity. -/
theorem pointChosenSmoothRadialChart_inverse_deriv_ne_zero
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ)
    {z : ℂ} (hz : z ∈ (pointChosenSmoothRadialChart ha y p).target) :
    deriv (pointChosenSmoothRadialChart ha y p).symm z ≠ 0 := by
  let e := pointChosenSmoothRadialChart ha y p
  obtain ⟨_, _, _, _, hInv, hForward, _⟩ := pointChosenSmoothRadialChart_spec ha y p
  have hs : e.symm z ∈ e.source := e.symm.mapsTo hz
  have hD := ((hForward _ hs).1.differentiableAt.hasDerivAt).comp z
    ((hInv z hz).differentiableAt.hasDerivAt)
  have heq : (e ∘ e.symm) =ᶠ[𝓝 z] (fun w : ℂ => w) := by
    filter_upwards [e.open_target.mem_nhds hz] with w hw
    exact e.right_inv hw
  have hId := hD.congr_of_eventuallyEq heq.symm
  have hone : deriv e (e.symm z) * deriv e.symm z = 1 := by
    simpa only [deriv_id''] using hId.deriv.symm
  intro hzero
  rw [hzero, mul_zero] at hone
  exact zero_ne_one hone

/-- Every actual cyclic macro-family supplies all the geometric data required
by the finite-corner theorem. The local short-turn condition is DERIVED from
the actual disjoint half-open traces, also for a two-edge bigon. -/
theorem point_radial_C1_cycle_oriented_total_turn
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (hσ : ∀ i, σ i ≠ i)
    (n : ℕ) (enumeration : ℕ → ι)
    (heinj : ∀ j ≤ n, ∀ k ≤ n, enumeration j = enumeration k → j = k)
    (hesurj : ∀ i, ∃ k ≤ n, enumeration k = i)
    (henext : ∀ k < n, σ (enumeration k) = enumeration (k + 1))
    (heclose : σ (enumeration n) = enumeration 0)
    (arcs : ι → PointRadialC1PlaneArc ha y)
    (hend : ∀ i, (arcs i).finish = (arcs (σ i)).start)
    (hdisj : Pairwise (fun i j => Disjoint
      ((arcs i).curve '' Ico (0 : ℝ) 1) ((arcs j).curve '' Ico (0 : ℝ) 1)))
    (w : ℂ) (hw : w ∉ ⋃ i, (arcs i).curve '' Icc (0 : ℝ) 1)
    (θ ψ : ι → Icc (0 : ℝ) 1 → ℝ)
    (hθ : ∀ i, Continuous (θ i)) (hψ : ∀ i, Continuous (ψ i))
    (hθl : ∀ i t, Complex.exp ((θ i t : ℂ) * Complex.I) =
      deriv (arcs i).curve t / (‖deriv (arcs i).curve t‖ : ℂ))
    (hψl : ∀ i t, Complex.exp ((ψ i t : ℂ) * Complex.I) =
      ((arcs i).curve t - w) / (‖(arcs i).curve t - w‖ : ℂ))
    (hpoint : (∑ i, (ψ i 1 - ψ i 0)) ≠ 0) :
    (∑ i, (θ i 1 - θ i 0)) +
      (∑ i, Complex.arg (deriv (arcs i).curve 0 / deriv (arcs (σ.symm i)).curve 1)) =
        ∑ i, (ψ i 1 - ψ i 0) := by
  let chart := fun i => pointChosenSmoothRadialChart ha y (arcs i).start
  let V := fun i => (chart i).target
  let H : ι → ℂ → ℂ := fun i => (chart i).symm
  let u := fun i => -(arcs (σ.symm i)).rightVector
  let v := fun i => (arcs i).leftVector
  have hspec (i : ι) := pointChosenSmoothRadialChart_spec ha y (arcs i).start
  have h0V (i : ι) : (0 : ℂ) ∈ V i := by
    obtain ⟨_, _, hep, hp, _, _, _⟩ := hspec i
    exact hep ▸ (chart i).mapsTo hp
  have hH (i : ι) : AnalyticOnNhd ℂ (H i) (V i) := by
    obtain ⟨_, _, _, _, hInv, _, _⟩ := hspec i
    exact hInv
  have hH0 (i : ι) : H i 0 = (arcs i).curve 0 := by
    obtain ⟨_, _, hep, hp, _, _, _⟩ := hspec i
    change (chart i).symm 0 = (arcs i).start
    have hep' : chart i (arcs i).start = 0 := hep
    rw [← hep']
    exact (chart i).left_inv hp
  have hjoin (i : ι) : (arcs i).curve 1 = (arcs (σ i)).curve 0 := hend i
  have hprejoin (i : ι) : (arcs (σ.symm i)).curve 1 = (arcs i).curve 0 := by
    simpa only [σ.apply_symm_apply] using hjoin (σ.symm i)
  have hratio (i : ι) : v i / u i ∈ Complex.slitPlane := by
    have hne : σ.symm i ≠ i := by
      intro he
      have hs := congrArg σ he
      rw [σ.apply_symm_apply] at hs
      exact hσ i hs.symm
    have hright := (arcs (σ.symm i)).right_radial
    rw [hprejoin i] at hright
    have hno := radial_corner_not_positive_multiple_of_halfOpen_disjoint
      (hdisj hne) hright (arcs i).left_radial
    have hr := neg_ratio_mem_slitPlane_of_not_positive_multiple
      (arcs (σ.symm i)).rightVector_ne (arcs i).leftVector_ne hno
    simpa only [u, v, div_neg, neg_div] using hr
  have hincoming (i : ι) : (fun t => (arcs i).curve (1 + t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => H (σ i) (t • u (σ i))) := by
    have ht : Tendsto (fun t : ℝ => 1 + t) (𝓝 0) (𝓝 1) := by
      have hc : Continuous (fun t : ℝ => 1 + t) := by fun_prop
      simpa only [add_zero] using hc.tendsto 0
    have h := (arcs i).right_radial.comp_tendsto ht
    filter_upwards [h] with t he
    change (arcs i).curve (1 + t) =
      (pointChosenSmoothRadialChart ha y (arcs (σ i)).start).symm
        (t • -(arcs (σ.symm (σ i))).rightVector)
    rw [σ.symm_apply_apply]
    change (arcs i).curve (1 + t) =
      (pointChosenSmoothRadialChart ha y ((arcs (σ i)).curve 0)).symm
        (t • -(arcs i).rightVector)
    rw [← hjoin i]
    simpa only [Function.comp_def, show (1 : ℝ) - (1 + t) = -t by ring,
      neg_smul, smul_neg] using he
  have hjoint : ∀ i j s t, s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      (arcs i).curve s = (arcs j).curve t → i = j ∧ s = t := by
    intro i j s t hs ht he
    by_cases hij : i = j
    · subst j
      exact ⟨rfl, (arcs i).injective (Ico_subset_Icc_self hs) (Ico_subset_Icc_self ht) he⟩
    · exact (Set.disjoint_left.mp (hdisj hij) ⟨s, hs, rfl⟩ ⟨t, ht, he.symm⟩).elim
  exact finite_radial_jordan_oriented_total_turn σ hσ n enumeration heinj hesurj henext heclose
    (fun i => (arcs i).curve) (fun i => (arcs i).smooth) hjoin (fun i => (arcs i).regular)
    hjoint w hw V (fun i => (chart i).open_target) h0V H hH
    (fun i z hz => pointChosenSmoothRadialChart_inverse_deriv_ne_zero ha y (arcs i).start hz)
    (fun i => (chart i).symm.injOn) hH0 u v
    (fun i => neg_ne_zero.mpr (arcs (σ.symm i)).rightVector_ne) hratio
    (fun i => (arcs i).left_radial) hincoming θ ψ hθ hψ hθl hψl hpoint

end RepulsiveCoulomb
