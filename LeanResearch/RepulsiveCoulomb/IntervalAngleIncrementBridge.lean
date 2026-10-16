module

public import LeanResearch.RepulsiveCoulomb.JordanTurnAngleLift
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Tactic

@[expose] public section

/-! Uncompiled additive successor. Construct a full continuous radial lift,
compare its increments with actual subinterval lifts, and pass a uniform
interior-endpoint bound to the original endpoints by closedness. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exists_global_interval_argument_lift {γ : ℝ → ℂ} (hc : Continuous γ)
    (hn : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      Complex.exp ((φ t : ℂ) * Complex.I) = γ t / (‖γ t‖ : ℂ) := by
  obtain ⟨α, hα, hlift⟩ := exists_interval_euclidean_angle_lift
    (hc.comp continuous_subtype_val) (fun t => hn t t.2)
  refine ⟨IccExtend (show (0 : ℝ) ≤ 1 by norm_num) α,
    continuous_IccExtend_iff.mpr hα, ?_⟩
  intro t ht
  rw [IccExtend_of_mem _ _ ht]
  exact hlift ⟨t, ht⟩

theorem interval_argument_increment_eq {γ : ℝ → ℂ} {φ ψ : ℝ → ℝ} {s u : ℝ}
    (hsu : s ≤ u) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφlift : ∀ t ∈ Icc s u, Complex.exp ((φ t : ℂ) * Complex.I) = γ t / (‖γ t‖ : ℂ))
    (hψlift : ∀ t ∈ Icc s u, Complex.exp ((ψ t : ℂ) * Complex.I) = γ t / (‖γ t‖ : ℂ)) :
    φ u - φ s = ψ u - ψ s := by
  letI : PreconnectedSpace (Icc s u) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  apply euclidean_angle_lift_increment_eq
    (hφ.comp continuous_subtype_val) (hψ.comp continuous_subtype_val)
    (fun t => by
      apply Circle.ext
      simpa only [Circle.coe_exp, Function.comp_def] using
        (hφlift t t.2).trans (hψlift t t.2).symm)
    (⟨s, ⟨le_rfl, hsu⟩⟩ : Icc s u) (⟨u, ⟨hsu, le_rfl⟩⟩ : Icc s u)

theorem endpoint_angle_bound_of_interior_straddling_bounds
    {φ : ℝ → ℝ} {m K : ℝ} (hφ : Continuous φ) (hm : m ∈ Ioo (0 : ℝ) 1)
    (hbound : ∀ s ∈ Ioo (0 : ℝ) m, ∀ u ∈ Ioo m 1, |φ u - φ s| ≤ K) :
    |φ 1 - φ 0| ≤ K := by
  let S : Set (ℝ × ℝ) := {q | |φ q.2 - φ q.1| ≤ K}
  have hS : IsClosed S :=
    isClosed_le (((hφ.comp continuous_snd).sub (hφ.comp continuous_fst)).abs) continuous_const
  have hsub : (Ioo (0 : ℝ) m ×ˢ Ioo m 1) ⊆ S := by
    intro q hq
    exact hbound q.1 hq.1 q.2 hq.2
  have hclosed : closure (Ioo (0 : ℝ) m ×ˢ Ioo m 1) ⊆ S := hS.closure_subset_iff.mpr hsub
  change ((0, 1) : ℝ × ℝ) ∈ S
  apply hclosed
  rw [closure_prod_eq, closure_Ioo (a := (0 : ℝ)) (b := m) (ne_of_lt hm.1),
    closure_Ioo (a := m) (b := (1 : ℝ)) (ne_of_lt hm.2)]
  exact ⟨⟨le_rfl, hm.1.le⟩, ⟨hm.2.le, le_rfl⟩⟩

theorem pi_le_abs_of_complex_exp_eq_neg_one {x : ℝ}
    (hx : Complex.exp ((x : ℂ) * Complex.I) = -1) : Real.pi ≤ |x| := by
  by_contra hn
  have hlt : |x| < Real.pi := lt_of_not_ge hn
  have harg : Complex.arg (Complex.exp ((x : ℂ) * Complex.I)) = x :=
    Circle.arg_exp (abs_lt.mp hlt).1 (abs_lt.mp hlt).2.le
  rw [hx, Complex.arg_neg_one] at harg
  rw [← harg, abs_of_pos Real.pi_pos] at hlt
  exact lt_irrefl _ hlt

theorem pi_le_abs_opposite_argument_increment
    {z : ℂ} (hz : z ≠ 0) {φ₀ φ₁ : ℝ}
    (h₀ : Complex.exp ((φ₀ : ℂ) * Complex.I) = z / (‖z‖ : ℂ))
    (h₁ : Complex.exp ((φ₁ : ℂ) * Complex.I) = (-z) / (‖-z‖ : ℂ)) :
    Real.pi ≤ |φ₁ - φ₀| := by
  apply pi_le_abs_of_complex_exp_eq_neg_one
  have hnorm : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hnormalized : z / (‖z‖ : ℂ) ≠ 0 := div_ne_zero hz hnorm
  rw [show (((φ₁ - φ₀ : ℝ) : ℂ) * Complex.I) =
    (φ₁ : ℂ) * Complex.I - (φ₀ : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_sub, h₀, h₁, norm_neg, neg_div]
  simp [hnormalized]

end RepulsiveCoulomb
