module

public import LeanResearch.RepulsiveCoulomb.PointFiniteCornerTurn

@[expose] public section

/-! Identify the full directed sector from the ACTUAL physical outward
tangents. Positive, possibly unequal endpoint speeds cancel. This transports
same-chart minimizing-passage short/long bounds to the very theta used by
boundary-atom accounting, without adding an angle-compatibility field. -/
noncomputable section
namespace RepulsiveCoulomb

/-- The actual principal corner determines the opposite outward tangent
argument, independently of the two positive speeds. -/
theorem outward_tangent_argument_of_principal_corner {u v : ℂ}
    (hu : u ≠ 0) (hv : v ≠ 0) {θ : ℝ}
    (hcorner : Complex.arg (u / v) = Real.pi - θ) :
    Complex.arg ((-v) / u) = Complex.arg (Circle.exp θ : ℂ) := by
  have hn : 0 < ‖u / v‖ := norm_pos_iff.mpr (div_ne_zero hu hv)
  have hnc : (‖u / v‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
  have hpolar : (‖u / v‖ : ℂ) * (Circle.exp (Real.pi - θ) : ℂ) = u / v := by
    have h := Complex.norm_mul_exp_arg_mul_I (u / v)
    rw [hcorner] at h
    exact h
  have hphase : (Circle.exp (Real.pi - θ) : ℂ) * (Circle.exp θ : ℂ) = -1 := by
    rw [← Circle.coe_mul, ← Circle.exp_add, sub_add_cancel, Circle.coe_exp,
      Complex.exp_pi_mul_I]
  have halg : u * (Circle.exp θ : ℂ) = -((‖u / v‖ : ℂ) * v) := by
    calc
      u * (Circle.exp θ : ℂ) = ((u / v) * v) * (Circle.exp θ : ℂ) := by rw [div_mul_cancel₀ _ hv]
      _ = (((‖u / v‖ : ℂ) * (Circle.exp (Real.pi - θ) : ℂ)) * v) *
          (Circle.exp θ : ℂ) :=
        congrArg (fun z : ℂ => (z * v) * (Circle.exp θ : ℂ)) hpolar.symm
      _ = (‖u / v‖ : ℂ) *
          ((Circle.exp (Real.pi - θ) : ℂ) * (Circle.exp θ : ℂ)) * v := by ring
      _ = -((‖u / v‖ : ℂ) * v) := by rw [hphase]; ring
  have hsolve : (Circle.exp θ : ℂ) / (‖u / v‖ : ℂ) = (-v) / u := by
    apply (div_eq_div_iff hnc hu).mpr
    calc
      (Circle.exp θ : ℂ) * u = u * (Circle.exp θ : ℂ) := mul_comm _ _
      _ = -((‖u / v‖ : ℂ) * v) := halg
      _ = (-v) * (‖u / v‖ : ℂ) := by ring
  have hratio : (-v) / u = ((‖u / v‖⁻¹ : ℝ) : ℂ) * (Circle.exp θ : ℂ) := by
    rw [Complex.ofReal_inv, mul_comm, ← div_eq_mul_inv]
    exact hsolve.symm
  rw [hratio, Complex.arg_real_mul _ (inv_pos.mpr hn)]

/-- Only the actual absolute argument is needed for the short/long pair;
this formulation permits unequal norms of the physical tangent vectors. -/
theorem cone_directed_sector_angles_of_abs_argument {α θ : ℝ} {u v : ℂ}
    (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi)
    (harg : |Complex.arg (v / u)| = min θ (2 * Real.pi - θ)) :
    ((α + 1) * θ = coneShortSectorAngle α u v ∧
      (α + 1) * (2 * Real.pi - θ) = coneLongSectorAngle α u v) ∨
    ((α + 1) * θ = coneLongSectorAngle α u v ∧
      (α + 1) * (2 * Real.pi - θ) = coneShortSectorAngle α u v) := by
  have hs : coneShortSectorAngle α u v = (α + 1) * min θ (2 * Real.pi - θ) := by
    rw [coneShortSectorAngle, harg]
  by_cases hθπ : θ ≤ Real.pi
  · rw [min_eq_left (by linarith)] at hs
    refine Or.inl ⟨hs.symm, ?_⟩
    rw [coneLongSectorAngle, hs]
    ring
  · rw [min_eq_right (by linarith)] at hs
    refine Or.inr ⟨?_, hs.symm⟩
    rw [coneLongSectorAngle, hs]
    ring

/-- The theta appearing in the actual boundary argument is one of the two
cone sectors of the physical outward tangents: incoming outward first,
outgoing second. No equality of their speeds is required. -/
theorem PointFiniteRadialCornerAt.physical_directed_sector_angles
    {f : ℕ → ℝ → ℂ} {n k : ℕ} {θ : ℝ} (D : PointFiniteRadialCornerAt f n k θ)
    (hf : ∀ i ≤ n, ContDiff ℝ 1 (f i))
    (hreg : ∀ i ≤ n, ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv (f i) t ≠ 0)
    (α : ℝ) :
    ((α + 1) * θ = coneShortSectorAngle α (-deriv (f (D.order n)) 1) (deriv (f k) 0) ∧
      (α + 1) * (2 * Real.pi - θ) = coneLongSectorAngle α (-deriv (f (D.order n)) 1) (deriv (f k) 0)) ∨
    ((α + 1) * θ = coneLongSectorAngle α (-deriv (f (D.order n)) 1) (deriv (f k) 0) ∧
      (α + 1) * (2 * Real.pi - θ) = coneShortSectorAngle α (-deriv (f (D.order n)) 1) (deriv (f k) 0)) := by
  have hk : k ≤ n := by simpa only [D.order_zero] using D.order_le 0 (Nat.zero_le n)
  have hu := hreg k hk 0 (by norm_num)
  have hv := hreg (D.order n) (D.order_le n le_rfl) 1 (by norm_num)
  have harg := outward_tangent_argument_of_principal_corner hu hv (D.principal_turn_eq hf)
  have hinverse : deriv (f k) 0 / (-deriv (f (D.order n)) 1) =
      ((-deriv (f (D.order n)) 1) / deriv (f k) 0)⁻¹ := by
    rw [inv_div]
  have habs : |Complex.arg (deriv (f k) 0 / (-deriv (f (D.order n)) 1))| =
      min θ (2 * Real.pi - θ) := by
    rw [hinverse, Complex.abs_arg_inv, harg, pointRadialSector_principal_abs D.angle_pos D.angle_lt]
  exact cone_directed_sector_angles_of_abs_argument D.angle_pos D.angle_lt habs

/-- Both actual physical sector-turn bounds transfer to the exact inside
sector used in full boundary Gauss–Bonnet. -/
theorem PointFiniteRadialCornerAt.directed_turn_nonpos
    {f : ℕ → ℝ → ℂ} {n k : ℕ} {θ α : ℝ} (D : PointFiniteRadialCornerAt f n k θ)
    (hf : ∀ i ≤ n, ContDiff ℝ 1 (f i))
    (hreg : ∀ i ≤ n, ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv (f i) t ≠ 0)
    (hshort : Real.pi - coneShortSectorAngle α (-deriv (f (D.order n)) 1) (deriv (f k) 0) ≤ 0)
    (hlong : Real.pi - coneLongSectorAngle α (-deriv (f (D.order n)) 1) (deriv (f k) 0) ≤ 0) :
    Real.pi - (α + 1) * θ ≤ 0 := by
  rcases D.physical_directed_sector_angles hf hreg α with h | h
  · rwa [h.1]
  · rwa [h.1]

end RepulsiveCoulomb
