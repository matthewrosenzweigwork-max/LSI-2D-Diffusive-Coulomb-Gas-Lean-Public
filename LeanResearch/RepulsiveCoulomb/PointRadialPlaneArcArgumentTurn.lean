module

public import LeanResearch.RepulsiveCoulomb.PointRadialC1ArcTransport
public import LeanResearch.RepulsiveCoulomb.PointRadialC1BigonSimplicity

@[expose] public section

/-! Transport the actual source-geodesic argument identity through the
forgetful plane-arc adapter and reversal. Reversal retains all endpoint
limits and adds pi to the reversed tangent lift. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

/-- Actual continuous tangent and active point lifts on one plane macro-arc,
with the conformal geodesic turn identity. This property is constructed from
the original source geodesic below. -/
def PointRadialC1PlaneArc.HasArgumentTurn
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    (e : PointRadialC1PlaneArc ha y) : Prop :=
  ∃ θ : Icc (0 : ℝ) 1 → ℝ, ∃ ψ : Fin m → Icc (0 : ℝ) 1 → ℝ,
    Continuous θ ∧ (∀ j, Continuous (ψ j)) ∧
    (∀ u, Complex.exp ((θ u : ℂ) * Complex.I) =
      deriv e.curve u / (‖deriv e.curve u‖ : ℂ)) ∧
    (∀ j, a j ≠ 0 → ∀ u : Icc (0 : ℝ) 1, u.1 ∈ Ioo (0 : ℝ) 1 →
      Complex.exp ((ψ j u : ℂ) * Complex.I) =
        (e.curve u - y j) / (‖e.curve u - y j‖ : ℂ)) ∧
    θ 1 - θ 0 = -(∑ j, (a j / 2) * (ψ j 1 - ψ j 0))

/-- Forgetting the source interval does not lose the constructed turn data. -/
theorem PointRadialC1ArcPiece.toPlane_hasArgumentTurn
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {γ : Icc (0 : ℝ) 1 → ℂ} (e : PointRadialC1ArcPiece ha y γ)
    {p q : ℂ} (hpq : p ≠ q) (h0 : γ ⟨0, by norm_num⟩ = p)
    (hd : ∀ v w, (pointSmoothConformalEDist a y (γ v) (γ w)).toReal =
      |w.1 - v.1| * (pointSmoothConformalEDist a y p q).toReal) :
    e.toPlane.HasArgumentTurn :=
  e.exists_argument_turn hpq h0 hd

/-- Reversal negates both the tangent increment and every point increment.
The added pi changes the tangent direction to the actual reversed velocity. -/
theorem PointRadialC1PlaneArc.HasArgumentTurn.reverse
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {e : PointRadialC1PlaneArc ha y} (he : e.HasArgumentTurn) :
    e.reverse.HasArgumentTurn := by
  obtain ⟨θ, ψ, hθ, hψ, hθl, hψl, hturn⟩ := he
  let Θ : Icc (0 : ℝ) 1 → ℝ := fun t => θ (unitInterval.symm t) + Real.pi
  let Ψ : Fin m → Icc (0 : ℝ) 1 → ℝ := fun j t => ψ j (unitInterval.symm t)
  refine ⟨Θ, Ψ, (hθ.comp unitInterval.continuous_symm).add continuous_const,
    fun j => (hψ j).comp unitInterval.continuous_symm, ?_, ?_, ?_⟩
  · intro t
    change Complex.exp (((θ (unitInterval.symm t) + Real.pi : ℝ) : ℂ) * Complex.I) =
      deriv (fun s : ℝ => e.curve (1 - s)) t /
        (‖deriv (fun s : ℝ => e.curve (1 - s)) t‖ : ℂ)
    simp only [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I,
      mul_neg_one, deriv_comp_const_sub, norm_neg, neg_div]
    exact congrArg Neg.neg (hθl (unitInterval.symm t))
  · intro j hj t ht
    exact hψl j hj (unitInterval.symm t)
      (by constructor <;> change _ < _ <;> simp only [unitInterval.coe_symm_eq] <;>
        linarith [ht.1, ht.2])
  · change (θ (unitInterval.symm 1) + Real.pi) -
      (θ (unitInterval.symm 0) + Real.pi) =
        -(∑ j, (a j / 2) * (ψ j (unitInterval.symm 1) - ψ j (unitInterval.symm 0)))
    rw [unitInterval.symm_one, unitInterval.symm_zero]
    have hsum : (∑ j, (a j / 2) * (ψ j 0 - ψ j 1)) =
        -(∑ j, (a j / 2) * (ψ j 1 - ψ j 0)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum]
    linarith

end RepulsiveCoulomb
