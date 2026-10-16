module

public import LeanResearch.RepulsiveCoulomb.PointUniformSuperPoincare
public import LeanResearch.RepulsiveCoulomb.DyadicTruncationEnergy

@[expose] public section

/-! The actual smooth dyadic truncations preserve the original core, with an
L1 bound by the untruncated square mass. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

def pointCoreSmoothTruncation {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (b : ℝ) (hb : 0 < b) (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    TestFunction (pointDomain a y) ℝ ⊤ :=
  ⟨fun x => smoothDyadicTruncation b (φ x),
    (smoothDyadicTruncation_contDiff b).comp φ.contDiff,
    φ.hasCompactSupport.comp_left (smoothDyadicTruncation_zero hb hb.le),
    (tsupport_comp_subset (smoothDyadicTruncation_zero hb hb.le) (φ : ℂ → ℝ)).trans φ.tsupport_subset⟩

theorem smoothDyadicTruncation_le_square {b : ℝ} (hb : 0 < b) (t : ℝ) :
    smoothDyadicTruncation b t ≤ t ^ 2 / b := by
  by_cases ht : t ≤ b
  · rw [smoothDyadicTruncation_zero hb ht]
    positivity
  · have htb : b < t := lt_of_not_ge ht
    apply (smoothDyadicTruncation_le hb.le t).trans
    apply (le_div_iff₀ hb).mpr
    nlinarith

theorem pointCore_truncation_l1_le_mass {m : ℕ} {γ b : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hb : 0 < b)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    (∫ x, |pointCoreSmoothTruncation b hb φ x| ∂pointMeasure γ a y) ≤
      (∫ x, φ x ^ 2 ∂pointMeasure γ a y) / b := by
  let _ := pointMeasure_isProbability hγ ha y
  let ψ := pointCoreSmoothTruncation b hb φ
  have hψ : Integrable (fun x : ℂ => |ψ x|) (pointMeasure γ a y) :=
    (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).abs
  have hs : HasCompactSupport (fun x : ℂ => φ x ^ 2) :=
    φ.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hi : Integrable (fun x : ℂ => φ x ^ 2) (pointMeasure γ a y) :=
    (φ.continuous.pow 2).integrable_of_hasCompactSupport hs
  rw [← integral_div]
  apply integral_mono hψ (hi.div_const b)
  intro x
  change |smoothDyadicTruncation b (φ x)| ≤ φ x ^ 2 / b
  rw [abs_of_nonneg (smoothDyadicTruncation_nonneg hb.le _)]
  exact smoothDyadicTruncation_le_square hb _

end RepulsiveCoulomb
