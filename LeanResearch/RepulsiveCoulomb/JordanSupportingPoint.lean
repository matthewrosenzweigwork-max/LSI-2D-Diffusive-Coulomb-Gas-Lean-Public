module

public import LeanResearch.RepulsiveCoulomb.JordanSmoothSupportedTurn
public import Mathlib.Algebra.Field.Periodic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

/-! Construct a genuine supporting point of a regular periodic curve using
compactness and Fermat's theorem. No supporting-point certificate is input.
Records-only candidate: compilation and admission pending. -/
noncomputable section
open Set
open scoped Topology
namespace RepulsiveCoulomb

theorem periodic_loop_deriv_periodic {γ : ℝ → ℂ} (hp : Function.Periodic γ 1) :
    Function.Periodic (deriv γ) 1 := by
  intro t
  have heq : (fun s : ℝ => γ (s + 1)) = γ := funext hp
  have h := congrArg (fun f : ℝ → ℂ => deriv f t) heq
  simpa only [deriv_comp_add_const] using h

theorem periodic_loop_regular_everywhere {γ : ℝ → ℂ} (hp : Function.Periodic γ 1)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0) :
    ∀ t : ℝ, deriv γ t ≠ 0 := by
  intro t
  obtain ⟨s, hs, hts⟩ := (periodic_loop_deriv_periodic hp).exists_mem_Ico₀ (by norm_num) t
  rw [hts]
  exact hreg s ⟨hs.1, hs.2.le⟩

/-- A regular periodic curve has a horizontal support point where the actual
tangent is a nonzero real vector; the whole curve is above that support line. -/
theorem exists_regular_periodic_horizontal_support {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0) :
    ∃ t₀ ∈ Icc (0 : ℝ) 1,
      (deriv γ t₀).im = 0 ∧ (deriv γ t₀).re ≠ 0 ∧
      ∀ t : ℝ, 0 ≤ (γ t - γ t₀).im := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩)
    ((Complex.continuous_im.comp hγ.continuous).continuousOn)
  have hglobal : ∀ t : ℝ, (γ t₀).im ≤ (γ t).im := by
    intro t
    obtain ⟨s, hs, hts⟩ := hp.exists_mem_Ico₀ (by norm_num) t
    rw [hts]
    exact hmin ⟨hs.1, hs.2.le⟩
  have hlocal : IsLocalMin (fun t => (γ t).im) t₀ := by
    apply (show IsMinOn (fun t => (γ t).im) univ t₀ from fun t _ => hglobal t).isLocalMin
    exact Filter.univ_mem
  have himDeriv : HasDerivAt (fun t => (γ t).im) (deriv γ t₀).im t₀ :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t₀
      (hγ.differentiable (by norm_num) t₀).hasDerivAt
  have him : (deriv γ t₀).im = 0 := himDeriv.deriv.symm.trans hlocal.deriv_eq_zero
  have hre : (deriv γ t₀).re ≠ 0 := by
    intro hz
    exact hreg t₀ ht₀ (Complex.ext hz him)
  exact ⟨t₀, ht₀, him, hre, fun t => by simpa only [Complex.sub_im] using sub_nonneg.mpr (hglobal t)⟩

/-- Simplicity in one half-open period transports to any shifted unit period
whose shift lies in the standard closed period. -/
theorem periodic_simple_loop_shift_injOn {γ : ℝ → ℂ}
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    InjOn (fun t => γ (t + a)) (Ico (0 : ℝ) 1) := by
  intro s hs t ht heq
  by_cases hsa : s + a < 1 <;> by_cases hta : t + a < 1
  · have h := hinj ⟨by linarith [hs.1, ha.1], hsa⟩
      ⟨by linarith [ht.1, ha.1], hta⟩ heq
    linarith
  · have het : γ (s + a) = γ (t + a - 1) := heq.trans (hp.sub_eq _).symm
    have h := hinj ⟨by linarith [hs.1, ha.1], hsa⟩
      ⟨by linarith, by linarith [ht.2, ha.2]⟩ het
    linarith [hs.1, ht.2]
  · have het : γ (s + a - 1) = γ (t + a) := (hp.sub_eq _).trans heq
    have h := hinj ⟨by linarith, by linarith [hs.2, ha.2]⟩
      ⟨by linarith [ht.1, ha.1], hta⟩ het
    linarith [ht.1, hs.2]
  · have het : γ (s + a - 1) = γ (t + a - 1) :=
      (hp.sub_eq _).trans (heq.trans (hp.sub_eq _).symm)
    have h := hinj ⟨by linarith, by linarith [hs.2, ha.2]⟩
      ⟨by linarith, by linarith [ht.2, ha.2]⟩ het
    linarith

theorem periodic_simple_loop_injOn_Ioc {γ : ℝ → ℂ}
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1)) :
    InjOn γ (Ioc (0 : ℝ) 1) := by
  intro s hs t ht heq
  by_cases hs1 : s = 1 <;> by_cases ht1 : t = 1
  · exact hs1.trans ht1.symm
  · subst s
    have h10 : γ 1 = γ 0 := by simpa using hp 0
    have h := hinj (show (0 : ℝ) ∈ Ico 0 1 by norm_num)
      ⟨ht.1.le, lt_of_le_of_ne ht.2 ht1⟩ (h10.symm.trans heq)
    linarith [ht.1]
  · subst t
    have h10 : γ 1 = γ 0 := by simpa using hp 0
    have h := hinj ⟨hs.1.le, lt_of_le_of_ne hs.2 hs1⟩
      (show (0 : ℝ) ∈ Ico 0 1 by norm_num) (heq.trans h10)
    linarith [hs.1]
  · exact hinj ⟨hs.1.le, lt_of_le_of_ne hs.2 hs1⟩
      ⟨ht.1.le, lt_of_le_of_ne ht.2 ht1⟩ heq

end RepulsiveCoulomb
