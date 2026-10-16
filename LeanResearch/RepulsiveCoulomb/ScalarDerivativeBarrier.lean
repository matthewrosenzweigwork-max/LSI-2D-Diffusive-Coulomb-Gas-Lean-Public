module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

@[expose] public section

/-!
UNCOMPILED ADDITIVE DRAFT, 2026-10-02. No accepted-source or inventory claim.

One-sided scalar barriers used in the exterior visibility proof. The proof uses
the last point in a compact sublevel set and a genuine mean-value theorem. It
does not infer an invariant region from a derivative sign merely at first contact.
-/

noncomputable section
open Set Filter

namespace RepulsiveCoulomb

theorem scalar_upper_barrier_of_deriv_neg_above
    {f : ℝ → ℝ} {a b K : ℝ} (hf : Continuous f) (hstart : f a ≤ K)
    (hderiv : ∀ u ∈ Ioo a b, K < f u → deriv f u < 0) :
    ∀ t ∈ Icc a b, f t ≤ K := by
  intro t ht
  by_contra hnot
  have htval : K < f t := lt_of_not_ge hnot
  let S : Set ℝ := Icc a t ∩ {u | f u ≤ K}
  have hScompact : IsCompact S :=
    isCompact_Icc.inter_right (isClosed_le hf continuous_const)
  have hSne : S.Nonempty := ⟨a, ⟨⟨le_rfl, ht.1⟩, hstart⟩⟩
  obtain ⟨x, hxS, hxmax⟩ := hScompact.exists_isGreatest hSne
  have hx : a ≤ x ∧ x ≤ t := hxS.1
  have hxval : f x ≤ K := hxS.2
  have hxt : x < t := lt_of_le_of_ne hx.2 (by
    intro h
    rw [h] at hxval
    linarith)
  have habove (u : ℝ) (hu : u ∈ Ioo x t) : K < f u := by
    by_contra hn
    have huS : u ∈ S :=
      ⟨⟨hx.1.trans hu.1.le, hu.2.le⟩, le_of_not_gt hn⟩
    have hux := hxmax huS
    linarith [hu.1]
  have hanti : StrictAntiOn f (Icc x t) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hf.continuousOn
    intro u hu
    have hu' : u ∈ Ioo x t := by simpa only [interior_Icc] using hu
    exact hderiv u ⟨hx.1.trans_lt hu'.1, hu'.2.trans_le ht.2⟩ (habove u hu')
  have hdrop := hanti (show x ∈ Icc x t from ⟨le_rfl, hxt.le⟩)
    (show t ∈ Icc x t from ⟨hxt.le, le_rfl⟩) hxt
  linarith

theorem scalar_lower_barrier_of_deriv_pos_below
    {f : ℝ → ℝ} {a b K : ℝ} (hf : Continuous f) (hstart : K ≤ f a)
    (hderiv : ∀ u ∈ Ioo a b, f u < K → 0 < deriv f u) :
    ∀ t ∈ Icc a b, K ≤ f t := by
  have h := scalar_upper_barrier_of_deriv_neg_above
    (f := fun u => -f u) (a := a) (b := b) (K := -K) hf.neg (by linarith) ?_
  · intro t ht
    have h' := h t ht
    linarith
  · intro u hu hval
    have hpos : 0 < deriv f u := hderiv u hu (by linarith)
    have hdiff : DifferentiableAt ℝ f u :=
      differentiableAt_of_deriv_ne_zero hpos.ne'
    have hneg : HasDerivAt (fun v => -f v) (-(deriv f u)) u := by
      convert! hdiff.hasDerivAt.neg using 1 <;> rfl
    have heq : deriv (fun v => -f v) u = -(deriv f u) := hneg.deriv
    rw [heq]
    linarith

end RepulsiveCoulomb
