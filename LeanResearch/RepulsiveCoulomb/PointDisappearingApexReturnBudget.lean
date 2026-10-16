module

public import LeanResearch.RepulsiveCoulomb.PointRetainedApexFirstReturnBudget
public import LeanResearch.RepulsiveCoulomb.PointDisappearingApexBudget

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. The disappearing-apex return contradiction uses
strict initial turn nu(z)+pi<pi and nonpositive remaining turns. It does NOT
apply the budget cap with beta=pi at z, which would incorrectly require
pi<=alpha(z). The proper old-end/cap side construction is a separate layer. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

theorem disappearingApex_return_turn_sum_lt_two_pi
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (turn : ι → ℝ)
    {start far : ι} (hstart : start∈s) (hfar : far∈s) (hne : start≠far)
    {nuz : ℝ} (hnuz : nuz<0) (hstartturn : turn start=nuz+Real.pi)
    (hfarstrict : turn far<Real.pi)
    (hother : ∀ i∈s,i≠start → i≠far → turn i≤0) :
    (∑ i∈s,turn i)<2*Real.pi := by
  let rest:=(s.erase start).erase far
  have hrest : (∑ i∈rest,turn i)≤0:=by
    apply Finset.sum_nonpos
    intro i hi
    obtain ⟨hif,his⟩:=Finset.mem_erase.mp hi
    obtain ⟨hia,hiS⟩:=Finset.mem_erase.mp his
    exact hother i hiS hia hif
  have hfar' : far∈s.erase start:=Finset.mem_erase.mpr ⟨hne.symm,hfar⟩
  have hsum1:=Finset.sum_erase_add s turn hstart
  have hsum2:=Finset.sum_erase_add (s.erase start) turn hfar'
  change (∑ i∈rest,turn i)+turn far=∑ i∈s.erase start,turn i at hsum2
  linarith

/-- Genuine finite radial GB data cannot be the cap of a later return.
The actual old compact arc must avoid the disappearing apex, derived using
the proper removed old end; otherwise the positive atom at y cannot be ignored.
No vertex injectivity is needed in this specialized nonpositive sum estimate. -/
theorem PointFirstReturnFiniteGBData.not_disappearingApex_return
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j,0≤a j} {y : Fin m → ℂ}
    {arcs : ℕ → PointRadialC1PlaneArc ha y} {n : ℕ} {U V : Set ℂ}
    (D : PointFirstReturnFiniteGBData ha y arcs n U V)
    {ν α : ℂ →₀ ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    {p z : ℂ} {β : ℝ} (hboundary : ν p=Real.pi-β)
    (hβπ : β≤Real.pi) (hβα : β≤α p) (hzneg : ν z<0)
    (oldBoundary : Set ℂ) {start far : ℕ}
    (hstart : start≤n) (hfar : far≤n) (hne : start≠far)
    (hstartturn : Real.pi-
      (1+coalescedPointExponent a y ((D.oriented start).curve 0)/2)*D.angle start=ν z+Real.pi)
    (holdAvoid : ∀ i≤n,i≠start → i≠far → (D.oriented i).curve 0∈oldBoundary →
      (D.oriented i).curve 0≠p)
    (hcoeff : ∀ i≤n,i≠start → i≠far → (D.oriented i).curve 0∈oldBoundary →
      Real.pi-(1+coalescedPointExponent a y ((D.oriented i).curve 0)/2)*D.angle i=
        ν ((D.oriented i).curve 0))
    (hnew : ∀ i≤n,i≠start → i≠far → (D.oriented i).curve 0∉oldBoundary →
      Real.pi-(1+coalescedPointExponent a y ((D.oriented i).curve 0)/2)*D.angle i≤0) : False := by
  let turn : ℕ → ℝ:=fun i ↦ Real.pi-
    (1+coalescedPointExponent a y ((D.oriented i).curve 0)/2)*D.angle i
  have hnonpos:=hbudget.full_angle_off_apex_nonpositive p hboundary hβπ hβα
  have hsum:=disappearingApex_return_turn_sum_lt_two_pi (Finset.range (n+1)) turn
    (Finset.mem_range.mpr (by omega : start<n+1))
    (Finset.mem_range.mpr (by omega : far<n+1)) hne hzneg hstartturn
    (D.physical_angle_pos_and_turn_lt_pi hfar).2 (by
      intro i hi hia hib
      have hin : i≤n:=by have := Finset.mem_range.mp hi; omega
      by_cases hold : (D.oriented i).curve 0∈oldBoundary
      · change Real.pi-(1+coalescedPointExponent a y ((D.oriented i).curve 0)/2)*D.angle i≤0
        rw [hcoeff i hin hia hib hold]
        exact hnonpos _ (holdAvoid i hin hia hib hold)
      · exact hnew i hin hia hib hold)
  exact (not_lt_of_ge D.two_pi_le_corner_turn_sum) hsum

end RepulsiveCoulomb
