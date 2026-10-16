module

public import LeanResearch.RepulsiveCoulomb.PointRetainedParallelReturnBudget

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. The actual marked attachment turn is nu(z)+nu(p).
Both p and z are omitted from the remaining old arc, and each positive atom is
charged at most once. This is finite signed accounting used by the actual cap
producer; it is not a replacement cap, first-return or direction certificate. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace RepulsiveCoulomb

theorem pointSignedPositiveMass_erase_two_add
    (ν α : ℂ→₀ℝ) {p z : ℂ} (hpz : p≠z) :
    (∑ x∈((pointSignedMarked ν α).erase z).erase p,signedBudgetPos (ν x))+
      signedBudgetPos (ν p)+signedBudgetPos (ν z)=pointSignedPositiveMass ν α := by
  have hfirst : (∑ x∈((pointSignedMarked ν α).erase z).erase p,signedBudgetPos (ν x))+
      signedBudgetPos (ν p)=pointSignedPositiveMassAway ν α z := by
    by_cases hp : p∈pointSignedMarked ν α
    · exact Finset.sum_erase_add ((pointSignedMarked ν α).erase z)
        (fun x ↦ signedBudgetPos (ν x)) (Finset.mem_erase.mpr ⟨hpz,hp⟩)
    · have hpe : p∉(pointSignedMarked ν α).erase z :=
        fun he ↦ hp (Finset.mem_of_mem_erase he)
      rw [Finset.erase_eq_of_notMem hpe,(pointSigned_eq_zero_off_marked hp).1,
        signedBudgetPos_zero,add_zero]
      rfl
  rw [hfirst]
  exact pointSignedPositiveMassAway_add ν α z

theorem retainedMarkedParallel_return_turn_sum_lt_two_pi
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (vertex : ι→ℂ) (turn : ι→ℝ) (oldBoundary : Set ℂ)
    {ν α : ℂ→₀ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    {p : ℂ} (hp : 0≤ν p) {start far : ι}
    (hvertex : Set.InjOn vertex (s:Set ι))
    (hstart : start∈s) (hfar : far∈s) (hne : start≠far)
    (hpstart : p≠vertex start)
    (hstartturn : turn start=ν p+ν (vertex start)) (hfarstrict : turn far<Real.pi)
    (holdAvoid : ∀ i∈s,i≠start→i≠far→vertex i∈oldBoundary→vertex i≠p)
    (hcoeff : ∀ i∈s,i≠start→i≠far→vertex i∈oldBoundary→turn i=ν (vertex i))
    (hnew : ∀ i∈s,i≠start→i≠far→vertex i∉oldBoundary→turn i≤0) :
    (∑ i∈s,turn i)<2*Real.pi := by
  let rest := (s.erase start).erase far
  let old := rest.filter (fun i ↦ vertex i∈oldBoundary)
  have hrest (i : ι) (hi : i∈rest) : i∈s ∧ i≠start ∧ i≠far := by
    obtain ⟨hif,his⟩ := Finset.mem_erase.mp hi
    obtain ⟨hia,hi⟩ := Finset.mem_erase.mp his
    exact ⟨hi,hia,hif⟩
  have holdsub : old⊆rest := Finset.filter_subset _ _
  have hdiscard : (∑ i∈rest,turn i)≤∑ i∈old,turn i := by
    apply Finset.sum_le_sum_of_subset_of_nonpos holdsub
    intro i hi hio
    obtain ⟨his,hia,hib⟩ := hrest i hi
    apply hnew i his hia hib
    intro hbd
    exact hio (Finset.mem_filter.mpr ⟨hi,hbd⟩)
  have hcoefficient : (∑ i∈old,turn i)=∑ i∈old,ν (vertex i) := by
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hir,hibd⟩ := Finset.mem_filter.mp hi
    obtain ⟨his,hia,hib⟩ := hrest i hir
    exact hcoeff i his hia hib hibd
  have hzavoid (i : ι) (hi : i∈old) : vertex i≠vertex start := by
    intro he
    exact (hrest i (holdsub hi)).2.1 (hvertex (hrest i (holdsub hi)).1 hstart he)
  have holdbound := old_arc_signed_sum_le_positive_mass_away old vertex
    (fun x ↦ ν x) ((pointSignedMarked ν α).erase (vertex start))
    (fun i hi j hj he ↦ hvertex (hrest i (holdsub hi)).1 (hrest j (holdsub hj)).1 he)
    (base:=p)
    (fun i hi ↦ holdAvoid i (hrest i (holdsub hi)).1
      (hrest i (holdsub hi)).2.1 (hrest i (holdsub hi)).2.2 (Finset.mem_filter.mp hi).2)
    (fun i hi hn ↦ (pointSigned_eq_zero_off_marked (fun hm ↦
      hn (Finset.mem_erase.mpr ⟨hzavoid i hi,hm⟩))).1.le)
  have hsplit := pointSignedPositiveMass_erase_two_add ν α hpstart
  have hpos : signedBudgetPos (ν p)=ν p := max_eq_left hp
  rw [hpos] at hsplit
  have hz : ν (vertex start) ≤ signedBudgetPos (ν (vertex start)) := le_max_left _ _
  have htotal := hbudget.positiveMass_le_pi
  have hfar' : far∈s.erase start := Finset.mem_erase.mpr ⟨hne.symm,hfar⟩
  have hsum1 := Finset.sum_erase_add s turn hstart
  have hsum2 := Finset.sum_erase_add (s.erase start) turn hfar'
  change (∑ i∈rest,turn i)+turn far=∑ i∈s.erase start,turn i at hsum2
  rw [hcoefficient] at hdiscard
  change (∑ i∈old,ν (vertex i))≤
    ∑ x∈((pointSignedMarked ν α).erase (vertex start)).erase p,signedBudgetPos (ν x) at holdbound
  linarith

theorem PointFirstReturnFiniteGBData.not_retainedMarkedParallel_return
    {m : ℕ} {a : Fin m→ℝ} {ha : ∀ j,0≤a j} {y : Fin m→ℂ}
    {arcs : ℕ→PointRadialC1PlaneArc ha y} {n : ℕ} {U V : Set ℂ}
    (D : PointFirstReturnFiniteGBData ha y arcs n U V)
    {ν α : ℂ→₀ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    {p : ℂ} (hp : 0≤ν p) (oldBoundary : Set ℂ) {start far : ℕ}
    (hstart : start≤n) (hfar : far≤n) (hne : start≠far)
    (hpstart : p≠(D.oriented start).curve 0)
    (hstartturn : Real.pi-
      (1+coalescedPointExponent a y ((D.oriented start).curve 0)/2)*D.angle start=
        ν p+ν ((D.oriented start).curve 0))
    (holdAvoid : ∀ i≤n,i≠start→i≠far→(D.oriented i).curve 0∈oldBoundary→
      (D.oriented i).curve 0≠p)
    (hcoeff : ∀ i≤n,i≠start→i≠far→(D.oriented i).curve 0∈oldBoundary→
      Real.pi-(1+coalescedPointExponent a y ((D.oriented i).curve 0)/2)*D.angle i=
        ν ((D.oriented i).curve 0))
    (hnew : ∀ i≤n,i≠start→i≠far→(D.oriented i).curve 0∉oldBoundary→
      Real.pi-(1+coalescedPointExponent a y ((D.oriented i).curve 0)/2)*D.angle i≤0) : False := by
  let vertex : ℕ→ℂ := fun i ↦ (D.oriented i).curve 0
  let turn : ℕ→ℝ := fun i ↦ Real.pi-(1+coalescedPointExponent a y (vertex i)/2)*D.angle i
  have hvertex : Set.InjOn vertex (Finset.range (n+1):Set ℕ) := by
    intro i hi j hj he
    exact (D.simple i j (by have := Finset.mem_range.mp hi;omega)
      (by have := Finset.mem_range.mp hj;omega) 0 0 (by norm_num) (by norm_num) he).1
  have hsum := retainedMarkedParallel_return_turn_sum_lt_two_pi
    (Finset.range (n+1)) vertex turn oldBoundary hbudget hp hvertex
    (Finset.mem_range.mpr (by omega : start<n+1))
    (Finset.mem_range.mpr (by omega : far<n+1)) hne hpstart hstartturn
    (D.physical_angle_pos_and_turn_lt_pi hfar).2
    (fun i hi ↦ holdAvoid i (by have := Finset.mem_range.mp hi;omega))
    (fun i hi ↦ hcoeff i (by have := Finset.mem_range.mp hi;omega))
    (fun i hi ↦ hnew i (by have := Finset.mem_range.mp hi;omega))
  exact (not_lt_of_ge D.two_pi_le_corner_turn_sum) hsum

end RepulsiveCoulomb
