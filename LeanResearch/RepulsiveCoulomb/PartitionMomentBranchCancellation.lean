module

public import LeanResearch.RepulsiveCoulomb.PartitionMomentBranchDiagrams

@[expose] public section

/-! Signed singleton cancellation under an actual finite product probability.
Fubini is applied only with the absolute integrability proved in Diagrams.
The coordinate split is the measure-preserving `piFinSuccAbove` equivalence.
Records-only; no compiler has been invoked by this author. -/

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace RepulsiveCoulomb

variable {X : Type*} [MeasurableSpace X]

/-- An integrable function with identically zero coordinate integrals has zero
integral under the genuine finite product law. -/
theorem partitionMoment_integral_zero_of_coordinate {N : ℕ}
    {μ : Measure X} [IsProbabilityMeasure μ]
    (f : (Fin N → X) → ℝ)
    (hf : Integrable f (Measure.pi (fun _ : Fin N => μ)))
    (v : Fin N)
    (hzero : ∀ x, (∫ y, f (Function.update x v y) ∂μ) = 0) :
    (∫ x, f x ∂Measure.pi (fun _ : Fin N => μ)) = 0 := by
  classical
  cases N with
  | zero => exact Fin.elim0 v
  | succ n =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) v
      have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) v
      have hmpi := MeasurePreserving.symm e hmp
      have hfi : Integrable (fun z : X × (Fin n → X) => f (e.symm z))
          (μ.prod (Measure.pi (fun _ : Fin n => μ))) :=
        hmpi.integrable_comp_of_integrable hf
      haveI : Nonempty X := nonempty_of_isProbabilityMeasure μ
      let x0 : X := Classical.choice (inferInstance : Nonempty X)
      calc
        (∫ x, f x ∂Measure.pi (fun _ : Fin (n + 1) => μ)) =
            ∫ z : X × (Fin n → X), f (e.symm z)
              ∂μ.prod (Measure.pi (fun _ : Fin n => μ)) :=
          (hmpi.integral_comp' f).symm
        _ = ∫ z : Fin n → X, ∫ y : X, f (e.symm (y, z)) ∂μ
            ∂Measure.pi (fun _ : Fin n => μ) := integral_prod_symm _ hfi
        _ = ∫ _z : Fin n → X, (0 : ℝ) ∂Measure.pi (fun _ : Fin n => μ) := by
          apply integral_congr_ae
          filter_upwards [] with z
          change (∫ y : X, f (v.insertNth y z) ∂μ) = 0
          simpa only [Fin.update_insertNth] using hzero (v.insertNth x0 z)
        _ = 0 := integral_zero _ _

/-- If a vertex has exactly one incident edge slot, all other factors are
independent of its coordinate and the remaining factor has zero row integral. -/
theorem partitionMomentDiagram_coordinate_zero {N p : ℕ}
    {μ : Measure X} (G : X → X → ℝ)
    (hsymm : ∀ x y, G x y = G y x)
    (hcenter : ∀ z, (∫ y, G z y ∂μ) = 0)
    (e : Fin p → Fin N × Fin N) (hloop : ∀ j, (e j).1 ≠ (e j).2)
    (v : Fin N) (hdegree : equilibriumDiagramDegree e v = 1)
    (x : Fin N → X) :
    (∫ y, partitionMomentDiagram G e (Function.update x v y) ∂μ) = 0 := by
  classical
  let t := partitionMomentIncident (fun j => (e j).1) (fun j => (e j).2)
    Finset.univ v
  have htcard : t.card = 1 :=
    (partitionMomentIncident_card_eq_degree e hloop v).trans hdegree
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp htcard
  have hjt : j ∈ t := by rw [hj]; exact Finset.mem_singleton_self _
  have hjincident : (e j).1 = v ∨ (e j).2 = v := (Finset.mem_filter.mp hjt).2
  have hother (k : Fin p) (hk : k ∈ (Finset.univ : Finset (Fin p)).erase j) :
      (e k).1 ≠ v ∧ (e k).2 ≠ v := by
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    have hn : k ∉ t := by simpa only [hj, Finset.mem_singleton] using hkj
    constructor
    · intro ha
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ha⟩)
    · intro hb
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hb⟩)
  let R : ℝ := ∏ k ∈ (Finset.univ : Finset (Fin p)).erase j,
    G (x (e k).1) (x (e k).2)
  have hrest (y : X) :
      (∏ k ∈ (Finset.univ : Finset (Fin p)).erase j,
        G ((Function.update x v y) (e k).1) ((Function.update x v y) (e k).2)) = R := by
    apply Finset.prod_congr rfl
    intro k hk
    simp only [Function.update_of_ne (hother k hk).1,
      Function.update_of_ne (hother k hk).2]
  have hfactor (y : X) : partitionMomentDiagram G e (Function.update x v y) =
      G ((Function.update x v y) (e j).1) ((Function.update x v y) (e j).2) * R := by
    unfold partitionMomentDiagram
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), hrest]
  have hedge : (∫ y, G ((Function.update x v y) (e j).1)
      ((Function.update x v y) (e j).2) ∂μ) = 0 := by
    rcases hjincident with ha | hb
    · have hb : (e j).2 ≠ v := fun hb => hloop j (ha.trans hb.symm)
      calc
        _ = ∫ y, G (x (e j).2) y ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with y
          simp only [ha, Function.update_self, Function.update_of_ne hb]
          exact hsymm _ _
        _ = 0 := hcenter _
    · have ha : (e j).1 ≠ v := fun ha => hloop j (ha.trans hb.symm)
      simpa only [hb, Function.update_self, Function.update_of_ne ha] using hcenter (x (e j).1)
  simp_rw [hfactor]
  rw [integral_mul_const, hedge, zero_mul]

/-- Actual signed singleton cancellation, with absolute integrability derived
first from the uniform p-th row moment. No cancellation assumption is hidden in
the diagram bound or imported as a correlation theorem. -/
theorem partitionMomentDiagram_integral_zero_singleton {N p : ℕ}
    {μ : Measure X} [IsProbabilityMeasure μ]
    (G : X → X → ℝ) (hG : Measurable (Function.uncurry G))
    (hsymm : ∀ x y, G x y = G y x)
    (hcenter : ∀ z, (∫ y, G z y ∂μ) = 0)
    (e : Fin p → Fin N × Fin N) (hloop : ∀ j, (e j).1 ≠ (e j).2)
    (hp : 0 < p) (B : ℝ)
    (hrowInt : ∀ z, Integrable (fun y => |G z y| ^ p) μ)
    (hrow : ∀ z, (∫ y, |G z y| ^ p ∂μ) ≤ B)
    (v : Fin N) (hdegree : equilibriumDiagramDegree e v = 1) :
    (∫ x, partitionMomentDiagram G e x ∂Measure.pi (fun _ : Fin N => μ)) = 0 := by
  apply partitionMoment_integral_zero_of_coordinate _
    (partitionMomentDiagram_integrable G hG hsymm e hloop hp B hrowInt hrow) v
  exact partitionMomentDiagram_coordinate_zero G hsymm hcenter e hloop v hdegree

end RepulsiveCoulomb
