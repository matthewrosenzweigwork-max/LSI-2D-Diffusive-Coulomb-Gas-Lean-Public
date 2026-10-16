import LeanResearch.RepulsiveCoulomb.PartitionMomentBranchHolder

/-! Genuine finite-product diagram integration by successive vertex removal.
Each ordered edge occurrence is an element of an arbitrary finite slot set.
Repetitions and reversed edges are never identified. All integrations here are
nonnegative Tonelli integrations; signed Fubini is used only downstream, after
this file establishes absolute integrability. Records-only, not author-checked. -/

noncomputable section
open scoped BigOperators ENNReal Classical
open MeasureTheory

namespace RepulsiveCoulomb

variable {X V E : Type*} [MeasurableSpace X] [DecidableEq V]

/-- Edge slots incident to a vertex, with repeated slots retained. -/
def partitionMomentIncident (a b : E → V) (s : Finset E) (v : V) : Finset E :=
  s.filter (fun e => a e = v ∨ b e = v)

/-- Remove every slot meeting the selected vertex. -/
def partitionMomentRemaining (a b : E → V) (s : Finset E) (v : V) : Finset E :=
  s.filter (fun e => ¬ (a e = v ∨ b e = v))

/-- The literal product belonging to an ordered edge-slot list. -/
def partitionMomentProduct (K : X → X → ℝ≥0∞) (a b : E → V)
    (s : Finset E) (x : V → X) : ℝ≥0∞ := ∏ e ∈ s, K (x (a e)) (x (b e))

theorem partitionMomentProduct_measurable (K : X → X → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (a b : E → V) (s : Finset E) :
    Measurable (partitionMomentProduct K a b s) := by
  apply s.measurable_fun_prod
  intro e _
  have hm : Measurable (fun x : V → X => (x (a e), x (b e))) :=
    (measurable_pi_apply (a e)).prodMk (measurable_pi_apply (b e))
  simpa only [Function.comp_def, Function.uncurry] using hK.comp hm

theorem partitionMomentIncident_card_add_remaining (a b : E → V)
    (s : Finset E) (v : V) :
    (partitionMomentIncident a b s v).card + (partitionMomentRemaining a b s v).card =
      s.card := by
  exact Finset.card_filter_add_card_filter_not (s := s) _

theorem partitionMomentIncident_mono (a b : E → V) {s t : Finset E}
    (hst : s ⊆ t) (v : V) :
    partitionMomentIncident a b s v ⊆ partitionMomentIncident a b t v := by
  exact Finset.filter_subset_filter _ hst

/-- Inactive slots are independent of the coordinate currently integrated. -/
theorem partitionMomentProduct_remaining_update (K : X → X → ℝ≥0∞)
    (a b : E → V) (s : Finset E) (v : V) (x : V → X) (y : X) :
    partitionMomentProduct K a b (partitionMomentRemaining a b s v)
      (Function.update x v y) =
      partitionMomentProduct K a b (partitionMomentRemaining a b s v) x := by
  apply Finset.prod_congr rfl
  intro e he
  have h := (Finset.mem_filter.mp he).2
  have ha : a e ≠ v := fun hh => h (Or.inl hh)
  have hb : b e ≠ v := fun hh => h (Or.inr hh)
  simp only [Function.update_of_ne ha, Function.update_of_ne hb]

/-- Exact splitting of all slots into the ones removed now and those retained. -/
theorem partitionMomentProduct_update_split (K : X → X → ℝ≥0∞)
    (a b : E → V) (s : Finset E) (v : V) (x : V → X) (y : X) :
    partitionMomentProduct K a b s (Function.update x v y) =
      partitionMomentProduct K a b (partitionMomentRemaining a b s v) x *
      partitionMomentProduct K a b (partitionMomentIncident a b s v)
        (Function.update x v y) := by
  rw [← partitionMomentProduct_remaining_update K a b s v x y]
  exact (Finset.prod_filter_not_mul_prod_filter s
    (fun e => a e = v ∨ b e = v)
    (fun e => K ((Function.update x v y) (a e))
      ((Function.update x v y) (b e)))).symm

/-- The one-vertex estimate uses actual uniform row moments and symmetry.
Loop-freeness is essential: it ensures the other endpoint stays frozen. -/
theorem partitionMoment_integrate_vertex
    {μ : Measure X} [IsProbabilityMeasure μ]
    (K : X → X → ℝ≥0∞) (hK : Measurable (Function.uncurry K))
    (hsymm : ∀ x y, K x y = K y x)
    (a b : E → V) (s : Finset E) (v : V) {q : ℕ} (hq : 0 < q)
    (hloop : ∀ e ∈ s, a e ≠ b e)
    (hdegree : (partitionMomentIncident a b s v).card ≤ q)
    (C : ℝ≥0∞)
    (hrow : ∀ z, (∫⁻ y, K z y ^ q ∂μ) ^ (1 / (q : ℝ)) ≤ C)
    (x : V → X) :
    (∫⁻ y, partitionMomentProduct K a b s (Function.update x v y) ∂μ) ≤
      C ^ (partitionMomentIncident a b s v).card *
        partitionMomentProduct K a b (partitionMomentRemaining a b s v) x := by
  let t := partitionMomentIncident a b s v
  have hf : ∀ e ∈ t, Measurable (fun y =>
      K ((Function.update x v y) (a e)) ((Function.update x v y) (b e))) := by
    intro e _
    exact (hK.comp ((measurable_pi_apply (a e)).prodMk
      (measurable_pi_apply (b e)))).comp (measurable_update x)
  have hroot : ∀ e ∈ t,
      (∫⁻ y, K ((Function.update x v y) (a e))
        ((Function.update x v y) (b e)) ^ q ∂μ) ^ (1 / (q : ℝ)) ≤ C := by
    intro e he
    have hes := (Finset.mem_filter.mp he).1
    rcases (Finset.mem_filter.mp he).2 with ha | hb
    · have hb : b e ≠ v := fun hb => hloop e hes (ha.trans hb.symm)
      have heq : (fun y => K ((Function.update x v y) (a e))
          ((Function.update x v y) (b e))) = (fun y => K (x (b e)) y) := by
        funext y
        simp only [ha, Function.update_self, Function.update_of_ne hb]
        exact hsymm _ _
      calc
        _ = (∫⁻ y, K (x (b e)) y ^ q ∂μ) ^ (1 / (q : ℝ)) := by
          congr 1
          exact lintegral_congr (fun y => congrArg (fun z : ℝ≥0∞ => z ^ q)
            (congrFun heq y))
        _ ≤ C := hrow (x (b e))
    · have ha : a e ≠ v := fun ha => hloop e hes (ha.trans hb.symm)
      have heq : (fun y => K ((Function.update x v y) (a e))
          ((Function.update x v y) (b e))) = (fun y => K (x (a e)) y) := by
        funext y
        simp only [hb, Function.update_self, Function.update_of_ne ha]
      calc
        _ = (∫⁻ y, K (x (a e)) y ^ q ∂μ) ^ (1 / (q : ℝ)) := by
          congr 1
          exact lintegral_congr (fun y => congrArg (fun z : ℝ≥0∞ => z ^ q)
            (congrFun heq y))
        _ ≤ C := hrow (x (a e))
  have hh := partitionMoment_lintegral_prod_le_pow t
    (fun e y => K ((Function.update x v y) (a e))
      ((Function.update x v y) (b e))) hq hdegree hf C hroot
  calc
    (∫⁻ y, partitionMomentProduct K a b s (Function.update x v y) ∂μ) =
        partitionMomentProduct K a b (partitionMomentRemaining a b s v) x *
          ∫⁻ y, partitionMomentProduct K a b t (Function.update x v y) ∂μ := by
      calc
        _ = ∫⁻ y, partitionMomentProduct K a b (partitionMomentRemaining a b s v) x *
            partitionMomentProduct K a b t (Function.update x v y) ∂μ :=
          lintegral_congr (fun y => partitionMomentProduct_update_split K a b s v x y)
        _ = _ := lintegral_const_mul _
          ((partitionMomentProduct_measurable K hK a b t).comp (measurable_update x))
    _ ≤ partitionMomentProduct K a b (partitionMomentRemaining a b s v) x *
        C ^ t.card := mul_le_mul_right hh _
    _ = _ := mul_comm _ _

/-- Constant factors pull out of the genuine product marginal. -/
theorem partitionMoment_lmarginal_const_mul
    {μ : Measure X} [SigmaFinite μ] (S : Finset V)
    (f : (V → X) → ℝ≥0∞) (hf : Measurable f) (C : ℝ≥0∞) (x : V → X) :
    lmarginal (fun _ : V => μ) S (fun z => C * f z) x =
      C * lmarginal (fun _ : V => μ) S f x := by
  unfold lmarginal
  exact lintegral_const_mul _ (hf.comp measurable_updateFinset)

/-- Successively integrate all vertices in `S`. Every original edge slot is
removed exactly once. The degree bound is inherited by taking subsets; there
is no reuse of an original minimum-degree assumption after a vertex is removed. -/
theorem partitionMoment_lmarginal_product_le
    {μ : Measure X} [IsProbabilityMeasure μ]
    (K : X → X → ℝ≥0∞) (hK : Measurable (Function.uncurry K))
    (hsymm : ∀ x y, K x y = K y x)
    (a b : E → V) (S : Finset V) (s : Finset E) {q : ℕ} (hq : 0 < q)
    (hloop : ∀ e ∈ s, a e ≠ b e)
    (hsupport : ∀ e ∈ s, a e ∈ S ∧ b e ∈ S)
    (hdegree : ∀ v, (partitionMomentIncident a b s v).card ≤ q)
    (C : ℝ≥0∞)
    (hrow : ∀ z, (∫⁻ y, K z y ^ q ∂μ) ^ (1 / (q : ℝ)) ≤ C)
    (x : V → X) :
    lmarginal (fun _ : V => μ) S (partitionMomentProduct K a b s) x ≤ C ^ s.card := by
  induction S using Finset.induction_on generalizing s with
  | empty =>
      have hs : s = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        exact Finset.notMem_empty _ (hsupport e he).1
      simp [hs, partitionMomentProduct]
  | @insert v S hv ih =>
      let t := partitionMomentIncident a b s v
      let r := partitionMomentRemaining a b s v
      have hrs : r ⊆ s := Finset.filter_subset _ _
      have hrloop : ∀ e ∈ r, a e ≠ b e := fun e he => hloop e (hrs he)
      have hrsupport : ∀ e ∈ r, a e ∈ S ∧ b e ∈ S := by
        intro e he
        have hs := hsupport e (hrs he)
        have hn := (Finset.mem_filter.mp he).2
        constructor
        · exact (Finset.mem_insert.mp hs.1).resolve_left (fun h => hn (Or.inl h))
        · exact (Finset.mem_insert.mp hs.2).resolve_left (fun h => hn (Or.inr h))
      have hrdegree : ∀ w, (partitionMomentIncident a b r w).card ≤ q := by
        intro w
        exact (Finset.card_le_card (partitionMomentIncident_mono a b hrs w)).trans
          (hdegree w)
      have hinner : (fun z => ∫⁻ y,
          partitionMomentProduct K a b s (Function.update z v y) ∂μ) ≤
          (fun z => C ^ t.card * partitionMomentProduct K a b r z) := by
        intro z
        exact partitionMoment_integrate_vertex K hK hsymm a b s v hq hloop
          (hdegree v) C hrow z
      rw [lmarginal_insert' _ (partitionMomentProduct_measurable K hK a b s) hv]
      calc
        lmarginal (fun _ : V => μ) S (fun z => ∫⁻ y,
            partitionMomentProduct K a b s (Function.update z v y) ∂μ) x ≤
            lmarginal (fun _ : V => μ) S
              (fun z => C ^ t.card * partitionMomentProduct K a b r z) x :=
          lmarginal_mono hinner x
        _ = C ^ t.card * lmarginal (fun _ : V => μ) S
            (partitionMomentProduct K a b r) x :=
          partitionMoment_lmarginal_const_mul S _
            (partitionMomentProduct_measurable K hK a b r) _ x
        _ ≤ C ^ t.card * C ^ r.card :=
          mul_le_mul_right (ih r hrloop hrsupport hrdegree) _
        _ = C ^ s.card := by
          rw [← pow_add]
          congr 1
          exact partitionMomentIncident_card_add_remaining a b s v

/-- Full continuous finite-product diagram estimate. The probability measure
is the actual product `Measure.pi`; no empirical approximation occurs. -/
theorem partitionMoment_lintegral_product_le
    [Fintype V] {μ : Measure X} [IsProbabilityMeasure μ]
    (K : X → X → ℝ≥0∞) (hK : Measurable (Function.uncurry K))
    (hsymm : ∀ x y, K x y = K y x)
    (a b : E → V) (s : Finset E) {q : ℕ} (hq : 0 < q)
    (hloop : ∀ e ∈ s, a e ≠ b e)
    (hdegree : ∀ v, (partitionMomentIncident a b s v).card ≤ q)
    (C : ℝ≥0∞)
    (hrow : ∀ z, (∫⁻ y, K z y ^ q ∂μ) ^ (1 / (q : ℝ)) ≤ C) :
    (∫⁻ x, partitionMomentProduct K a b s x ∂Measure.pi (fun _ : V => μ)) ≤
      C ^ s.card := by
  classical
  haveI : Nonempty X := nonempty_of_isProbabilityMeasure μ
  let x : V → X := fun _ => Classical.choice (inferInstance : Nonempty X)
  rw [lintegral_eq_lmarginal_univ x]
  exact partitionMoment_lmarginal_product_le K hK hsymm a b Finset.univ s hq
    hloop (fun _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩) hdegree C hrow x

end RepulsiveCoulomb
