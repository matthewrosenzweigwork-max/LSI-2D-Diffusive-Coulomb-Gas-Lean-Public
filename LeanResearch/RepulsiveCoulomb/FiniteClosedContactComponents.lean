import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Interval.Set.OrdConnected

/-! Source-only draft. A finite union of closed order intervals has a genuine
next contact after a terminal contact component. This fills the gap left by
compact-curve first/last-hit lemmas: the later set is initially open at `z`,
so its infimum cannot be declared a later contact without this argument. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- An order-connected contact piece containing a terminal point cannot also
contain a later point. `hterminal` says exactly that the contact component
through `z` has no extension to the right; it asserts no positive gap. -/
theorem contact_piece_no_later_of_terminal {C J : Set ℝ} {z : ℝ}
    (hJ : OrdConnected J) (hJC : J ⊆ C) (hz : z ∈ J)
    (hterminal : ∀ t, z < t → ¬ Icc z t ⊆ C) :
    ∀ t ∈ J, t ≤ z := by
  intro t ht
  by_contra htz
  exact hterminal t (lt_of_not_ge htz) ((hJ.out hz ht).trans hJC)

/-- Removing the terminal component makes the genuinely later contact set
closed. Finiteness, rather than a claimed crossing-finiteness theorem, is the
only ingredient that lets closedness survive this deletion. -/
theorem finite_closed_contact_later_closed {ι : Type*} [Finite ι]
    (J : ι → Set ℝ) (hclosed : ∀ i, IsClosed (J i))
    (hinterval : ∀ i, OrdConnected (J i)) {z : ℝ}
    (hterminal : ∀ t, z < t → ¬ Icc z t ⊆ ⋃ i, J i) :
    IsClosed ((⋃ i, J i) ∩ Ioi z) := by
  classical
  let K : ι → Set ℝ := fun i => if z ∈ J i then ∅ else J i ∩ Ici z
  have hK : ∀ i, IsClosed (K i) := by
    intro i
    by_cases hz : z ∈ J i
    · simpa [K, hz] using (isClosed_empty : IsClosed (∅ : Set ℝ))
    · simpa [K, hz] using (hclosed i).inter isClosed_Ici
  have heq : (⋃ i, J i) ∩ Ioi z = ⋃ i, K i := by
    ext t
    constructor
    · rintro ⟨ht, hzt⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp ht
      have hzi : z ∉ J i := by
        intro hz
        have hle := contact_piece_no_later_of_terminal (hinterval i)
          (subset_iUnion J i) hz hterminal t hi
        exact (not_lt_of_ge hle) hzt
      exact mem_iUnion.mpr ⟨i, by simpa [K, hzi] using And.intro hi hzt.le⟩
    · intro ht
      obtain ⟨i, hi⟩ := mem_iUnion.mp ht
      by_cases hzi : z ∈ J i
      · exact False.elim (by simpa [K, hzi] using hi)
      · have hit : t ∈ J i ∩ Ici z := by simpa [K, hzi] using hi
        refine ⟨mem_iUnion.mpr ⟨i, hit.1⟩, ?_⟩
        change z < t
        apply lt_of_le_of_ne (show z ≤ t from hit.2)
        intro he
        exact hzi (he.symm ▸ hit.1)
  rw [heq]
  exact isClosed_iUnion_of_finite hK

/-- The first later contact is the actual least point of the later set.
In particular the complete intervening open interval is contact-free. -/
theorem exists_first_later_finite_closed_contact {ι : Type*} [Finite ι]
    (J : ι → Set ℝ) (hclosed : ∀ i, IsClosed (J i))
    (hinterval : ∀ i, OrdConnected (J i)) {z : ℝ}
    (hterminal : ∀ t, z < t → ¬ Icc z t ⊆ ⋃ i, J i)
    (hlater : ((⋃ i, J i) ∩ Ioi z).Nonempty) :
    ∃ w : ℝ, z < w ∧ w ∈ ⋃ i, J i ∧
      IsLeast ((⋃ i, J i) ∩ Ioi z) w ∧
      ∀ t ∈ Ioo z w, t ∉ ⋃ i, J i := by
  let C := (⋃ i, J i) ∩ Ioi z
  have hC : IsClosed C := finite_closed_contact_later_closed J hclosed hinterval hterminal
  have hbelow : BddBelow C := ⟨z, fun t ht => ht.2.le⟩
  have hleast := hC.isLeast_csInf hlater hbelow
  refine ⟨sInf C, hleast.1.2, hleast.1.1, hleast, ?_⟩
  intro t ht hcontact
  exact (not_le_of_gt ht.2) (hleast.2 ⟨hcontact, ht.1⟩)

/-- A completely explicit trimming alternative. Given an interior time and
contacts on either side, choose the last old contact before that time and the
first one afterwards on a compact window. No finite-contact premise is needed.
This does not identify the trimmed point with the original initial component. -/
theorem exists_contact_gap_around_noncontact {C : Set ℝ} (hC : IsClosed C)
    {a e b : ℝ} (hae : a < e) (heb : e < b)
    (ha : a ∈ C) (he : e ∉ C) (hb : b ∈ C) :
    ∃ z w : ℝ, a ≤ z ∧ z < e ∧ e < w ∧ w ≤ b ∧ z ∈ C ∧ w ∈ C ∧
      ∀ t ∈ Ioo z w, t ∉ C := by
  obtain ⟨z, hz⟩ := (isCompact_Icc.inter_right hC).exists_isGreatest
    (show (Icc a e ∩ C).Nonempty from ⟨a, ⟨le_rfl, hae.le⟩, ha⟩)
  obtain ⟨w, hw⟩ := (isCompact_Icc.inter_right hC).exists_isLeast
    (show (Icc e b ∩ C).Nonempty from ⟨b, ⟨heb.le, le_rfl⟩, hb⟩)
  have hze : z < e := lt_of_le_of_ne hz.1.1.2 (fun h => he (h ▸ hz.1.2))
  have hew : e < w := lt_of_le_of_ne hw.1.1.1 (fun h => he (h.symm ▸ hw.1.2))
  refine ⟨z, w, hz.1.1.1, hze, hew, hw.1.1.2, hz.1.2, hw.1.2, ?_⟩
  intro t ht htc
  rcases le_total t e with hte | het
  · have htz := hz.2 ⟨⟨hz.1.1.1.trans ht.1.le, hte⟩, htc⟩
    exact (not_le_of_gt ht.1) htz
  · have hwt := hw.2 ⟨⟨het, ht.2.le.trans hw.1.1.2⟩, htc⟩
    exact (not_le_of_gt ht.2) hwt

end RepulsiveCoulomb
