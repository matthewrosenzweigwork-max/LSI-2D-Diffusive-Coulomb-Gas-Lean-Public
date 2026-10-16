import LeanResearch.RepulsiveCoulomb.PointRadialC1GapPiece
import Mathlib.Data.Finset.Card

/-! Genuine finite-exception assembly. Every recursion step selects an actual
interior exceptional time and strictly reduces its finite cardinality on both
sides. The resulting finite macro-arc list is ordered by interval concatenation. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- A constructed macro-arc on intervals with no interior exceptional
time assembles into an actual finite ordered subdivision across all exceptions.
This generic lemma will be applied to the constructed finite puncture-time set. -/
theorem exists_pointRadialC1ArcChain_of_finite_exceptions
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (γ : Icc (0 : ℝ) 1 → ℂ) (P : Finset (Icc (0 : ℝ) 1))
    (hlocal : ∀ s t : Icc (0 : ℝ) 1, s < t →
      (∀ u ∈ Ioo s t, u ∉ P) →
      ∃ es : List (PointRadialC1ArcPiece ha y γ), PointRadialC1ArcChain ha y γ s t es)
    (s t : Icc (0 : ℝ) 1) (hst : s < t) :
    ∃ es : List (PointRadialC1ArcPiece ha y γ), PointRadialC1ArcChain ha y γ s t es := by
  classical
  let K (s t : Icc (0 : ℝ) 1) := P.filter (fun u => s < u ∧ u < t)
  have hmain : ∀ n : ℕ, ∀ s t : Icc (0 : ℝ) 1, s < t → (K s t).card = n →
      ∃ es : List (PointRadialC1ArcPiece ha y γ), PointRadialC1ArcChain ha y γ s t es := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s t hst hcard
      by_cases hne : (K s t).Nonempty
      · obtain ⟨r, hr⟩ := hne
        obtain ⟨hrP, hsr, hrt⟩ := Finset.mem_filter.mp hr
        have hleftsub : K s r ⊆ K s t := by
          intro u hu
          obtain ⟨huP, hsu, hur⟩ := Finset.mem_filter.mp hu
          exact Finset.mem_filter.mpr ⟨huP, hsu, hur.trans hrt⟩
        have hrightsub : K r t ⊆ K s t := by
          intro u hu
          obtain ⟨huP, hru, hut⟩ := Finset.mem_filter.mp hu
          exact Finset.mem_filter.mpr ⟨huP, hsr.trans hru, hut⟩
        have hrleft : r ∉ K s r := by
          intro h
          exact (lt_irrefl r) (Finset.mem_filter.mp h).2.2
        have hrright : r ∉ K r t := by
          intro h
          exact (lt_irrefl r) (Finset.mem_filter.mp h).2.1
        have hleftcard : (K s r).card < n := by
          rw [← hcard]
          apply Finset.card_lt_card
          exact Finset.ssubset_iff_subset_ne.mpr ⟨hleftsub, fun he => hrleft (he.symm ▸ hr)⟩
        have hrightcard : (K r t).card < n := by
          rw [← hcard]
          apply Finset.card_lt_card
          exact Finset.ssubset_iff_subset_ne.mpr ⟨hrightsub, fun he => hrright (he.symm ▸ hr)⟩
        obtain ⟨es, hes⟩ := ih (K s r).card hleftcard s r hsr rfl
        obtain ⟨fs, hfs⟩ := ih (K r t).card hrightcard r t hrt rfl
        exact ⟨es ++ fs, hes.append hfs⟩
      · apply hlocal s t hst
        intro u hu huP
        exact hne ⟨u, Finset.mem_filter.mpr ⟨huP, hu⟩⟩
  exact hmain (K s t).card s t hst rfl

end RepulsiveCoulomb
