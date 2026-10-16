module

public import LeanResearch.RepulsiveCoulomb.PointSignedCurvatureFinite
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Topology.Closure
public import Mathlib.Tactic

@[expose] public section

/-!
ISOLATED SOURCE-ONLY DRAFT, 2026-10-03. No compiler run or canonical staging.

Elementary support/cardinality theorems are separated from an explicit
set/clock interface. There is no assumed rank decrease, exposed-atom witness,
clean-ray conclusion, or finite-preparation conclusion in the Move fields.
The actual translated-strip/cut/attained-contact constructors are still needed
before this interface can be instantiated for the manuscript's preparation.

The existing project representation is `ν α : ℂ →₀ ℝ`, from
PointSignedCurvatureFinite. The finite algebra below works on any ambient X.
-/
noncomputable section
open Set
open scoped Classical

namespace RepulsiveCoulomb.BoundaryPreparation

variable {X : Type*}

/-- The literal ambient coefficient update, with transported mass ν p. -/
def transfer (ν : X →₀ ℝ) (p z : X) : X →₀ ℝ :=
  ν + Finsupp.single z (ν p) - Finsupp.single p (ν p)

def interiorSupport (ν : X →₀ ℝ) (I : Set X) : Finset X := by
  classical
  exact ν.support.filter (fun x => x ∈ I)

def rank (ν : X →₀ ℝ) (I : Set X) : ℕ :=
  ν.support.card + (interiorSupport ν I).card

@[simp] theorem mem_interiorSupport (ν : X →₀ ℝ) (I : Set X) (x : X) :
    x ∈ interiorSupport ν I ↔ ν x ≠ 0 ∧ x ∈ I := by
  classical
  simp [interiorSupport, Finsupp.mem_support_iff]

theorem transfer_source (ν : X →₀ ℝ) {p z : X} (hpz : p ≠ z) :
    transfer ν p z p = 0 := by
  classical
  simp [transfer, hpz, hpz.symm]

theorem transfer_target (ν : X →₀ ℝ) {p z : X} (hpz : p ≠ z) :
    transfer ν p z z = ν z + ν p := by
  classical
  simp [transfer, hpz, hpz.symm]

theorem transfer_away (ν : X →₀ ℝ) {p z x : X}
    (hxp : x ≠ p) (hxz : x ≠ z) : transfer ν p z x = ν x := by
  classical
  simp [transfer, hxp, hxz, hxp.symm, hxz.symm]

/-- Exact support, including cancellation at a previously marked target. -/
theorem transfer_support (ν : X →₀ ℝ) {p z : X} (hpz : p ≠ z) :
    (transfer ν p z).support =
      if ν z + ν p = 0 then (ν.support.erase p).erase z
      else insert z (ν.support.erase p) := by
  classical
  by_cases hsum : ν z + ν p = 0
  · rw [if_pos hsum]
    ext x
    by_cases hxp : x = p
    · subst x
      simp [Finsupp.mem_support_iff, transfer_source ν hpz]
    · by_cases hxz : x = z
      · subst x
        simp [Finsupp.mem_support_iff, transfer_target ν hpz, hsum]
      · simp [Finsupp.mem_support_iff, transfer_away ν hxp hxz, hxp, hxz]
  · rw [if_neg hsum]
    ext x
    by_cases hxp : x = p
    · subst x
      simp [Finsupp.mem_support_iff, transfer_source ν hpz, hpz]
    · by_cases hxz : x = z
      · subst x
        simp [Finsupp.mem_support_iff, transfer_target ν hpz, hsum]
      · simp [Finsupp.mem_support_iff, transfer_away ν hxp hxz, hxp, hxz]

/-- Existing target atoms produce no new support and lose the source atom. -/
theorem transfer_support_subset_erase (ν : X →₀ ℝ) {p z : X}
    (hpz : p ≠ z) (hz : ν z ≠ 0) :
    (transfer ν p z).support ⊆ ν.support.erase p := by
  classical
  intro x hx
  have hxp : x ≠ p := by
    intro h
    subst x
    exact (Finsupp.mem_support_iff.mp hx) (transfer_source ν hpz)
  refine Finset.mem_erase.mpr ⟨hxp, ?_⟩
  apply Finsupp.mem_support_iff.mpr
  by_cases hxz : x = z
  · simpa [hxz] using hz
  · simpa only [transfer_away ν hxp hxz] using Finsupp.mem_support_iff.mp hx

theorem transfer_card_lt_of_target_nonzero (ν : X →₀ ℝ) {p z : X}
    (hpz : p ≠ z) (hp : ν p ≠ 0) (hz : ν z ≠ 0) :
    (transfer ν p z).support.card < ν.support.card := by
  classical
  exact (Finset.card_le_card (transfer_support_subset_erase ν hpz hz)).trans_lt
    (Finset.card_erase_lt_of_mem (Finsupp.mem_support_iff.mpr hp))

/-- A new target replaces the source; the support cardinal is exactly unchanged. -/
theorem transfer_card_eq_of_target_zero (ν : X →₀ ℝ) {p z : X}
    (hpz : p ≠ z) (hp : ν p ≠ 0) (hz : ν z = 0) :
    (transfer ν p z).support.card = ν.support.card := by
  classical
  have hsum : ν z + ν p ≠ 0 := by simpa [hz] using hp
  have hznot : z ∉ ν.support.erase p := by
    simp [Finsupp.mem_support_iff, hz]
  rw [transfer_support ν hpz, if_neg hsum, Finset.card_insert_of_notMem hznot]
  exact Finset.card_erase_add_one (Finsupp.mem_support_iff.mpr hp)

theorem transfer_card_le (ν : X →₀ ℝ) {p z : X}
    (hpz : p ≠ z) (hp : ν p ≠ 0) :
    (transfer ν p z).support.card ≤ ν.support.card := by
  by_cases hz : ν z = 0
  · exact (transfer_card_eq_of_target_zero ν hpz hp hz).le
  · exact (transfer_card_lt_of_target_nonzero ν hpz hp hz).le

/-- Interior coefficients agree because neither modified point is interior. -/
theorem transfer_agrees_on_new_interior (ν : X →₀ ℝ) {p z : X} {I J : Set X}
    (hJI : J ⊆ I) (hpI : p ∉ I) (hzI : z ∉ I) :
    ∀ x ∈ J, transfer ν p z x = ν x := by
  intro x hx
  exact transfer_away ν (fun h => hpI (h ▸ hJI hx))
    (fun h => hzI (h ▸ hJI hx))

theorem transfer_interiorSupport_eq (ν : X →₀ ℝ) {p z : X} {I J : Set X}
    (hJI : J ⊆ I) (hpI : p ∉ I) (hzI : z ∉ I) :
    interiorSupport (transfer ν p z) J = interiorSupport ν J := by
  classical
  ext x
  by_cases hx : x ∈ J
  · simp only [mem_interiorSupport]
    rw [transfer_agrees_on_new_interior ν hJI hpI hzI x hx]
  · simp [mem_interiorSupport, hx]

theorem transfer_interiorSupport_subset (ν : X →₀ ℝ) {p z : X} {I J : Set X}
    (hJI : J ⊆ I) (hpI : p ∉ I) (hzI : z ∉ I) :
    interiorSupport (transfer ν p z) J ⊆ interiorSupport ν I := by
  rw [transfer_interiorSupport_eq ν hJI hpI hzI]
  intro x hx
  obtain ⟨hν, hxJ⟩ := (mem_interiorSupport ν J x).mp hx
  exact (mem_interiorSupport ν I x).mpr ⟨hν, hJI hxJ⟩

theorem transfer_interior_card_le (ν : X →₀ ℝ) {p z : X} {I J : Set X}
    (hJI : J ⊆ I) (hpI : p ∉ I) (hzI : z ∉ I) :
    (interiorSupport (transfer ν p z) J).card ≤ (interiorSupport ν I).card :=
  Finset.card_le_card (transfer_interiorSupport_subset ν hJI hpI hzI)

/-- Strictness is obtained from one actual exposed old curvature atom. -/
theorem transfer_interior_card_lt_of_exposed (ν : X →₀ ℝ)
    {p z q : X} {I J : Set X} (hJI : J ⊆ I) (hpI : p ∉ I) (hzI : z ∉ I)
    (hqν : ν q ≠ 0) (hqI : q ∈ I) (hqJ : q ∉ J) :
    (interiorSupport (transfer ν p z) J).card < (interiorSupport ν I).card := by
  classical
  have hsub : interiorSupport (transfer ν p z) J ⊆ (interiorSupport ν I).erase q := by
    intro x hx
    refine Finset.mem_erase.mpr ⟨?_, transfer_interiorSupport_subset ν hJI hpI hzI hx⟩
    intro hxq
    have hxJ := ((mem_interiorSupport (transfer ν p z) J x).mp hx).2
    exact hqJ (hxq ▸ hxJ)
  exact (Finset.card_le_card hsub).trans_lt
    (Finset.card_erase_lt_of_mem ((mem_interiorSupport ν I q).mpr ⟨hqν, hqI⟩))

/-- This names only the explicit finite-mark tail property. It is not an
invented replacement for the geometric clean-boundary-ray predicate. -/
def BudgetCleanTail (ν : X →₀ ℝ) (B : Finset X) (r : NNReal → X) : Prop :=
  ∃ s : NNReal, r s ∈ B ∧ ∀ u : NNReal, s < u → ν (r u) = 0 ∧ r u ∉ B

/-- Attained first contact plus a finite maximal budget clock proves the
clean-tail/exposed-atom dichotomy. No descent or exposed witness is assumed. -/
theorem first_contact_clean_or_exposed (ν : X →₀ ℝ) (B : Finset X)
    {p z : X} {I J : Set X} (hpI : p ∉ I) (hzI : z ∉ I) (hz : ν z = 0)
    (r : NNReal → X) (hr : Function.Injective r) (hbase : r 0 = z)
    (hopen : ∀ s, 0 < s → r s ∈ I) (hnew : ∀ s, r s ∉ J)
    (hcontact : ∃ s, ν (r s) ≠ 0 ∨ r s ∈ B) :
    BudgetCleanTail (transfer ν p z) B r ∨ ∃ q, ν q ≠ 0 ∧ q ∈ I ∧ q ∉ J := by
  classical
  by_cases hcurv : ∃ s : NNReal, 0 < s ∧ ν (r s) ≠ 0
  · obtain ⟨s, hs, hν⟩ := hcurv
    exact Or.inr ⟨r s, hν, hopen s hs, hnew s⟩
  · have hzero : ∀ s : NNReal, ν (r s) = 0 := by
      intro s
      by_cases hs : s = 0
      · simpa only [hs, hbase] using hz
      · by_contra hν
        exact hcurv ⟨s, pos_iff_ne_zero.mpr hs, hν⟩
    let K : Set NNReal := r ⁻¹' (↑B : Set X)
    have hK : K.Finite := B.finite_toSet.preimage (fun s _ u _ h => hr h)
    have hKne : K.Nonempty := by
      obtain ⟨s, hs⟩ := hcontact
      rcases hs with hs | hs
      · exact False.elim (hs (hzero s))
      · exact ⟨s, hs⟩
    obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image hK.toFinset id
      (hK.toFinset_nonempty.mpr hKne)
    have hsB : r s ∈ B := hK.mem_toFinset.mp hs
    left
    refine ⟨s, hsB, ?_⟩
    intro u hsu
    have huI : r u ∈ I := hopen u ((show (0 : NNReal) ≤ s from zero_le).trans_lt hsu)
    have hup : r u ≠ p := fun h => hpI (h ▸ huI)
    have huz : r u ≠ z := fun h => hzI (h ▸ huI)
    refine ⟨(transfer_away ν hup huz).trans (hzero u), ?_⟩
    intro huB
    have huK : u ∈ hK.toFinset := hK.mem_toFinset.mpr huB
    exact (not_le_of_gt hsu) (hmax u huK)

/-- The contact used above is literally contact with the project's old marked
set, including budget-only atoms. -/
theorem contact_of_pointSignedMarked {ν α : ℂ →₀ ℝ} {r : NNReal → ℂ}
    (h : ∃ s, r s ∈ pointSignedMarked ν α) :
    ∃ s, ν (r s) ≠ 0 ∨ r s ∈ α.support := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, ?_⟩
  simpa only [Finsupp.mem_support_iff] using (mem_pointSignedMarked ν α (r s)).mp hs

/-- The chosen farthest budget clock gives exactly the marked-set avoidance
shape consumed by PointMarkedRayClearance, after shifting the ray. Metric and
boundary-end properties of that shifted ray remain separate geometric facts. -/
theorem BudgetCleanTail.pointSignedMarked_shift_disjoint
    {ν α : ℂ →₀ ℝ} {r : NNReal → ℂ} (h : BudgetCleanTail ν α.support r) :
    ∃ s : NNReal, α (r s) ≠ 0 ∧
      Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {r s})
        (range (fun u : NNReal => r (u + s))) := by
  classical
  obtain ⟨s, hs, htail⟩ := h
  refine ⟨s, Finsupp.mem_support_iff.mp hs, ?_⟩
  apply Set.disjoint_left.mpr
  intro x hx hrange
  obtain ⟨u, rfl⟩ := hrange
  by_cases hu : u = 0
  · exact hx.2 (by simpa [hu])
  · have hu0 : 0 < u := pos_iff_ne_zero.mpr hu
    have hsu : s < u + s := lt_add_of_pos_left s hu0
    obtain ⟨hν, hα⟩ := htail (u + s) hsu
    rcases (mem_pointSignedMarked ν α (r (u + s))).mp hx.1 with hm | hm
    · exact hm hν
    · exact hα (Finsupp.mem_support_iff.mpr hm)

/-- Minimal elementary interface for one *actual* translated move.
Every field concerns coefficient values, actual point sets, or actual clocks.
The geometric strip construction must supply these; this structure does not
construct a strip, its first contact, or a residual halfplane. -/
structure Move (ν ν' : X →₀ ℝ) (B : Finset X) (I J : Set X) where
  source : X
  target : X
  distinct : source ≠ target
  source_positive : 0 < ν source
  source_not_interior : source ∉ I
  target_not_interior : target ∉ I
  interior_subset : J ⊆ I
  update : ν' = transfer ν source target
  ray : NNReal → X
  ray_injective : Function.Injective ray
  ray_zero : ray 0 = target
  ray_positive_interior : ∀ s, 0 < s → ray s ∈ I
  ray_not_new_interior : ∀ s, ray s ∉ J
  marked_contact : ∃ s, ν (ray s) ≠ 0 ∨ ray s ∈ B

namespace Move

variable {ν ν' : X →₀ ℝ} {B : Finset X} {I J : Set X}

theorem support_card_le (M : Move ν ν' B I J) : ν'.support.card ≤ ν.support.card := by
  rw [M.update]
  exact transfer_card_le ν M.distinct M.source_positive.ne'

theorem interior_card_le (M : Move ν ν' B I J) :
    (interiorSupport ν' J).card ≤ (interiorSupport ν I).card := by
  rw [M.update]
  exact transfer_interior_card_le ν M.interior_subset M.source_not_interior M.target_not_interior

/-- Existing-target moves strictly lower n+i even when terminal. In the
new-target case, the proved marked-clock dichotomy supplies strictness unless
there is an actual budget-clean tail. -/
theorem clean_or_rank_lt (M : Move ν ν' B I J) :
    BudgetCleanTail ν' B M.ray ∨ rank ν' J < rank ν I := by
  by_cases hz : ν M.target = 0
  · obtain hc | ⟨q, hqν, hqI, hqJ⟩ := first_contact_clean_or_exposed ν B
      M.source_not_interior M.target_not_interior hz M.ray M.ray_injective M.ray_zero
      M.ray_positive_interior M.ray_not_new_interior M.marked_contact
    · left
      simpa only [M.update] using hc
    · right
      have hn := transfer_card_eq_of_target_zero ν M.distinct M.source_positive.ne' hz
      have hi := transfer_interior_card_lt_of_exposed ν M.interior_subset
        M.source_not_interior M.target_not_interior hqν hqI hqJ
      rw [M.update, rank, hn]
      exact Nat.add_lt_add_left hi _
  · right
    have hn := transfer_card_lt_of_target_nonzero ν M.distinct M.source_positive.ne' hz
    have hi := transfer_interior_card_le ν M.interior_subset
      M.source_not_interior M.target_not_interior
    rw [M.update, rank]
    exact Nat.add_lt_add_of_lt_of_le hn hi

theorem rank_lt_of_no_clean (M : Move ν ν' B I J)
    (h : ¬ BudgetCleanTail ν' B M.ray) : rank ν' J < rank ν I :=
  M.clean_or_rank_lt.resolve_left h

end Move

/-- A geometric first-contact set is on the new free ray once the removed
old sides are clean. This lemma consumes the boundary decomposition, not a
maximality-to-attainment shortcut. -/
theorem contact_subset_free {C O E R : Set X} {z : X}
    (hcover : C ⊆ O ∪ E ∪ R)
    (hO : ∀ x ∈ C, x ∉ O)
    (hE : ∀ x ∈ C, x ∈ E → x = z)
    (hz : z ∈ R) : C ⊆ R := by
  intro x hx
  rcases hcover hx with (hxO | hxE) | hxR
  · exact False.elim (hO x hx hxO)
  · simpa only [hE x hx hxE] using hz
  · exact hxR

/-- Exact old-boundary contact and source-side separation force positive-time
free-ray points into the old interior. No global old-boundary geodesicity. -/
theorem positive_ray_mem_old_interior [TopologicalSpace X]
    {P : Set X} {z : X} {r : NNReal → X}
    (hr : Function.Injective r) (hbase : r 0 = z)
    (hP : ∀ s, r s ∈ P)
    (hcontact : Set.range r ∩ frontier P ⊆ {z}) :
    ∀ s, 0 < s → r s ∈ interior P := by
  intro s hs
  apply (mem_interior_iff_notMem_frontier (hP s)).mpr
  intro hb
  have heq : r s = z := hcontact ⟨mem_range_self s, hb⟩
  have hs0 : s = 0 := hr (heq.trans hbase.symm)
  exact hs.ne' hs0

/-- New-frontier membership excludes new interior membership. -/
theorem ray_not_interior_of_frontier [TopologicalSpace X]
    {Q : Set X} {r : NNReal → X} (hr : Set.range r ⊆ frontier Q) :
    ∀ s, r s ∉ interior Q := by
  intro s hs
  exact disjoint_interior_frontier.le_bot ⟨hs, hr (mem_range_self s)⟩

/-- The rank's factor-two estimate counts only nonzero curvature atoms. -/
theorem rank_le_twice_support (ν : X →₀ ℝ) (I : Set X) :
    rank ν I ≤ 2 * ν.support.card := by
  classical
  have h : (interiorSupport ν I).card ≤ ν.support.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  unfold rank
  omega

/-- Honest translated-move bound, derived from actual Move fields and a
geometric clean-tail-to-terminal bridge. Only results of the first N−1 moves
are required nonterminal; the final move may leave rank unchanged.

n_initial here is ν 0's support count at the translated-loop start. A prior
full-strip cut requires a separately proved support-count comparison. -/
theorem translated_trace_bound (ν : ℕ → X →₀ ℝ) (I : ℕ → Set X)
    (B : Finset X) (Terminal : ℕ → Prop) (N : ℕ)
    (step : ∀ k, k < N → Move (ν k) (ν (k + 1)) B (I k) (I (k + 1)))
    (clean_terminal : ∀ k (hk : k < N),
      BudgetCleanTail (ν (k + 1)) B (step k hk).ray → Terminal (k + 1))
    (not_terminal : ∀ k, 0 < k → k < N → ¬ Terminal k) :
    N ≤ rank (ν 0) (I 0) + 1 ∧ N ≤ 2 * (ν 0).support.card + 1 := by
  have hdrop (k : ℕ) (hk : k < N - 1) :
      rank (ν (k + 1)) (I (k + 1)) < rank (ν k) (I k) := by
    have hkN : k < N := by omega
    apply (step k hkN).rank_lt_of_no_clean
    intro hc
    exact not_terminal (k + 1) (by omega) (by omega) (clean_terminal k hkN hc)
  have hacc : ∀ k, k ≤ N - 1 → rank (ν k) (I k) + k ≤ rank (ν 0) (I 0) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hi := ih (by omega)
      have hd := hdrop k (by omega)
      omega
  have ha := hacc (N - 1) le_rfl
  have hr := rank_le_twice_support (ν 0) (I 0)
  constructor <;> omega

end RepulsiveCoulomb.BoundaryPreparation
