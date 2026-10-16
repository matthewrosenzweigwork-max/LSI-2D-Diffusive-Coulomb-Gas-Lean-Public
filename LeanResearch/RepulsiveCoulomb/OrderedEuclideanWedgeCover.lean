import LeanResearch.RepulsiveCoulomb.FlatLinkCircularArcSubdivision
import Mathlib.Order.Fin.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-! SOURCE-ONLY, UNCOMPILED. Construct the ordered target disk wedges from
actual positive widths with their scalar total. The finite cover and closed
pieces are conclusions, not an assumed target atlas or piece cover. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- An origin ray absent from an occupied open arc prevents strict wrapping
after the lower endpoint has been put into one period. -/
theorem flatLink_no_wrap_of_origin_avoided {r lo width : ℝ}
    (hlo : lo ∈ Ico (0 : ℝ) (2 * Real.pi))
    (havoid : ∀ θ ∈ Ioo lo (lo + width), sectorPolar r 0 ≠ sectorPolar r θ) :
    lo + width ≤ 2 * Real.pi := by
  by_contra hn
  have hwrap : 2 * Real.pi < lo + width := lt_of_not_ge hn
  apply havoid (2 * Real.pi) ⟨hlo.2, hwrap⟩
  simpa only [zero_add] using ((sectorPolar_periodic r) 0).symm

def linkCumulativeWidth (width : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, width i

@[simp] theorem linkCumulativeWidth_zero (width : ℕ → ℝ) : linkCumulativeWidth width 0 = 0 := by
  simp [linkCumulativeWidth]

theorem linkCumulativeWidth_succ (width : ℕ → ℝ) (n : ℕ) :
    linkCumulativeWidth width (n + 1) = linkCumulativeWidth width n + width n := by
  simp only [linkCumulativeWidth, Finset.sum_range_succ]

/-- Ordered cumulative target angles are constructed from positive widths. -/
theorem linkCumulativeWidth_strictMono {N : ℕ} (width : ℕ → ℝ)
    (hwidth : ∀ i < N, 0 < width i) :
    StrictMono (fun i : Fin (N + 1) ↦ linkCumulativeWidth width i.1) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  change linkCumulativeWidth width i.1 < linkCumulativeWidth width (i.1 + 1)
  rw [linkCumulativeWidth_succ]
  exact lt_add_of_pos_right _ (hwidth i.1 i.2)

/-- Consecutive intervals cover the entire interval between the first and
last values. The proof constructs an index by finite induction. -/
theorem exists_consecutive_interval_cover (u : ℕ → ℝ) :
    ∀ N : ℕ, 0 < N → ∀ θ : ℝ, θ ∈ Icc (u 0) (u N) →
      ∃ i : ℕ, i < N ∧ θ ∈ Icc (u i) (u (i + 1)) := by
  intro N
  induction N with
  | zero => intro hN; omega
  | succ N ih =>
      intro hN θ hθ
      by_cases hzero : N = 0
      · subst N
        exact ⟨0, by omega, hθ⟩
      · by_cases hθN : θ ≤ u N
        · obtain ⟨i, hi, hmem⟩ := ih (Nat.pos_of_ne_zero hzero) θ ⟨hθ.1, hθN⟩
          exact ⟨i, hi.trans (Nat.lt_succ_self _), hmem⟩
        · exact ⟨N, Nat.lt_succ_self _, (lt_of_not_ge hθN).le, hθ.2⟩

theorem exists_sectorPolar_nonnegative_angle (z : ℂ) :
    ∃ θ ∈ Icc (0 : ℝ) (2 * Real.pi), z = sectorPolar ‖z‖ θ := by
  by_cases harg : Complex.arg z < 0
  · refine ⟨Complex.arg z + 2 * Real.pi,
      ⟨by linarith [Complex.neg_pi_lt_arg z, Real.pi_pos], by linarith⟩, ?_⟩
    rw [(sectorPolar_periodic ‖z‖) (Complex.arg z)]
    exact (sectorPolar_norm_arg z).symm
  · exact ⟨Complex.arg z, ⟨le_of_not_gt harg,
      (Complex.arg_le_pi z).trans (by linarith [Real.pi_pos])⟩,
      (sectorPolar_norm_arg z).symm⟩

/-- A literal finite cover of the entire target disk by the ordered wedges. -/
theorem orderedEuclideanWedges_cover {N : ℕ} (hN : 0 < N)
    (width : ℕ → ℝ) (htotal : linkCumulativeWidth width N = 2 * Real.pi)
    (R : ℝ) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ∃ i : Fin N, z ∈ flatLinkOccupiedDisk R (linkCumulativeWidth width i.1)
      (linkCumulativeWidth width (i.1 + 1)) := by
  obtain ⟨θ, hθ, he⟩ := exists_sectorPolar_nonnegative_angle z
  have hθ' : θ ∈ Icc (linkCumulativeWidth width 0) (linkCumulativeWidth width N) := by
    simpa only [linkCumulativeWidth_zero, htotal] using hθ
  obtain ⟨i, hi, hmem⟩ := exists_consecutive_interval_cover (linkCumulativeWidth width) N hN θ hθ'
  exact ⟨⟨i, hi⟩, ‖z‖, ⟨norm_nonneg _, hz⟩, θ, hmem, he⟩

/-- Every finite closed angular disk is a genuine closed subset of C,
including intervals crossing a principal-argument cut. -/
theorem flatLinkOccupiedDisk_isClosed (R lo hi : ℝ) :
    IsClosed (flatLinkOccupiedDisk R lo hi) := by
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) R ×ˢ Icc lo hi
  let f : ℝ × ℝ → ℂ := fun p ↦ sectorPolar p.1 p.2
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hf : Continuous f := by
    dsimp [f, sectorPolar, conePhase]
    fun_prop
  have heq : flatLinkOccupiedDisk R lo hi = f '' K := by
    ext z
    constructor
    · rintro ⟨r, hr, θ, hθ, he⟩
      exact ⟨(r, θ), ⟨hr, hθ⟩, he.symm⟩
    · rintro ⟨⟨r, θ⟩, ⟨hr, hθ⟩, he⟩
      exact ⟨r, hr, θ, hθ, he.symm⟩
  rw [heq]
  exact (hK.image hf).isClosed

end RepulsiveCoulomb
