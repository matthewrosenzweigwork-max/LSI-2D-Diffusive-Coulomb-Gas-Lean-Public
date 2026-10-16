module

public import LeanResearch.RepulsiveCoulomb.PointSectorReturnCleanRay
public import LeanResearch.RepulsiveCoulomb.PointFirstReturnCapAdapter
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-! Isolated, uncompiled successor. The actual old-boundary clock orientation
is constructed; the first-return extraction's s != t is not strengthened by
assumption. A clean ray avoiding the return endpoint must occupy the opposite
unbounded old end. -/
noncomputable section
open Set
open scoped NNReal
namespace RepulsiveCoulomb

/-- A continuous boundary clock based at s, avoiding both s after time zero
and the return parameter t>s, must remain below s. The alternative would trap
the escaping clean ray in the ACTUAL compact old arc b '' [s,t]. -/
theorem escaping_boundary_clock_before_return
    (b : ℝ → ℂ) (hb : Continuous b)
    (ρ : ℝ≥0 → ℂ) (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (hρf : ∀ u, ρ u = b (f u)) {s t : ℝ} (hst : s < t) (hf0 : f 0 = s)
    (hbase : ∀ u : ℝ≥0, 0 < u → f u ≠ s)
    (hreturn : ∀ u : ℝ≥0, f u ≠ t)
    (hescape : ∀ K : Set ℂ, IsCompact K → ∃ u : ℝ≥0, 0 < u ∧ ρ u ∉ K) :
    ∀ u : ℝ≥0, 0 < u → f u < s := by
  have hft (u : ℝ≥0) : f u < t := by
    by_contra hn
    have hI : t ∈ Icc (f 0) (f u) := by rw [hf0]; exact ⟨hst.le, le_of_not_gt hn⟩
    obtain ⟨v, _, hv⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ u from zero_le)
      hf.continuousOn hI
    exact hreturn v hv
  let S := f '' Ioi (0 : ℝ≥0)
  have hS : IsPreconnected S := isPreconnected_Ioi.image f hf.continuousOn
  have hdisj : Disjoint (Iio s) (Ioi s) := by
    apply disjoint_left.mpr
    intro x hx hy
    change x < s at hx
    change s < x at hy
    exact lt_asymm hx hy
  have hcover : S ⊆ Iio s ∪ Ioi s := by
    rintro x ⟨u, hu, rfl⟩
    exact lt_or_gt_of_ne (hbase u hu)
  rcases IsPreconnected.subset_or_subset isOpen_Iio isOpen_Ioi hdisj hcover hS with hlow | hhigh
  · exact fun u hu => hlow ⟨u, hu, rfl⟩
  · have hK : IsCompact (b '' Icc s t) := isCompact_Icc.image hb
    obtain ⟨u, hu, hnot⟩ := hescape (b '' Icc s t) hK
    exact False.elim (hnot ⟨f u, ⟨(hhigh ⟨u, hu, rfl⟩).le, (hft u).le⟩, (hρf u).symm⟩)

/-- Both old parameter orientations are covered. Reversing the boundary
clock changes neither the actual clean ray nor the actual old arc. -/
theorem escaping_boundary_clock_opposite_return
    (b : ℝ → ℂ) (hb : Continuous b)
    (ρ : ℝ≥0 → ℂ) (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (hρf : ∀ u, ρ u = b (f u)) {s t : ℝ} (hst : s ≠ t) (hf0 : f 0 = s)
    (hbase : ∀ u : ℝ≥0, 0 < u → f u ≠ s)
    (hreturn : ∀ u : ℝ≥0, f u ≠ t)
    (hescape : ∀ K : Set ℂ, IsCompact K → ∃ u : ℝ≥0, 0 < u ∧ ρ u ∉ K) :
    (s < t ∧ ∀ u : ℝ≥0, 0 < u → f u < s) ∨
      (t < s ∧ ∀ u : ℝ≥0, 0 < u → s < f u) := by
  rcases lt_or_gt_of_ne hst with hst | hts
  · exact Or.inl ⟨hst, escaping_boundary_clock_before_return b hb ρ f hf hρf hst hf0
      hbase hreturn hescape⟩
  · have hrev := escaping_boundary_clock_before_return
      (fun x : ℝ => b (-x)) (hb.comp continuous_neg) ρ (fun u => -f u) hf.neg
      (by intro u; simpa only [neg_neg] using hρf u)
      (show -s < -t by linarith) (by rw [hf0])
      (by intro u hu he; apply hbase u hu; linarith)
      (by intro u he; apply hreturn u; linarith) hescape
    exact Or.inr ⟨hts, fun u hu => by have h := hrev u hu; linarith⟩

/-- Reflection of an arbitrary continuous boundary parametrization preserves
its actual forward compact arc, including its original unit-interval clock. -/
theorem sectorReturn_reverse_boundary_clock_arc (b : ℝ → ℂ) (s t : ℝ) :
    lineCapSegment (fun x : ℝ => b (-x)) (-s) (-t) = lineCapSegment b s t := by
  funext u
  apply congrArg b
  change -(-s + u.1 * (-t - -s)) = s + u.1 * (t - s)
  ring

/-- A supplied ambient halfplane straightening gives a canonical actual
boundary parametrization and a continuous real clock for every boundary ray.
No order of its two ends is imposed here. -/
theorem straightened_halfplane_actual_boundary_clock
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hP : P = H ⁻¹' planarClosedUpperHalfplane)
    (ρ : ℝ≥0 → ℂ) (hρ : Continuous ρ) (hρfront : ∀ u, ρ u ∈ frontier P) :
    ∃ b : ℝ → ℂ, Continuous b ∧ Function.Injective b ∧ range b = frontier P ∧
      ∃ f : ℝ≥0 → ℝ, Continuous f ∧ (∀ u, ρ u = b (f u)) := by
  have hfront : frontier P = {z : ℂ | (H z).im = 0} := by
    rw [hP, ← H.preimage_frontier]
    change H ⁻¹' frontier {z : ℂ | (0 : ℝ) ≤ z.im} = _
    rw [Complex.frontier_setOfPred_le_im]
    rfl
  let b : ℝ → ℂ := fun s => H.symm (s : ℂ)
  have hb : Continuous b := H.symm.continuous.comp Complex.continuous_ofReal
  have hbi : Function.Injective b := H.symm.injective.comp Complex.ofReal_injective
  have hbreal (z : ℂ) (hz : z ∈ frontier P) : b (H z).re = z := by
    have him : (H z).im = 0 := by
      rw [hfront] at hz
      exact hz
    have he : ((H z).re : ℂ) = H z := by
      apply Complex.ext <;> simp [him]
    dsimp [b]
    rw [he, H.symm_apply_apply]
  have hboundary : range b = frontier P := by
    apply Subset.antisymm
    · rintro z ⟨s, rfl⟩
      rw [hfront]
      change (H (H.symm (s : ℂ))).im = 0
      simp
    · intro z hz
      exact ⟨(H z).re, hbreal z hz⟩
  let f : ℝ≥0 → ℝ := fun u => (H (ρ u)).re
  exact ⟨b, hb, hbi, hboundary, f,
    Complex.continuous_re.comp (H.continuous.comp hρ),
    fun u => (hbreal (ρ u) (hρfront u)).symm⟩

end RepulsiveCoulomb
