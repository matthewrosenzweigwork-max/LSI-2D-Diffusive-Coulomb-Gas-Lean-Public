import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Maps.Proper.Basic

/-! ISOLATED SOURCE-ONLY DRAFT. Build the proper broken backward old end
BEFORE an unbounded strip has been constructed. Its compact edge and clean
escaping ray are actual old-boundary maps. No strip map is needed. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

def compactEdgeReverseClock {b : ℝ} (hb : 0 ≤ b) (t : NNReal) : Icc (0 : ℝ) b :=
  ⟨max (b - (t : ℝ)) 0, le_max_right _ _, max_le (sub_le_self _ t.2) hb⟩

def compactEdgeRayJoin {b : ℝ} (hb : 0 ≤ b)
    (e : Icc (0 : ℝ) b → ℂ) (ρ : NNReal → ℂ) (t : NNReal) : ℂ :=
  if (t : ℝ) ≤ b then e (compactEdgeReverseClock hb t) else ρ (((t : ℝ) - b).toNNReal)

theorem compactEdgeRayJoin_before {b : ℝ} (hb : 0 ≤ b)
    (e : Icc (0 : ℝ) b → ℂ) (ρ : NNReal → ℂ) (t : NNReal) (ht : (t : ℝ) ≤ b) :
    compactEdgeRayJoin hb e ρ t = e ⟨b - (t : ℝ), sub_nonneg.mpr ht, sub_le_self _ t.2⟩ := by
  simp only [compactEdgeRayJoin, if_pos ht, compactEdgeReverseClock, max_eq_left (sub_nonneg.mpr ht)]

theorem compactEdgeRayJoin_after {b : ℝ} (hb : 0 ≤ b)
    (e : Icc (0 : ℝ) b → ℂ) (ρ : NNReal → ℂ)
    (hzero : e ⟨0, le_rfl, hb⟩ = ρ 0) (t : NNReal) (ht : b ≤ (t : ℝ)) :
    compactEdgeRayJoin hb e ρ t = ρ ⟨(t : ℝ) - b, sub_nonneg.mpr ht⟩ := by
  by_cases htb : (t : ℝ) ≤ b
  · have he : (t : ℝ) = b := le_antisymm htb ht
    rw [compactEdgeRayJoin_before hb e ρ t htb]
    have hz : b - (t : ℝ) = 0 := by linarith
    have hz' : (t : ℝ) - b = 0 := by linarith
    have he0 : (⟨b - (t : ℝ), sub_nonneg.mpr htb, sub_le_self _ t.2⟩ :
        Icc (0 : ℝ) b) = ⟨0, le_rfl, hb⟩ := Subtype.ext hz
    have hr0 : (⟨(t : ℝ) - b, sub_nonneg.mpr ht⟩ : NNReal) = 0 :=
      Subtype.ext hz'
    rw [he0, hr0]
    exact hzero
  · simp only [compactEdgeRayJoin, if_neg htb]
    apply congrArg ρ
    apply Subtype.ext
    exact Real.coe_toNNReal _ (sub_nonneg.mpr ht)

theorem compactEdgeRayJoin_continuous {b : ℝ} (hb : 0 ≤ b)
    {e : Icc (0 : ℝ) b → ℂ} {ρ : NNReal → ℂ}
    (he : Continuous e) (hρ : Continuous ρ)
    (hzero : e ⟨0, le_rfl, hb⟩ = ρ 0) : Continuous (compactEdgeRayJoin hb e ρ) := by
  have hc : Continuous (compactEdgeReverseClock hb) := by
    apply Continuous.subtype_mk
    fun_prop
  apply Continuous.if_le (he.comp hc)
    (hρ.comp (continuous_real_toNNReal.comp (continuous_subtype_val.sub continuous_const)))
    continuous_subtype_val continuous_const
  intro t ht
  change (t : ℝ) = b at ht
  have hclock : compactEdgeReverseClock hb t = ⟨0, le_rfl, hb⟩ := by
    apply Subtype.ext
    simp [compactEdgeReverseClock, ht]
  change e (compactEdgeReverseClock hb t) = ρ (((t : ℝ) - b).toNNReal)
  rw [hclock, ht]
  simpa using hzero

/-- The exact image formula also proves closedness on every closed subset. -/
theorem compactEdgeRayJoin_image {b : ℝ} (hb : 0 ≤ b)
    (e : Icc (0 : ℝ) b → ℂ) (ρ : NNReal → ℂ)
    (hzero : e ⟨0, le_rfl, hb⟩ = ρ 0) (A : Set NNReal) :
    compactEdgeRayJoin hb e ρ '' A =
      e '' {u : Icc (0 : ℝ) b | (⟨b - u.1, sub_nonneg.mpr u.2.2⟩ : NNReal) ∈ A} ∪
      ρ '' {r : NNReal | (⟨b + r.1, add_nonneg hb r.2⟩ : NNReal) ∈ A} := by
  ext z
  constructor
  · rintro ⟨t, htA, rfl⟩
    rcases le_total (t : ℝ) b with ht | ht
    · left
      let u : Icc (0 : ℝ) b := ⟨b - t.1, sub_nonneg.mpr ht, sub_le_self _ t.2⟩
      refine ⟨u, ?_, (compactEdgeRayJoin_before hb e ρ t ht).symm⟩
      have hu : (⟨b - u.1, sub_nonneg.mpr u.2.2⟩ : NNReal) = t := by
        apply Subtype.ext
        dsimp [u]
        ring
      change (⟨b - u.1, sub_nonneg.mpr u.2.2⟩ : NNReal) ∈ A
      rwa [hu]
    · right
      let r : NNReal := ⟨t.1 - b, sub_nonneg.mpr ht⟩
      refine ⟨r, ?_, (compactEdgeRayJoin_after hb e ρ hzero t ht).symm⟩
      have hr : (⟨b + r.1, add_nonneg hb r.2⟩ : NNReal) = t := by
        apply Subtype.ext
        dsimp [r]
        ring
      change (⟨b + r.1, add_nonneg hb r.2⟩ : NNReal) ∈ A
      rwa [hr]
  · rintro (⟨u, hu, rfl⟩ | ⟨r, hr, rfl⟩)
    · let t : NNReal := ⟨b - u.1, sub_nonneg.mpr u.2.2⟩
      refine ⟨t, hu, ?_⟩
      rw [compactEdgeRayJoin_before hb e ρ t (by change b-u.1≤b; exact sub_le_self _ u.2.1)]
      apply congrArg e
      apply Subtype.ext
      change b - (b - u.1) = u.1
      ring
    · let t : NNReal := ⟨b + r.1, add_nonneg hb r.2⟩
      refine ⟨t, hr, ?_⟩
      rw [compactEdgeRayJoin_after hb e ρ hzero t (by change b≤b+r.1; linarith [r.2])]
      apply congrArg ρ
      apply Subtype.ext
      change b + r.1 - b = r.1
      ring

theorem compactEdgeRayJoin_injective {b : ℝ} (hb : 0 ≤ b)
    {e : Icc (0 : ℝ) b → ℂ} {ρ : NNReal → ℂ}
    (he : Function.Injective e) (hρ : Function.Injective ρ)
    (hzero : e ⟨0, le_rfl, hb⟩ = ρ 0)
    (hmeet : range e ∩ range ρ = {ρ 0}) : Function.Injective (compactEdgeRayJoin hb e ρ) := by
  have hcross {u : Icc (0 : ℝ) b} {r : NNReal} (h : e u = ρ r) : u.1 = 0 ∧ r = 0 := by
    have hp : e u = ρ 0 := mem_singleton_iff.mp (hmeet ▸ ⟨mem_range_self u, ⟨r, h.symm⟩⟩)
    exact ⟨congrArg Subtype.val (he (hp.trans hzero.symm)), hρ (h.symm.trans hp)⟩
  intro s t h
  by_cases hs : s.1 ≤ b <;> by_cases ht : t.1 ≤ b
  · rw [compactEdgeRayJoin_before hb e ρ s hs, compactEdgeRayJoin_before hb e ρ t ht] at h
    have heq := congrArg Subtype.val (he h)
    apply Subtype.ext
    change b - s.1 = b - t.1 at heq
    linarith
  · rw [compactEdgeRayJoin_before hb e ρ s hs,
      compactEdgeRayJoin_after hb e ρ hzero t (le_of_not_ge ht)] at h
    obtain ⟨hu, hr⟩ := hcross h
    have hr' := congrArg Subtype.val hr
    apply Subtype.ext
    change b - s.1 = 0 at hu
    change t.1 - b = 0 at hr'
    linarith
  · rw [compactEdgeRayJoin_after hb e ρ hzero s (le_of_not_ge hs),
      compactEdgeRayJoin_before hb e ρ t ht] at h
    obtain ⟨hu, hr⟩ := hcross h.symm
    have hr' := congrArg Subtype.val hr
    apply Subtype.ext
    change b - t.1 = 0 at hu
    change s.1 - b = 0 at hr'
    linarith
  · rw [compactEdgeRayJoin_after hb e ρ hzero s (le_of_not_ge hs),
      compactEdgeRayJoin_after hb e ρ hzero t (le_of_not_ge ht)] at h
    have heq := congrArg Subtype.val (hρ h)
    apply Subtype.ext
    change s.1 - b = t.1 - b at heq
    linarith

/-- Proper backward old boundary from a genuine compact edge and escaping
ray. Their only common point is the shared original corner. -/
theorem compactEdgeRayJoin_isClosedEmbedding {b : ℝ} (hb : 0 ≤ b)
    {e : Icc (0 : ℝ) b → ℂ} {ρ : NNReal → ℂ}
    (he : Continuous e) (hei : Function.Injective e) (hρ : IsClosedEmbedding ρ)
    (hzero : e ⟨0, le_rfl, hb⟩ = ρ 0)
    (hmeet : range e ∩ range ρ = {ρ 0}) : IsClosedEmbedding (compactEdgeRayJoin hb e ρ) := by
  have heclosed := he.isClosedEmbedding hei
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
    (compactEdgeRayJoin_continuous hb he hρ.continuous hzero)
    (compactEdgeRayJoin_injective hb hei hρ.injective hzero hmeet)
  intro A hA
  rw [compactEdgeRayJoin_image hb e ρ hzero]
  have hc₁ : Continuous (fun u : Icc (0 : ℝ) b ↦
      (⟨b - u.1, sub_nonneg.mpr u.2.2⟩ : NNReal)) := by fun_prop
  have hc₂ : Continuous (fun r : NNReal ↦ (⟨b + r.1, add_nonneg hb r.2⟩ : NNReal)) := by fun_prop
  exact (heclosed.isClosedMap _ (hA.preimage hc₁)).union
    (hρ.isClosedMap _ (hA.preimage hc₂))

end RepulsiveCoulomb
