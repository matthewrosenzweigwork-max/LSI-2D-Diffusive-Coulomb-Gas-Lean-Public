module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Piecewise
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

/-! Inversion compactifies a closed embedded nonnegative real ray to a genuine
closed arc. The point at infinity is the endpoint `1`, mapped to `0`; all other
parameters use exactly `u / (1-u)`. -/
noncomputable section
open Set Topology Filter Function
open scoped NNReal
namespace RepulsiveCoulomb

/-- The inverse stereographic time parameter on the half-open unit interval.
Its arbitrary value at `1` is replaced in `compactifiedPlanarRay`. -/
def planarRayTime (u : unitInterval) : ℝ≥0 :=
  ⟨(u : ℝ) / (1 - (u : ℝ)), div_nonneg u.property.1 (sub_nonneg.mpr u.property.2)⟩

def planarRayParameter (t : ℝ≥0) : unitInterval :=
  ⟨(t : ℝ) / (1 + (t : ℝ)),
    div_nonneg t.property (by positivity),
    (div_le_one (by positivity : 0 < 1 + (t : ℝ))).mpr (by linarith)⟩

theorem planarRayParameter_ne_one (t : ℝ≥0) : planarRayParameter t ≠ 1 := by
  intro h
  have he := congrArg Subtype.val h
  have hl : (t : ℝ) / (1 + (t : ℝ)) < 1 :=
    (div_lt_one (by positivity : 0 < 1 + (t : ℝ))).mpr (by linarith)
  change (t : ℝ) / (1 + (t : ℝ)) = 1 at he
  exact (ne_of_lt hl) he

@[simp] theorem planarRayTime_parameter (t : ℝ≥0) :
    planarRayTime (planarRayParameter t) = t := by
  apply Subtype.ext
  change ((t : ℝ) / (1 + (t : ℝ))) / (1 - (t : ℝ) / (1 + (t : ℝ))) = t
  have hd : 1 + (t : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

@[simp] theorem planarRayTime_zero : planarRayTime 0 = 0 := by
  apply Subtype.ext
  simp [planarRayTime]

theorem planarRayTime_injOn : InjOn planarRayTime ({1}ᶜ : Set unitInterval) := by
  intro s hs t ht he
  have hs' : (s : ℝ) ≠ 1 := fun h => hs (Subtype.ext h)
  have ht' : (t : ℝ) ≠ 1 := fun h => ht (Subtype.ext h)
  have hds : 1 - (s : ℝ) ≠ 0 := sub_ne_zero.mpr hs'.symm
  have hdt : 1 - (t : ℝ) ≠ 0 := sub_ne_zero.mpr ht'.symm
  have he' := congrArg Subtype.val he
  change (s : ℝ) / (1 - (s : ℝ)) = (t : ℝ) / (1 - (t : ℝ)) at he'
  have hm := (div_eq_div_iff hds hdt).mp he'
  apply Subtype.ext
  nlinarith

theorem continuousAt_planarRayTime {u : unitInterval} (hu : u ≠ 1) :
    ContinuousAt planarRayTime u := by
  have hu' : (u : ℝ) ≠ 1 := fun h => hu (Subtype.ext h)
  have hd : 1 - (u : ℝ) ≠ 0 := sub_ne_zero.mpr hu'.symm
  exact (continuousAt_subtype_val.div
    (continuousAt_const.sub continuousAt_subtype_val) hd).codRestrict _

theorem tendsto_planarRayTime_one :
    Tendsto planarRayTime (𝓝[≠] (1 : unitInterval)) atTop := by
  have hv : Tendsto (fun u : unitInterval => (u : ℝ))
      (𝓝[≠] (1 : unitInterval)) (𝓝 1) :=
    continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hd : Tendsto (fun u : unitInterval => 1 - (u : ℝ))
      (𝓝[≠] (1 : unitInterval)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hv, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : (u : ℝ) ≠ 1 := fun h => hu (Subtype.ext h)
    exact sub_pos.mpr (lt_of_le_of_ne u.property.2 hu')
  have hi := hd.inv_tendsto_nhdsGT_zero
  have hsub := tendsto_atTop_add_const_right (𝓝[≠] (1 : unitInterval)) (-1 : ℝ) hi
  apply NNReal.tendsto_coe_atTop.mp
  apply hsub.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : (u : ℝ) ≠ 1 := fun h => hu (Subtype.ext h)
  have hd' : 1 - (u : ℝ) ≠ 0 := sub_ne_zero.mpr hu'.symm
  change (1 - (u : ℝ))⁻¹ + -1 = (u : ℝ) / (1 - (u : ℝ))
  field_simp
  <;> ring

/-- Complex inversion centered at `p`. -/
def planarInversion (p z : ℂ) : ℂ := (z - p)⁻¹

theorem planarInversion_injective (p : ℂ) : Injective (planarInversion p) := by
  intro x y h
  exact sub_left_inj.mp (inv_injective h)

theorem planarInversion_ne_zero {p z : ℂ} (h : z ≠ p) :
    planarInversion p z ≠ 0 := inv_ne_zero (sub_ne_zero.mpr h)

theorem continuousOn_planarInversion {A : Set ℂ} {p : ℂ} (hp : p ∉ A) :
    ContinuousOn (planarInversion p) A :=
  (continuous_id.sub continuous_const).continuousOn.inv₀
    (fun z hz => sub_ne_zero.mpr (by
      change z ≠ p
      intro he
      apply hp
      rwa [← he]))

/-- The continuous closed arc obtained by compactifying a proper embedded ray. -/
def compactifiedPlanarRay (p : ℂ) (γ : ℝ≥0 → ℂ) : unitInterval → ℂ :=
  Function.update (fun u => planarInversion p (γ (planarRayTime u))) 1 0

@[simp] theorem compactifiedPlanarRay_one (p : ℂ) (γ : ℝ≥0 → ℂ) :
    compactifiedPlanarRay p γ 1 = 0 := by simp [compactifiedPlanarRay]

theorem compactifiedPlanarRay_of_ne_one (p : ℂ) (γ : ℝ≥0 → ℂ)
    {u : unitInterval} (hu : u ≠ 1) :
    compactifiedPlanarRay p γ u = planarInversion p (γ (planarRayTime u)) :=
  Function.update_of_ne hu _ _

@[simp] theorem compactifiedPlanarRay_zero (p : ℂ) (γ : ℝ≥0 → ℂ) :
    compactifiedPlanarRay p γ 0 = planarInversion p (γ 0) := by
  rw [compactifiedPlanarRay_of_ne_one p γ (by norm_num), planarRayTime_zero]

theorem continuous_compactifiedPlanarRay {p : ℂ} {γ : ℝ≥0 → ℂ}
    (hγ : IsClosedEmbedding γ) (hp : p ∉ range γ) :
    Continuous (compactifiedPlanarRay p γ) := by
  have hne (t : ℝ≥0) : γ t ≠ p := fun h => hp ⟨t, h⟩
  have hγtop : Tendsto γ atTop (cocompact ℂ) := by
    simpa only [cocompact_eq_atTop] using hγ.tendsto_cocompact
  have hinv : Tendsto (fun t => planarInversion p (γ t)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hd := (tendsto_dist_right_cocompact_atTop p).comp hγtop
    have hdi := hd.inv_tendsto_atTop
    change Tendsto (fun t => (dist (γ t) p)⁻¹) atTop (𝓝 (0 : ℝ)) at hdi
    simpa only [planarInversion, norm_inv, ← dist_eq_norm] using hdi
  apply continuous_iff_continuousAt.mpr
  intro u
  by_cases hu : u = 1
  · subst u
    exact continuousAt_update_same.mpr (hinv.comp tendsto_planarRayTime_one)
  · apply (continuousAt_update_of_ne hu).mpr
    exact ((hγ.continuous.continuousAt.comp (continuousAt_planarRayTime hu)).sub
      continuousAt_const).inv₀ (sub_ne_zero.mpr (hne _))

theorem compactifiedPlanarRay_injective {p : ℂ} {γ : ℝ≥0 → ℂ}
    (hγ : Injective γ) (hp : p ∉ range γ) :
    Injective (compactifiedPlanarRay p γ) := by
  have hne (u : unitInterval) : planarInversion p (γ (planarRayTime u)) ≠ 0 :=
    planarInversion_ne_zero (fun h => hp ⟨_, h⟩)
  intro s t h
  by_cases hs : s = 1
  · by_cases ht : t = 1
    · exact hs.trans ht.symm
    · rw [hs, compactifiedPlanarRay_one, compactifiedPlanarRay_of_ne_one p γ ht] at h
      exact False.elim (hne t h.symm)
  · by_cases ht : t = 1
    · rw [ht, compactifiedPlanarRay_one, compactifiedPlanarRay_of_ne_one p γ hs] at h
      exact False.elim (hne s h)
    · rw [compactifiedPlanarRay_of_ne_one p γ hs,
        compactifiedPlanarRay_of_ne_one p γ ht] at h
      exact planarRayTime_injOn hs ht (hγ (planarInversion_injective p h))

theorem compactifiedPlanarRay_isClosedEmbedding {p : ℂ} {γ : ℝ≥0 → ℂ}
    (hγ : IsClosedEmbedding γ) (hp : p ∉ range γ) :
    IsClosedEmbedding (compactifiedPlanarRay p γ) :=
  (continuous_compactifiedPlanarRay hγ hp).isClosedEmbedding
    (compactifiedPlanarRay_injective hγ.injective hp)

theorem range_compactifiedPlanarRay (p : ℂ) (γ : ℝ≥0 → ℂ) :
    range (compactifiedPlanarRay p γ) = insert 0 (planarInversion p '' range γ) := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    by_cases hu : u = 1
    · simp [hu]
    · rw [compactifiedPlanarRay_of_ne_one p γ hu]
      exact Or.inr ⟨_, ⟨_, rfl⟩, rfl⟩
  · intro hz
    rcases hz with hz | ⟨_, ⟨t, rfl⟩, rfl⟩
    · exact ⟨1, by simpa using hz.symm⟩
    · refine ⟨planarRayParameter t, ?_⟩
      rw [compactifiedPlanarRay_of_ne_one p γ (planarRayParameter_ne_one t),
        planarRayTime_parameter]

theorem compactifiedPlanarRay_attachment {K : Set ℂ} {γ : ℝ≥0 → ℂ} {p q : ℂ}
    (hpK : p ∉ K) (hmeet : range γ ∩ K = {q}) :
    range (compactifiedPlanarRay p γ) ∩ (planarInversion p '' K) =
      {planarInversion p q} := by
  have hq : q ∈ range γ ∩ K := by rw [hmeet]; exact mem_singleton q
  rw [range_compactifiedPlanarRay]
  ext z
  constructor
  · rintro ⟨hz, k, hk, hkz⟩
    rcases hz with hz | ⟨r, hr, hrz⟩
    · have hkp : k ≠ p := by
        intro he
        apply hpK
        rwa [← he]
      exact False.elim ((planarInversion_ne_zero hkp) (hkz.trans hz))
    · have hrk : r = k := planarInversion_injective p (hrz.trans hkz.symm)
      have hrq : r = q := by
        apply mem_singleton_iff.mp
        rw [← hmeet]
        exact ⟨hr, by rwa [hrk]⟩
      exact mem_singleton_iff.mpr (hrz.symm.trans (congrArg (planarInversion p) hrq))
  · intro hz
    rw [mem_singleton_iff] at hz
    subst z
    exact ⟨Or.inr ⟨q, hq.1, rfl⟩, ⟨q, hq.2, rfl⟩⟩

end RepulsiveCoulomb
