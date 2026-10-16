module

public import LeanResearch.RepulsiveCoulomb.JordanC1Joining
public import Mathlib.Analysis.Calculus.Deriv.Shift

@[expose] public section

/-! Glue the two halves of neighboring actual corner patches through the
unchanged middle of each edge. Global C¹ and cyclic endpoint-jet matching are
constructed, not assumed. This is the concrete bridge from local equal-width
corner patches to the finite matched-jet family. Records-only candidate. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

def euclideanSplitCornerEdges {ι : Type*} (σ : ι → ι) (C : ι → ℝ → ℂ)
    (i : ι) : ℝ → ℂ := euclideanC1Glue (1 / 2) (C i) (fun t => C (σ i) (t - 1))

/-- The original middle is preserved, and the endpoint values and derivatives
are those of the two actual patch midpoints. Thus cyclic matching is literal. -/
theorem euclideanSplitCornerEdges_properties {ι : Type*}
    (σ : ι → ι) (f C : ι → ℝ → ℂ) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (hC : ∀ i, ContDiff ℝ 1 (C i))
    (hright : ∀ i t, δ ≤ t → C i t = f i t)
    (hleft : ∀ i t, t ≤ -δ → C (σ i) t = f i (t + 1))
    (hfreg : ∀ i t, t ∈ Icc (0 : ℝ) 1 → deriv (f i) t ≠ 0)
    (hCreg : ∀ i t, t ∈ Icc (-δ) δ → deriv (C i) t ≠ 0) (i : ι) :
    ContDiff ℝ 1 (euclideanSplitCornerEdges σ C i) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, deriv (euclideanSplitCornerEdges σ C i) t ≠ 0) ∧
      euclideanSplitCornerEdges σ C i 0 = C i 0 ∧
      euclideanSplitCornerEdges σ C i 1 = C (σ i) 0 ∧
      deriv (euclideanSplitCornerEdges σ C i) 0 = deriv (C i) 0 ∧
      deriv (euclideanSplitCornerEdges σ C i) 1 = deriv (C (σ i)) 0 ∧
      (∀ t ∈ Icc δ (1 - δ), euclideanSplitCornerEdges σ C i t = f i t) ∧
      (∀ t ∈ Icc (0 : ℝ) δ, euclideanSplitCornerEdges σ C i t = C i t) ∧
      (∀ t ∈ Icc (1 - δ) 1, euclideanSplitCornerEdges σ C i t = C (σ i) (t - 1)) := by
  let D : ℝ → ℂ := fun t => C (σ i) (t - 1)
  have hD : ContDiff ℝ 1 D := by have h := hC (σ i); dsimp [D]; fun_prop
  have hDD (t : ℝ) : deriv D t = deriv (C (σ i)) (t - 1) := deriv_comp_sub_const _ _ _
  have hCrad {t : ℝ} (ht : δ < t) : C i =ᶠ[𝓝 t] f i := by
    filter_upwards [lt_mem_nhds ht] with s hs
    exact hright i s hs.le
  have hDrad {t : ℝ} (ht : t < 1 - δ) : D =ᶠ[𝓝 t] f i := by
    filter_upwards [gt_mem_nhds ht] with s hs
    change C (σ i) (s - 1) = f i s
    simpa only [sub_add_cancel] using hleft i (s - 1) (by linarith)
  have hCmid := hCrad hδhalf
  have hDmid := hDrad (show (1 / 2 : ℝ) < 1 - δ by linarith)
  have hv : C i (1 / 2) = D (1 / 2) := hCmid.self_of_nhds.trans hDmid.self_of_nhds.symm
  have hd : deriv (C i) (1 / 2) = deriv D (1 / 2) := hCmid.deriv_eq.trans hDmid.deriv_eq.symm
  have hG : ContDiff ℝ 1 (euclideanSplitCornerEdges σ C i) :=
    euclideanC1Glue_contDiff (hC i) hD hv hd
  have hGD (t : ℝ) : deriv (euclideanSplitCornerEdges σ C i) t =
      if t ≤ 1 / 2 then deriv (C i) t else deriv D t :=
    euclideanC1Glue_deriv ((hC i).differentiable (by norm_num)) (hD.differentiable (by norm_num)) hv hd t
  refine ⟨hG, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [hGD]
    split_ifs with hmid
    · by_cases htd : t ≤ δ
      · exact hCreg i t ⟨by linarith [ht.1], htd⟩
      · rw [(hCrad (not_le.mp htd)).deriv_eq]
        exact hfreg i t ht
    · by_cases htd : 1 - δ ≤ t
      · rw [hDD]
        exact hCreg (σ i) (t - 1) ⟨by linarith, by linarith [ht.2]⟩
      · rw [(hDrad (not_le.mp htd)).deriv_eq]
        exact hfreg i t ht
  · exact euclideanC1Glue_eq_left _ _ _ (by norm_num)
  · have h := euclideanC1Glue_eq_right hv (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    simpa only [euclideanSplitCornerEdges, D, sub_self] using h
  · rw [hGD, if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  · rw [hGD, if_neg (by norm_num : ¬(1 : ℝ) ≤ 1 / 2), hDD, sub_self]
  · intro t ht
    change euclideanC1Glue (1 / 2) (C i) D t = f i t
    by_cases hmid : t ≤ 1 / 2
    · rw [euclideanC1Glue_eq_left _ _ _ hmid]
      exact hright i t ht.1
    · rw [euclideanC1Glue_eq_right hv (not_le.mp hmid).le]
      change C (σ i) (t - 1) = f i t
      simpa only [sub_add_cancel] using hleft i (t - 1) (by linarith [ht.2])
  · intro t ht
    exact euclideanC1Glue_eq_left _ _ _ (by linarith [ht.2])
  · intro t ht
    exact euclideanC1Glue_eq_right hv (by linarith [ht.1])

/-- Different actual old edge interiors and different actual patch interiors
are disjoint. Every patch interior misses every retained old middle. Under
these literal geometric hypotheses, the constructed new half-open edges are
jointly injective, so the whole cyclic family is genuinely simple. -/
theorem euclideanSplitCornerEdges_joint_injective {ι : Type*}
    (σ : Equiv.Perm ι) (f C : ι → ℝ → ℂ) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (hC : ∀ i, ContDiff ℝ 1 (C i))
    (hright : ∀ i t, δ ≤ t → C i t = f i t)
    (hleft : ∀ i t, t ≤ -δ → C (σ i) t = f i (t + 1))
    (hOld : ∀ i j s t, s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      f i s = f j t → i = j ∧ s = t)
    (hPatch : ∀ i j s t, s ∈ Ioo (-δ) δ → t ∈ Ioo (-δ) δ →
      C i s = C j t → i = j ∧ s = t)
    (hAvoid : ∀ i j s t, s ∈ Ioo (-δ) δ → t ∈ Icc δ (1 - δ) → C i s ≠ f j t)
    (i j : ι) {s t : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1)
    (heq : euclideanSplitCornerEdges σ C i s = euclideanSplitCornerEdges σ C j t) :
    i = j ∧ s = t := by
  have hvalues (k : ι) (x : ℝ) (hx : x ∈ Ico (0 : ℝ) 1) :
      (x < δ ∧ euclideanSplitCornerEdges σ C k x = C k x) ∨
      (1 - δ < x ∧ euclideanSplitCornerEdges σ C k x = C (σ k) (x - 1)) ∨
      (x ∈ Icc δ (1 - δ) ∧ euclideanSplitCornerEdges σ C k x = f k x) := by
    have hCrad : C k =ᶠ[𝓝 (1 / 2 : ℝ)] f k := by
      filter_upwards [lt_mem_nhds hδhalf] with y hy
      exact hright k y hy.le
    have hDrad : (fun y => C (σ k) (y - 1)) =ᶠ[𝓝 (1 / 2 : ℝ)] f k := by
      filter_upwards [gt_mem_nhds (show (1 / 2 : ℝ) < 1 - δ by linarith)] with y hy
      simpa only [sub_add_cancel] using hleft k (y - 1) (by linarith)
    have hv : C k (1 / 2) = C (σ k) (1 / 2 - 1) :=
      hCrad.self_of_nhds.trans hDrad.self_of_nhds.symm
    by_cases hxd : x < δ
    · exact Or.inl ⟨hxd, euclideanC1Glue_eq_left _ _ _ (by linarith)⟩
    by_cases hdx : 1 - δ < x
    · exact Or.inr (Or.inl ⟨hdx, euclideanC1Glue_eq_right hv (by linarith)⟩)
    have hmid : x ∈ Icc δ (1 - δ) := ⟨le_of_not_gt hxd, le_of_not_gt hdx⟩
    refine Or.inr (Or.inr ⟨hmid, ?_⟩)
    change euclideanC1Glue (1 / 2) (C k) (fun t => C (σ k) (t - 1)) x = f k x
    by_cases hxhalf : x ≤ 1 / 2
    · rw [euclideanC1Glue_eq_left _ _ _ hxhalf]
      exact hright k x hmid.1
    · rw [euclideanC1Glue_eq_right hv (not_le.mp hxhalf).le]
      simpa only [sub_add_cancel] using hleft k (x - 1) (by linarith [hmid.2])
  have hpos {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) (hxd : x < δ) : x ∈ Ioo (-δ) δ :=
    ⟨by linarith [hx.1], hxd⟩
  have hneg {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) (hxd : 1 - δ < x) : x - 1 ∈ Ioo (-δ) δ :=
    ⟨by linarith, by linarith [hx.2]⟩
  rcases hvalues i s hs with ⟨hsd, hse⟩ | ⟨hsd, hse⟩ | ⟨hsm, hse⟩ <;>
    rcases hvalues j t ht with ⟨htd, hte⟩ | ⟨htd, hte⟩ | ⟨htm, hte⟩ <;>
    rw [hse, hte] at heq
  · exact hPatch i j s t (hpos hs hsd) (hpos ht htd) heq
  · have h := (hPatch i (σ j) s (t - 1) (hpos hs hsd) (hneg ht htd) heq).2
    exfalso
    linarith [hs.1, ht.2]
  · exact (hAvoid i j s t (hpos hs hsd) htm heq).elim
  · have h := (hPatch (σ i) j (s - 1) t (hneg hs hsd) (hpos ht htd) heq).2
    exfalso
    linarith [hs.2, ht.1]
  · obtain ⟨hij, hst⟩ := hPatch (σ i) (σ j) (s - 1) (t - 1) (hneg hs hsd) (hneg ht htd) heq
    exact ⟨σ.injective hij, by linarith⟩
  · exact (hAvoid (σ i) j (s - 1) t (hneg hs hsd) htm heq).elim
  · exact (hAvoid j i t s (hpos ht htd) hsm heq.symm).elim
  · exact (hAvoid (σ j) i (t - 1) s (hneg ht htd) hsm heq.symm).elim
  · exact hOld i j s t hs ht heq

end RepulsiveCoulomb
