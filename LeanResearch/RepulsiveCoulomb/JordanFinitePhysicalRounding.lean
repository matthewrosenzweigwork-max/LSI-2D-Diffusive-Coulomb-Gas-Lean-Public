module

public import LeanResearch.RepulsiveCoulomb.JordanPhysicalCornerMap
public import LeanResearch.RepulsiveCoulomb.JordanPhysicalCornerTurn
public import LeanResearch.RepulsiveCoulomb.JordanFiniteCornerWidths
public import LeanResearch.RepulsiveCoulomb.JordanSplitCornerEdges
public import LeanResearch.RepulsiveCoulomb.JordanCornerReplacementHomotopy

@[expose] public section

/-! Constructed simultaneous rounding for arbitrary regular C1 non-antipodal
corners. The additive real maps need no injectivity or conformality. Positivity
of actual physical projections provides precisely the missing local geometry.
Records-only uncompiled candidate. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

theorem exists_simultaneous_physical_C1_rounding
    {ι : Type*} [Finite ι] (σ : Equiv.Perm ι) (hσ : ∀ i, σ i ≠ i)
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 1 (f i))
    (hend : ∀ i, f i 1 = f (σ i) 0)
    (hreg : ∀ i t, t ∈ Icc (0 : ℝ) 1 → deriv (f i) t ≠ 0)
    (hinj : ∀ i j s t, s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      f i s = f j t → i = j ∧ s = t)
    (hc : ∀ i, deriv (f i) 0 / deriv (f (σ.symm i)) 1 ∈ Complex.slitPlane)
    (w : ℂ) (hw : w ∉ ⋃ i, f i '' Icc (0 : ℝ) 1) :
    ∃ (δ : ℝ) (c : ι → ℂ) (C E : ι → ℝ → ℂ),
      0 < δ ∧ δ < 1 / 4 ∧
      (∀ i, ContDiff ℝ 1 (C i)) ∧
      (∀ i, ContDiff ℝ 1 (E i)) ∧
      (∀ i t, t ∈ Icc (0 : ℝ) 1 → deriv (E i) t ≠ 0) ∧
      (∀ i, E i 1 = E (σ i) 0) ∧
      (∀ i, deriv (E i) 1 = deriv (E (σ i)) 0) ∧
      (∀ i j s t, s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
        E i s = E j t → i = j ∧ s = t) ∧
      (∀ i t, t ∈ Icc δ (1 - δ) → E i t = f i t) ∧
      (∀ i t, t ∈ Icc (0 : ℝ) δ → E i t = C i t) ∧
      (∀ i t, t ∈ Icc (1 - δ) 1 → E i t = C (σ i) (t - 1)) ∧
      (∀ i t, t ∈ Icc (-δ) δ → C i t =
        finitePhysicalCornerMap σ f i (euclideanSymmetricCornerPatch δ 1 Complex.I t)) ∧
      (∀ i t, t ∈ Icc (0 : ℝ) 1 → E i t ≠ w) ∧
      (∀ i t, t ∈ Icc (1 - δ) 1 → deriv (f (σ.symm i)) t ∈ physicalHalfplane (c i)) ∧
      (∀ i t, t ∈ Icc (0 : ℝ) δ → deriv (f i) t ∈ physicalHalfplane (c i)) ∧
      (∀ i t, t ∈ Icc (1 - δ) 1 → deriv (E (σ.symm i)) t ∈ physicalHalfplane (c i)) ∧
      (∀ i t, t ∈ Icc (0 : ℝ) δ → deriv (E i) t ∈ physicalHalfplane (c i)) ∧
      ∀ i, ∃ F : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → ℂ, Continuous F ∧
        (∀ t, F (0, t) = finitePhysicalCornerMap σ f i
          (euclideanRadialCorner (δ • (1 : ℂ)) (δ • Complex.I) t)) ∧
        (∀ t, F (1, t) = finitePhysicalCornerMap σ f i
          (euclideanBezierCorner (δ • (1 : ℂ)) (δ • Complex.I) t)) ∧
        (∀ s, F (s, 0) = f (σ.symm i) (1 - δ)) ∧
        (∀ s, F (s, 1) = f i δ) ∧ ∀ q, F q ≠ w := by
  classical
  choose c hcin hcout using fun i =>
    exists_physical_common_halfplane (hreg (σ.symm i) 1 (by norm_num)) (hc i)
  let H := finitePhysicalCornerMap σ f
  let L := finitePhysicalIncoming σ f
  have hL (i : ι) : ContDiff ℝ 1 (L i) := finitePhysicalIncoming_contDiff σ hf i
  have hL0 (i : ι) : L i 0 = f i 0 := by
    simpa [L, finitePhysicalIncoming] using hend (σ.symm i)
  have hLd (i : ι) (t : ℝ) : deriv (L i) t = deriv (f (σ.symm i)) (1 + t) :=
    finitePhysicalIncoming_deriv σ f i t
  let V : ι → Set ℂ := fun i =>
    {z | 0 < (c i * deriv (L i) z.re).re ∧ 0 < (c i * deriv (f i) z.im).re}
  have hV (i : ι) : IsOpen (V i) := by
    apply IsOpen.and
    · exact isOpen_lt continuous_const
        (Complex.continuous_re.comp (continuous_const.mul ((hL i).continuous_deriv_one.comp Complex.continuous_re)))
    · exact isOpen_lt continuous_const
        (Complex.continuous_re.comp (continuous_const.mul ((hf i).continuous_deriv_one.comp Complex.continuous_im)))
  have h0V (i : ι) : (0 : ℂ) ∈ V i := by
    change 0 < (c i * deriv (L i) 0).re ∧ 0 < (c i * deriv (f i) 0).re
    rw [hLd, add_zero]
    exact ⟨hcin i, hcout i⟩
  have hH (i : ι) : Continuous (H i) := finitePhysicalCornerMap_continuous σ (fun i => (hf i).continuous) i
  have hH0 (i : ι) : H i 0 = f i 0 := by
    simpa using (finitePhysicalCornerMap_axes σ f hend i 0).2
  have hout (i : ι) : f i =ᶠ[𝓝 (0 : ℝ)] (fun t => H i (t • Complex.I)) :=
    Filter.Eventually.of_forall (fun t => (finitePhysicalCornerMap_axes σ f hend i t).2.symm)
  have hin (i : ι) : (fun t => f i (1 + t)) =ᶠ[𝓝 (0 : ℝ)] (fun t => H (σ i) (t • (1 : ℂ))) :=
    Filter.Eventually.of_forall (fun t => by
      simpa only [σ.symm_apply_apply] using (finitePhysicalCornerMap_axes σ f hend (σ i) t).1.symm)
  obtain ⟨a, r, R, ρ, δ, ha, haq, hr, hR, hρ, hρR, hδ, hδa, hδq,
      hwindow, _, _, _, hRV, _, havoid, hdisj, hlocal, hnorm⟩ :=
    exists_finite_radial_corner_rounding_parameters σ hσ f (fun i => (hf i).continuous)
      hend hinj w hw V hV h0V H (fun i => (hH i).continuousOn) hH0
      (fun _ => 1) (fun _ => Complex.I) hout hin
  have hposL (i : ι) (t : ℝ) (ht : |t| ≤ 2 * a) :
      0 < (c i * deriv (L i) t).re := by
    have h := (hwindow i t ht).1
    change 0 < (c i * deriv (L i) ((t • (1 : ℂ)).re)).re ∧ _ at h
    simpa using h.1
  have hposR (i : ι) (t : ℝ) (ht : |t| ≤ 2 * a) :
      0 < (c i * deriv (f i) t).re := by
    have h := (hwindow i t ht).2.1
    change _ ∧ 0 < (c i * deriv (f i) ((t • Complex.I).im)).re at h
    simpa using h.2
  have hLP (i : ι) (t : ℝ) (ht : t ∈ Icc (-δ) 0) :
      0 < (c i * deriv (L i) t).re := hposL i t (abs_le.mpr (by constructor <;> linarith [ht.1, ht.2]))
  have hRP (i : ι) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) δ) :
      0 < (c i * deriv (f i) t).re := hposR i t (abs_le.mpr (by constructor <;> linarith [ht.1, ht.2]))
  choose C hC hCL hCR hCP hCD hCpos using fun i =>
    exists_C1_physical_corner_patch (hL i) (hf i) (hL0 i) rfl (c i) hδ (hLP i) (hRP i)
  have hCPH (i : ι) (t : ℝ) (ht : t ∈ Icc (-δ) δ) :
      C i t = H i (euclideanSymmetricCornerPatch δ 1 Complex.I t) :=
    (hCP i t ht).trans (physicalCornerPatch_eq_map _ _ _ _ _)
  have hCLnext (i : ι) (t : ℝ) (ht : t ≤ -δ) : C (σ i) t = f i (t + 1) := by
    simpa [L, finitePhysicalIncoming, add_comm] using hCL (σ i) t ht
  have hCreg (i : ι) (t : ℝ) (ht : t ∈ Icc (-δ) δ) : deriv (C i) t ≠ 0 := by
    intro hz
    have h := hCpos i t ht
    simpa [hz] using h
  have hCinj (i : ι) : InjOn (C i) (Icc (-δ) δ) := by
    intro s hs t ht heq
    exact (complex_curve_strictMono_projection
      ((hC i).differentiable (by norm_num)) (c i) (hCpos i)).injOn hs ht
      (congrArg (fun z : ℂ => (c i * z).re) heq)
  have hCmem (i : ι) (t : ℝ) (ht : t ∈ Icc (-δ) δ) : C i t ∈ H i '' closedBall (0 : ℂ) R := by
    refine ⟨euclideanSymmetricCornerPatch δ 1 Complex.I t, ?_, (hCPH i t ht).symm⟩
    rw [mem_closedBall_zero_iff]
    exact (euclideanBezierCorner_norm_le hρ.le (hnorm i).1 (hnorm i).2
      (physicalCornerClock_mem hδ ht)).trans hρR.le
  have hCjoint : ∀ i j s t, s ∈ Ioo (-δ) δ → t ∈ Ioo (-δ) δ →
      C i s = C j t → i = j ∧ s = t := by
    intro i j s t hs ht heq
    have hij : i = j := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj hne) (hCmem i s (Ioo_subset_Icc_self hs))
        (heq.symm ▸ hCmem j t (Ioo_subset_Icc_self ht))
    subst j
    exact ⟨rfl, hCinj i (Ioo_subset_Icc_self hs) (Ioo_subset_Icc_self ht) heq⟩
  have hCmiddle : ∀ i j s t, s ∈ Ioo (-δ) δ → t ∈ Icc δ (1 - δ) → C i s ≠ f j t := by
    intro i j s t hs ht heq
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨hδ.le.trans ht.1, ht.2.trans (by linarith)⟩
    have hhit : f j t ∈ H i '' closedBall (0 : ℂ) R := heq ▸ hCmem i s (Ioo_subset_Icc_self hs)
    have hmonoP := complex_curve_strictMono_projection
      ((hC i).differentiable (by norm_num)) (c i) (hCpos i)
    rcases hlocal i j t ht01 hhit with ⟨hji, hta⟩ | ⟨hsji, hat⟩
    · subst j
      have hmonoR := complex_curve_strictMono_projection
        ((hf i).differentiable (by norm_num)) (c i)
        (a := (0 : ℝ)) (b := 2 * a)
        (fun x hx => hposR i x (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩))
      have hless := hmonoP (Ioo_subset_Icc_self hs)
        (show δ ∈ Icc (-δ) δ by constructor <;> linarith) hs.2
      change (c i * C i s).re < (c i * C i δ).re at hless
      rw [hCR i δ le_rfl] at hless
      have hle := hmonoR.monotoneOn
        (show δ ∈ Icc (0 : ℝ) (2 * a) by constructor <;> linarith)
        (show t ∈ Icc (0 : ℝ) (2 * a) by constructor <;> linarith [ht.1]) ht.1
      change (c i * f i δ).re ≤ (c i * f i t).re at hle
      rw [heq] at hless
      linarith
    · have hji : j = σ.symm i := by simpa using congrArg σ.symm hsji
      subst j
      have hmonoL := complex_curve_strictMono_projection
        ((hL i).differentiable (by norm_num)) (c i)
        (a := -2 * a) (b := (0 : ℝ))
        (fun x hx => hposL i x (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩))
      have hless := hmonoP (show -δ ∈ Icc (-δ) δ by constructor <;> linarith)
        (Ioo_subset_Icc_self hs) hs.1
      change (c i * C i (-δ)).re < (c i * C i s).re at hless
      rw [hCL i (-δ) le_rfl] at hless
      have hle := hmonoL.monotoneOn
        (show t - 1 ∈ Icc (-2 * a) (0 : ℝ) by constructor <;> linarith [ht.2])
        (show -δ ∈ Icc (-2 * a) (0 : ℝ) by constructor <;> linarith)
        (show t - 1 ≤ -δ by linarith [ht.2])
      have hLt : L i (t - 1) = f (σ.symm i) t := by simp [L, finitePhysicalIncoming]
      change (c i * L i (t - 1)).re ≤ (c i * L i (-δ)).re at hle
      rw [hLt] at hle
      rw [heq] at hless
      linarith
  let E := euclideanSplitCornerEdges σ C
  have hE (i : ι) := euclideanSplitCornerEdges_properties σ f C hδ (by linarith)
    hf hC hCR hCLnext hreg hCreg i
  have hEL (i : ι) := (hE i).2.2.2.2.2.2.2.1
  have hER (i : ι) := (hE i).2.2.2.2.2.2.2.2
  have hmid (i : ι) := (hE i).2.2.2.2.2.2.1
  have hEposR (i : ι) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) δ) : deriv (E i) t ∈ physicalHalfplane (c i) := by
    have he := physical_deriv_eq_of_eqOn_Icc hδ ht
      ((hE i).1.differentiable (by norm_num) t) ((hC i).differentiable (by norm_num) t) (hEL i)
    rw [he]
    exact hCpos i t ⟨by linarith [ht.1], ht.2⟩
  have hEposL (i : ι) (t : ℝ) (ht : t ∈ Icc (1 - δ) 1) :
      deriv (E (σ.symm i)) t ∈ physicalHalfplane (c i) := by
    have hshift : ContDiff ℝ 1 (fun x => C i (x - 1)) := by have h := hC i; fun_prop
    have he := physical_deriv_eq_of_eqOn_Icc (show 1 - δ < 1 by linarith) ht
      ((hE (σ.symm i)).1.differentiable (by norm_num) t)
      (hshift.differentiable (by norm_num) t)
      (fun x hx => by simpa only [σ.apply_symm_apply] using hER (σ.symm i) x hx)
    rw [he, deriv_comp_sub_const]
    exact hCpos i (t - 1) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hEa (i : ι) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : E i t ≠ w := by
    change euclideanSplitCornerEdges σ C i t ≠ w
    by_cases htd : t ≤ δ
    · rw [hEL i t ⟨ht.1, htd⟩]
      intro heq
      exact havoid i (heq ▸ hCmem i t ⟨by linarith [ht.1], htd⟩)
    by_cases hdt : 1 - δ ≤ t
    · rw [hER i t ⟨hdt, ht.2⟩]
      intro heq
      exact havoid (σ i) (heq ▸ hCmem (σ i) (t - 1) ⟨by linarith, by linarith [ht.2]⟩)
    rw [hmid i t ⟨(not_le.mp htd).le, (not_le.mp hdt).le⟩]
    intro heq
    exact hw (mem_iUnion.mpr ⟨i, t, ht, heq⟩)
  refine ⟨δ, c, C, E, hδ, hδq, hC, fun i => (hE i).1,
    fun i => (hE i).2.1, ?_, ?_, ?_, hmid, hEL, hER, hCPH, hEa, ?_, hRP, hEposL, hEposR, ?_⟩
  · intro i
    exact (hE i).2.2.2.1.trans (hE (σ i)).2.2.1.symm
  · intro i
    exact (hE i).2.2.2.2.2.1.trans (hE (σ i)).2.2.2.2.1.symm
  · exact euclideanSplitCornerEdges_joint_injective σ f C hδ (by linarith)
      hf hC hCR hCLnext hinj hCjoint hCmiddle
  · intro i t ht
    have h := hLP i (t - 1) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [hLd, show 1 + (t - 1) = t by ring] at h
    exact h
  · intro i
    have hball : ball (0 : ℂ) R ⊆ V i := ball_subset_closedBall.trans (hRV i)
    obtain ⟨F, hF, hF0, hF1, hFs, hFt, hFw⟩ :=
      exists_chart_corner_replacement_homotopy hρ.le hρR (hnorm i).1 (hnorm i).2
        ((hH i).continuousOn) (fun h => havoid i ((image_mono ball_subset_closedBall) h))
    refine ⟨F, hF, hF0, hF1, ?_, ?_, hFw⟩
    · intro s
      rw [hFs]
      have he := (finitePhysicalCornerMap_axes σ f hend i (-δ)).1
      simpa only [neg_smul, show 1 + -δ = 1 - δ by ring] using he
    · intro s
      exact (hFt s).trans (finitePhysicalCornerMap_axes σ f hend i δ).2

end RepulsiveCoulomb
