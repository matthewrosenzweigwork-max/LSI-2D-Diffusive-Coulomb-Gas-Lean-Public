import LeanResearch.RepulsiveCoulomb.JordanFiniteCornerWidths
import LeanResearch.RepulsiveCoulomb.JordanSplitCornerEdges
import LeanResearch.RepulsiveCoulomb.JordanC1RadialCornerPatch
import LeanResearch.RepulsiveCoulomb.JordanCornerReplacementHomotopy

/-! Actual simultaneous rounding with the original radial windows retained.
Unlike a geometry-only existence statement, this conclusion retains the exact
old-arc source formulas throughout the entire chosen cut, and one actual
simply connected chart disk containing all three replacement traces. These
witnesses are needed to transport turns and cannot be inferred from mere
endpoint matching or equality of the rounded patch to a quadratic.
Actual simultaneous rounding of a finite simple radial-chart family.
The common cut, disjoint neighborhoods, regular corner patches, cyclic matched
jets, joint simplicity, and avoiding local homotopies are all constructed.
No global rounded family or separation certificate is assumed. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RepulsiveCoulomb

/-- A finite actual noncuspidal radial-chart family admits simultaneous C¹
rounding. The new edge endpoints are the actual corner-patch midpoints, which
makes every cyclic endpoint derivative match literally. The original middle
of every edge remains unchanged, and the whole new family avoids the chosen
point. The final local homotopies are actual chart-transported maps. -/
theorem exists_simultaneous_radial_C1_rounding_with_windows
    {ι : Type*} [Finite ι] (σ : Equiv.Perm ι) (hσ : ∀ i, σ i ≠ i)
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 1 (f i))
    (hend : ∀ i, f i 1 = f (σ i) 0)
    (hreg : ∀ i t, t ∈ Icc (0 : ℝ) 1 → deriv (f i) t ≠ 0)
    (hinj : ∀ i j s t, s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
      f i s = f j t → i = j ∧ s = t)
    (w : ℂ) (hw : w ∉ ⋃ i, f i '' Icc (0 : ℝ) 1)
    (V : ι → Set ℂ) (hV : ∀ i, IsOpen (V i)) (h0V : ∀ i, (0 : ℂ) ∈ V i)
    (H : ι → ℂ → ℂ) (hH : ∀ i, AnalyticOnNhd ℂ (H i) (V i))
    (hHreg : ∀ i z, z ∈ V i → deriv (H i) z ≠ 0)
    (hHinj : ∀ i, InjOn (H i) (V i)) (hH0 : ∀ i, H i 0 = f i 0)
    (u v : ι → ℂ) (hu : ∀ i, u i ≠ 0)
    (hc : ∀ i, v i / u i ∈ Complex.slitPlane)
    (hout : ∀ i, f i =ᶠ[𝓝 (0 : ℝ)] (fun t => H i (t • v i)))
    (hin : ∀ i, (fun t => f i (1 + t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => H (σ i) (t • u (σ i)))) :
    ∃ (δ : ℝ) (C E : ι → ℝ → ℂ),
      0 < δ ∧ δ < 1 / 4 ∧
      (∀ i, ContDiff ℝ 1 (C i)) ∧
      (∀ i t, t ≤ -δ → C i t = f (σ.symm i) (1 + t)) ∧
      (∀ i t, δ ≤ t → C i t = f i t) ∧
      (∀ i t, t ∈ Icc (-δ) δ →
        C i t = H i (euclideanSymmetricCornerPatch δ (u i) (v i) t)) ∧
      (∀ i t, t ∈ Icc (-δ) δ → deriv (C i) t ≠ 0) ∧
      (∀ i, E i = euclideanSplitCornerEdges σ C i) ∧
      (∀ i, ContDiff ℝ 1 (E i)) ∧
      (∀ i t, t ∈ Icc (0 : ℝ) 1 → deriv (E i) t ≠ 0) ∧
      (∀ i, E i 1 = E (σ i) 0) ∧
      (∀ i, deriv (E i) 1 = deriv (E (σ i)) 0) ∧
      (∀ i j s t, s ∈ Ico (0 : ℝ) 1 → t ∈ Ico (0 : ℝ) 1 →
        E i s = E j t → i = j ∧ s = t) ∧
      (∀ i t, t ∈ Icc δ (1 - δ) → E i t = f i t) ∧
      (∀ i t, t ∈ Icc (0 : ℝ) δ → E i t = C i t) ∧
      (∀ i t, t ∈ Icc (1 - δ) 1 → E i t = C (σ i) (t - 1)) ∧
      (∀ i t, t ∈ Icc (0 : ℝ) 1 → E i t ≠ w) ∧
      (∀ i t, |t| ≤ δ →
        f (σ.symm i) (1 + t) = H i (t • u i) ∧ f i t = H i (t • v i)) ∧
      (∃ R : ℝ, 0 < R ∧ (∀ i, closedBall (0 : ℂ) R ⊆ V i) ∧
        ∀ i, ‖δ • u i‖ < R ∧ ‖δ • v i‖ < R) ∧
      ∀ i, ∃ F : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 → ℂ, Continuous F ∧
        (∀ t, F (0, t) = H i (euclideanRadialCorner (δ • u i) (δ • v i) t)) ∧
        (∀ t, F (1, t) = H i (euclideanBezierCorner (δ • u i) (δ • v i) t)) ∧
        (∀ s, F (s, 0) = f (σ.symm i) (1 - δ)) ∧
        (∀ s, F (s, 1) = f i δ) ∧ ∀ q, F q ≠ w := by
  classical
  obtain ⟨a, r, R, ρ, δ, ha, haq, hr, hR, hρ, hρR, hδ, hδa, hδq,
      hwindow, _, _, _, hRV, _, havoid, hdisj, hlocal, hnorm⟩ :=
    exists_finite_radial_corner_rounding_parameters σ hσ f
      (fun i => (hf i).continuous) hend hinj w hw V hV h0V H
      (fun i => (hH i).continuousOn) hH0 u v hout hin
  obtain ⟨hBV, hBi, hBdisj, hBavoid, hBmiddle⟩ :=
    finiteChartBezier_disjoint_retained_middles σ f V H u v w hδ hδa haq
      hρ hρR hwindow hRV havoid hdisj hlocal hnorm hHinj hu hc
  have hpatch (i : ι) : ∃ G : ℝ → ℂ, ContDiff ℝ 1 G ∧
      (∀ t, t ≤ -δ → G t = f (σ.symm i) (1 + t)) ∧
      (∀ t, δ ≤ t → G t = f i t) ∧
      (∀ t ∈ Icc (-δ) δ, G t = H i (euclideanSymmetricCornerPatch δ (u i) (v i) t)) ∧
      (∀ t ∈ Icc (-δ) δ, deriv G t ≠ 0) := by
    have hcuts := finite_radial_window_attachment_germs σ f V H u v hδ hδa hwindow i
    have hL : ContDiff ℝ 1 (fun t => f (σ.symm i) (1 + t)) := by
      have h := hf (σ.symm i)
      fun_prop
    obtain ⟨G, hG, hGL, hGR, hGP, hGD, _, _⟩ :=
      exists_C1_radial_corner_patch (hV i) (hH i) (hHreg i) (hHinj i)
        hδ (hu i) (hc i) (hBV i) hL (hf i) hcuts.1 hcuts.2.1
    exact ⟨G, hG, hGL, hGR, hGP, hGD⟩
  choose C hC hCL hCR hCP hCD using hpatch
  have hCLnext (i : ι) (t : ℝ) (ht : t ≤ -δ) : C (σ i) t = f i (t + 1) := by
    simpa only [σ.symm_apply_apply, add_comm] using hCL (σ i) t ht
  let A : ℝ → ℝ := fun t => (t + δ) / (2 * δ)
  have hA {t : ℝ} (ht : t ∈ Icc (-δ) δ) : A t ∈ Icc (0 : ℝ) 1 := by
    dsimp [A]
    exact ⟨div_nonneg (by linarith [ht.1]) (by positivity),
      (div_le_one (by positivity : 0 < 2 * δ)).mpr (by linarith [ht.2])⟩
  have hAo {t : ℝ} (ht : t ∈ Ioo (-δ) δ) : A t ∈ Ioo (0 : ℝ) 1 := by
    dsimp [A]
    exact ⟨div_pos (by linarith [ht.1]) (by positivity),
      (div_lt_one (by positivity : 0 < 2 * δ)).mpr (by linarith [ht.2])⟩
  have hCB (i : ι) (t : ℝ) (ht : t ∈ Icc (-δ) δ) :
      C i t = finiteChartBezier H u v δ i (A t) := hCP i t ht
  have hCinj : ∀ i j s t, s ∈ Ioo (-δ) δ → t ∈ Ioo (-δ) δ →
      C i s = C j t → i = j ∧ s = t := by
    intro i j s t hs ht heq
    rw [hCB i s (Ioo_subset_Icc_self hs), hCB j t (Ioo_subset_Icc_self ht)] at heq
    have hij : i = j := by
      by_contra hne
      exact Set.disjoint_left.mp (hBdisj hne)
        ⟨A s, Ioo_subset_Icc_self (hAo hs), rfl⟩
        ⟨A t, Ioo_subset_Icc_self (hAo ht), heq.symm⟩
    subst j
    have hparam := hBi i (Ioo_subset_Icc_self (hAo hs)) (Ioo_subset_Icc_self (hAo ht)) heq
    have he : s + δ = t + δ := (div_left_inj' (by positivity : 2 * δ ≠ 0)).mp hparam
    exact ⟨rfl, by linarith⟩
  have hCmiddle : ∀ i j s t, s ∈ Ioo (-δ) δ → t ∈ Icc δ (1 - δ) →
      C i s ≠ f j t := by
    intro i j s t hs ht heq
    exact Set.disjoint_left.mp (hBmiddle i j)
      ⟨A s, hAo hs, (hCB i s (Ioo_subset_Icc_self hs)).symm⟩ ⟨t, ht, heq.symm⟩
  have hCavoid (i : ι) (t : ℝ) (ht : t ∈ Icc (-δ) δ) : C i t ≠ w := by
    intro heq
    exact hBavoid i ⟨A t, hA ht, (hCB i t ht).symm.trans heq⟩
  let E := euclideanSplitCornerEdges σ C
  have hδhalf : δ < 1 / 2 := by linarith
  have hE (i : ι) := euclideanSplitCornerEdges_properties σ f C hδ hδhalf hf hC
    hCR hCLnext hreg hCD i
  refine ⟨δ, C, E, hδ, hδq, hC, hCL, hCR, hCP, hCD, fun _ => rfl,
    fun i => (hE i).1, fun i => (hE i).2.1, ?_, ?_, ?_,
    fun i => (hE i).2.2.2.2.2.2.1,
    fun i => (hE i).2.2.2.2.2.2.2.1,
    fun i => (hE i).2.2.2.2.2.2.2.2, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hE i).2.2.2.1.trans (hE (σ i)).2.2.1.symm
  · intro i
    exact (hE i).2.2.2.2.2.1.trans (hE (σ i)).2.2.2.2.1.symm
  · exact euclideanSplitCornerEdges_joint_injective σ f C hδ hδhalf hf hC
      hCR hCLnext hinj hCinj hCmiddle
  · intro i t ht
    change euclideanSplitCornerEdges σ C i t ≠ w
    by_cases htd : t ≤ δ
    · rw [(hE i).2.2.2.2.2.2.2.1 t ⟨ht.1, htd⟩]
      exact hCavoid i t ⟨by linarith [ht.1], htd⟩
    by_cases hdt : 1 - δ ≤ t
    · rw [(hE i).2.2.2.2.2.2.2.2 t ⟨hdt, ht.2⟩]
      exact hCavoid (σ i) (t - 1) ⟨by linarith, by linarith [ht.2]⟩
    rw [(hE i).2.2.2.2.2.2.1 t ⟨(not_le.mp htd).le, (not_le.mp hdt).le⟩]
    intro heq
    exact hw (mem_iUnion.mpr ⟨i, t, ht, heq⟩)
  · intro i t ht
    have hbound : |t| ≤ 2 * a := ht.trans (by linarith)
    exact (hwindow i t hbound).2.2
  · exact ⟨R, hR, hRV, fun i =>
      ⟨(hnorm i).1.trans_lt hρR, (hnorm i).2.trans_lt hρR⟩⟩
  · intro i
    have hballV : ball (0 : ℂ) R ⊆ V i := ball_subset_closedBall.trans (hRV i)
    have haw : w ∉ H i '' ball (0 : ℂ) R := fun hw => havoid i ((image_mono ball_subset_closedBall) hw)
    obtain ⟨F, hF, hF0, hF1, hFs, hFt, hFw⟩ :=
      exists_chart_corner_replacement_homotopy hρ.le hρR (hnorm i).1 (hnorm i).2
        ((hH i).continuousOn.mono hballV) haw
    have hcuts := finite_radial_window_attachment_germs σ f V H u v hδ hδa hwindow i
    refine ⟨F, hF, hF0, hF1, ?_, ?_, hFw⟩
    · intro s
      rw [hFs]
      simpa only [neg_smul] using hcuts.2.2.2.2.1.symm
    · intro s
      exact (hFt s).trans hcuts.2.2.2.2.2.symm

end RepulsiveCoulomb
