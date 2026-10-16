import LeanResearch.RepulsiveCoulomb.JordanC1GlueGeometry
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Actual C¹ regular embedded gluing of an unchanged incoming collar, a
middle arc with matched velocities, and an unchanged outgoing collar. The
three equal parameter slots retain exact affine radial endpoint germs.
Records-only candidate, not admitted or compiled. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

private theorem shifted_unit_image (f : ℝ → ℂ) (a : ℝ) :
    (fun t => f (t - a)) '' Icc a (a + 1) = f '' Icc (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    exact ⟨t - a, by constructor <;> linarith [ht.1, ht.2], rfl⟩
  · rintro z ⟨t, ht, rfl⟩
    exact ⟨t + a, by constructor <;> linarith [ht.1, ht.2], by congr 1; ring⟩

/-- Construct the whole gap arc, preserving both collar germs exactly (up to
the explicit affine factor3), rather than reparameterizing those collars. -/
theorem exists_three_piece_regular_C1_gap
    {L M R : ℝ → ℂ} (hL : ContDiff ℝ 1 L) (hM : ContDiff ℝ 1 M) (hR : ContDiff ℝ 1 R)
    (hLM : L 1 = M 0) (hMR : M 1 = R 0)
    (hjLM : deriv L 1 = deriv M 0) (hjMR : deriv M 1 = deriv R 0)
    (hLreg : ∀ t ∈ Icc (0 : ℝ) 1, deriv L t ≠ 0)
    (hMreg : ∀ t ∈ Icc (0 : ℝ) 1, deriv M t ≠ 0)
    (hRreg : ∀ t ∈ Icc (0 : ℝ) 1, deriv R t ≠ 0)
    (hLi : InjOn L (Icc (0 : ℝ) 1)) (hMi : InjOn M (Icc (0 : ℝ) 1))
    (hRi : InjOn R (Icc (0 : ℝ) 1))
    (hLMmeet : L '' Icc (0 : ℝ) 1 ∩ M '' Icc (0 : ℝ) 1 ⊆ {L 1})
    (hMRmeet : M '' Icc (0 : ℝ) 1 ∩ R '' Icc (0 : ℝ) 1 ⊆ {M 1})
    (hLR : Disjoint (L '' Icc (0 : ℝ) 1) (R '' Icc (0 : ℝ) 1)) :
    ∃ η : ℝ → ℂ, ContDiff ℝ 1 η ∧ InjOn η (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, deriv η t ≠ 0) ∧
      η 0 = L 0 ∧ η 1 = R 1 ∧
      η '' Icc (0 : ℝ) 1 =
        (L '' Icc (0 : ℝ) 1 ∪ M '' Icc (0 : ℝ) 1) ∪ R '' Icc (0 : ℝ) 1 ∧
      η =ᶠ[𝓝 (0 : ℝ)] (fun t => L (3 * t)) ∧
      η =ᶠ[𝓝 (1 : ℝ)] (fun t => R (3 * t - 2)) := by
  let Ms : ℝ → ℂ := fun t => M (t - 1)
  let Rs : ℝ → ℂ := fun t => R (t - 2)
  have hMs : ContDiff ℝ 1 Ms := by dsimp [Ms]; fun_prop
  have hRs : ContDiff ℝ 1 Rs := by dsimp [Rs]; fun_prop
  have hMsD (t : ℝ) : deriv Ms t = deriv M (t - 1) := deriv_comp_sub_const _ _ _
  have hRsD (t : ℝ) : deriv Rs t = deriv R (t - 2) := deriv_comp_sub_const _ _ _
  have hv1 : L 1 = Ms 1 := by simpa [Ms] using hLM
  have hd1 : deriv L 1 = deriv Ms 1 := by simpa only [hMsD, sub_self] using hjLM
  let A := euclideanC1Glue 1 L Ms
  have hA : ContDiff ℝ 1 A := euclideanC1Glue_contDiff hL hMs hv1 hd1
  have hv2 : A 2 = Rs 2 := by
    change euclideanC1Glue 1 L Ms 2 = Rs 2
    rw [euclideanC1Glue_eq_right hv1 (by norm_num : (1 : ℝ) ≤ 2)]
    simpa [Ms, Rs, show (2 : ℝ) - 1 = 1 by norm_num] using hMR
  have hd2 : deriv A 2 = deriv Rs 2 := by
    rw [euclideanC1Glue_deriv_right (hL.differentiable (by norm_num))
      (hMs.differentiable (by norm_num)) hv1 hd1 (by norm_num : (1 : ℝ) ≤ 2), hMsD, hRsD]
    norm_num
    exact hjMR
  let B := euclideanC1Glue 2 A Rs
  have hB : ContDiff ℝ 1 B := euclideanC1Glue_contDiff hA hRs hv2 hd2
  have hMsimage : Ms '' Icc (1 : ℝ) 2 = M '' Icc (0 : ℝ) 1 := by
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using shifted_unit_image M 1
  have hRsimage : Rs '' Icc (2 : ℝ) 3 = R '' Icc (0 : ℝ) 1 := by
    simpa only [show (2 : ℝ) + 1 = 3 by norm_num] using shifted_unit_image R 2
  have hAimage : A '' Icc (0 : ℝ) 2 = L '' Icc (0 : ℝ) 1 ∪ M '' Icc (0 : ℝ) 1 := by
    rw [euclideanC1Glue_interval_image (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) ≤ 2) hv1, hMsimage]
  have hBimage : B '' Icc (0 : ℝ) 3 =
      (L '' Icc (0 : ℝ) 1 ∪ M '' Icc (0 : ℝ) 1) ∪ R '' Icc (0 : ℝ) 1 := by
    rw [euclideanC1Glue_interval_image (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (2 : ℝ) ≤ 3) hv2, hAimage, hRsimage]
  have hMsi : InjOn Ms (Icc (1 : ℝ) 2) := by
    intro s hs t ht heq
    have he := hMi (show s - 1 ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hs.1, hs.2])
      (show t - 1 ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [ht.1, ht.2]) heq
    linarith
  have hRsi : InjOn Rs (Icc (2 : ℝ) 3) := by
    intro s hs t ht heq
    have he := hRi (show s - 2 ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hs.1, hs.2])
      (show t - 2 ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [ht.1, ht.2]) heq
    linarith
  have hAi : InjOn A (Icc (0 : ℝ) 2) := by
    apply euclideanC1Glue_interval_injOn (by norm_num) (by norm_num) hLi hMsi hv1
    rwa [hMsimage]
  have hBi : InjOn B (Icc (0 : ℝ) 3) := by
    apply euclideanC1Glue_interval_injOn (by norm_num) (by norm_num) hAi hRsi hv2
    rw [hAimage, hRsimage]
    rintro z ⟨hAor, hRz⟩
    rcases hAor with hLz | hMz
    · exact (Set.disjoint_left.mp hLR hLz hRz).elim
    · have hz : z = M 1 := hMRmeet ⟨hMz, hRz⟩
      have hA2 : A 2 = M 1 := by
        change euclideanC1Glue 1 L Ms 2 = M 1
        rw [euclideanC1Glue_eq_right hv1 (by norm_num : (1 : ℝ) ≤ 2)]
        norm_num [Ms]
      exact hz.trans hA2.symm
  have hBreg : ∀ t ∈ Icc (0 : ℝ) 3, deriv B t ≠ 0 := by
    intro t ht
    rw [euclideanC1Glue_deriv (hA.differentiable (by norm_num))
      (hRs.differentiable (by norm_num)) hv2 hd2]
    split_ifs with ht2
    · rw [euclideanC1Glue_deriv (hL.differentiable (by norm_num))
        (hMs.differentiable (by norm_num)) hv1 hd1]
      split_ifs with ht1
      · exact hLreg t ⟨ht.1, ht1⟩
      · rw [hMsD]
        exact hMreg _ (by constructor <;> linarith [ht.1, ht.2])
    · rw [hRsD]
      exact hRreg _ (by constructor <;> linarith [ht.1, ht.2])
  have hBL : B =ᶠ[𝓝 (0 : ℝ)] L := by
    filter_upwards [gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    change euclideanC1Glue 2 A Rs t = L t
    rw [euclideanC1Glue_eq_left 2 A Rs (show t ≤ 2 by linarith)]
    exact euclideanC1Glue_eq_left 1 L Ms ht.le
  have hBR : B =ᶠ[𝓝 (3 : ℝ)] Rs := by
    filter_upwards [lt_mem_nhds (show (2 : ℝ) < 3 by norm_num)] with t ht
    exact euclideanC1Glue_eq_right hv2 ht.le
  let η : ℝ → ℂ := fun t => B (3 * t)
  have hη : ContDiff ℝ 1 η := by dsimp [η]; fun_prop
  have hηL : η =ᶠ[𝓝 (0 : ℝ)] (fun t => L (3 * t)) := by
    have hmap : Tendsto (fun t : ℝ => 3 * t) (𝓝 0) (𝓝 0) := by
      have hcont : Continuous (fun t : ℝ => 3 * t) := by fun_prop
      simpa only [mul_zero] using hcont.tendsto 0
    exact hBL.comp_tendsto hmap
  have hηR : η =ᶠ[𝓝 (1 : ℝ)] (fun t => R (3 * t - 2)) := by
    have hmap : Tendsto (fun t : ℝ => 3 * t) (𝓝 1) (𝓝 3) := by
      have hcont : Continuous (fun t : ℝ => 3 * t) := by fun_prop
      simpa only [mul_one] using hcont.tendsto 1
    exact hBR.comp_tendsto hmap
  refine ⟨η, hη, ?_, ?_, ?_, ?_, ?_, hηL, hηR⟩
  · intro s hs t ht heq
    have he := hBi (show 3 * s ∈ Icc (0 : ℝ) 3 by constructor <;> linarith [hs.1, hs.2])
      (show 3 * t ∈ Icc (0 : ℝ) 3 by constructor <;> linarith [ht.1, ht.2]) heq
    linarith
  · intro t ht
    have hdη : deriv η t = (3 : ℝ) • deriv B (3 * t) := by
      simpa only [Function.comp_def, id_eq, mul_one, η] using
        ((((hB.differentiable (by norm_num)) (3 * t)).hasDerivAt).scomp t
          ((hasDerivAt_id t).const_mul 3)).deriv
    rw [hdη]
    exact smul_ne_zero (by norm_num) (hBreg _ (by constructor <;> linarith [ht.1, ht.2]))
  · simpa using hηL.self_of_nhds
  · have hvη := hηR.self_of_nhds
    norm_num at hvη
    exact hvη
  · rw [← hBimage]
    apply Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨3 * t, by constructor <;> linarith [ht.1, ht.2], rfl⟩
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨t / 3, by constructor <;> linarith [ht.1, ht.2], by dsimp [η]; congr 1; ring⟩

end RepulsiveCoulomb
