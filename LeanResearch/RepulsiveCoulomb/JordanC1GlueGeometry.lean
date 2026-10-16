import LeanResearch.RepulsiveCoulomb.JordanC1Joining

/-! Exact image and actual injectivity for C¹ gluing on arbitrary adjacent
closed intervals. These geometric pasting lemmas use literal images and
endpoint intersections, and do not assume a global embedding certificate.
Records-only candidate. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem euclideanC1Glue_deriv_right {c : ℝ} {f g : ℝ → ℂ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hval : f c = g c) (hjet : deriv f c = deriv g c)
    {t : ℝ} (ht : c ≤ t) : deriv (euclideanC1Glue c f g) t = deriv g t := by
  rw [euclideanC1Glue_deriv hf hg hval hjet]
  by_cases htc : t ≤ c
  · have he : t = c := le_antisymm htc ht
    simp only [he, hjet, ite_self]
  · rw [if_neg htc]

theorem euclideanC1Glue_interval_image {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    {f g : ℝ → ℂ} (hval : f c = g c) :
    euclideanC1Glue c f g '' Icc a b = f '' Icc a c ∪ g '' Icc c b := by
  apply Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    by_cases htc : t ≤ c
    · left
      rw [euclideanC1Glue_eq_left c f g htc]
      exact ⟨t, ⟨ht.1, htc⟩, rfl⟩
    · right
      rw [euclideanC1Glue_eq_right hval (not_le.mp htc).le]
      exact ⟨t, ⟨(not_le.mp htc).le, ht.2⟩, rfl⟩
  · rintro z (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨t, ⟨ht.1, ht.2.trans hcb⟩, euclideanC1Glue_eq_left c f g ht.2⟩
    · exact ⟨t, ⟨hac.trans ht.1, ht.2⟩, euclideanC1Glue_eq_right hval ht.1⟩

/-- One actual attachment point is sufficient for global injectivity of the
pasted arc on the entire adjacent-interval domain. -/
theorem euclideanC1Glue_interval_injOn {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    {f g : ℝ → ℂ} (hf : InjOn f (Icc a c)) (hg : InjOn g (Icc c b))
    (hval : f c = g c)
    (hmeet : f '' Icc a c ∩ g '' Icc c b ⊆ {f c}) :
    InjOn (euclideanC1Glue c f g) (Icc a b) := by
  intro s hs t ht heq
  by_cases hsc : s ≤ c <;> by_cases htc : t ≤ c
  · rw [euclideanC1Glue_eq_left c f g hsc, euclideanC1Glue_eq_left c f g htc] at heq
    exact hf ⟨hs.1, hsc⟩ ⟨ht.1, htc⟩ heq
  · rw [euclideanC1Glue_eq_left c f g hsc,
      euclideanC1Glue_eq_right hval (not_le.mp htc).le] at heq
    have hm : f s = f c := hmeet
      ⟨⟨s, ⟨hs.1, hsc⟩, rfl⟩, ⟨t, ⟨(not_le.mp htc).le, ht.2⟩, heq.symm⟩⟩
    have hse : s = c := hf ⟨hs.1, hsc⟩ ⟨hac, le_rfl⟩ hm
    have hte : t = c := hg ⟨(not_le.mp htc).le, ht.2⟩ ⟨le_rfl, hcb⟩
      (heq.symm.trans (hm.trans hval))
    exact hse.trans hte.symm
  · rw [euclideanC1Glue_eq_right hval (not_le.mp hsc).le,
      euclideanC1Glue_eq_left c f g htc] at heq
    have hm : f t = f c := hmeet
      ⟨⟨t, ⟨ht.1, htc⟩, rfl⟩, ⟨s, ⟨(not_le.mp hsc).le, hs.2⟩, heq⟩⟩
    have hte : t = c := hf ⟨ht.1, htc⟩ ⟨hac, le_rfl⟩ hm
    have hse : s = c := hg ⟨(not_le.mp hsc).le, hs.2⟩ ⟨le_rfl, hcb⟩
      (heq.trans (hm.trans hval))
    exact hse.trans hte.symm
  · rw [euclideanC1Glue_eq_right hval (not_le.mp hsc).le,
      euclideanC1Glue_eq_right hval (not_le.mp htc).le] at heq
    exact hg ⟨(not_le.mp hsc).le, hs.2⟩ ⟨(not_le.mp htc).le, ht.2⟩ heq

end RepulsiveCoulomb
