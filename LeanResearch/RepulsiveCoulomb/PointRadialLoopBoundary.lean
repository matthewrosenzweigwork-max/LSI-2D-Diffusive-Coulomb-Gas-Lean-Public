import LeanResearch.RepulsiveCoulomb.PointRadialSectorTopology
import Mathlib.Topology.Order.ProjIcc

/-! The entire local boundary near a based simple loop corner is derived
from the actual radial collars. Compactness excludes the rest of the loop.
This supplies the two-ray equality needed by actual Jordan side selection;
it is not an additional drawing hypothesis. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- Exact two-ray local boundary for an actual simple loop with literal
radial collars in one partial-homeomorphism chart. -/
theorem exists_simple_loop_exact_radial_boundary
    (γ : Icc (0 : ℝ) 1 → ℂ) (hγ : Continuous γ)
    (hinj : InjOn γ {t : Icc (0 : ℝ) 1 | t.1 < 1})
    (e : OpenPartialHomeomorph ℂ ℂ) {p : ℂ} (hp : p ∈ e.source) (hep : e p = 0)
    (hγ0 : γ 0 = p) {l r cL cR R θ : ℝ}
    (hl : 0 < l) (hlr : l < r) (hr : r < 1) (hcL : 0 < cL) (hcR : 0 < cR)
    (hR : 0 < R) (hball : ball (0 : ℂ) R ⊆ e.target)
    (hLrad : cL * l < R) (hRrad : cR * (1 - r) < R)
    (hleft : ∀ t : Icc (0 : ℝ) 1, t.1 ≤ l →
      γ t = e.symm (pointRadialSectorPoint (cL * t.1) 0))
    (hright : ∀ t : Icc (0 : ℝ) 1, r ≤ t.1 →
      γ t = e.symm (pointRadialSectorPoint (cR * (1 - t.1)) θ)) :
    ∃ δ : ℝ, 0 < δ ∧ ball (0 : ℂ) δ ⊆ e.target ∧
      ∀ z ∈ ball (0 : ℂ) δ,
        e.symm z ∈ range γ ↔ z ∈ pointDiskRay δ 0 ∪ pointDiskRay δ θ := by
  let Γ := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ
  have hΓ : Continuous Γ := continuous_IccExtend_iff.mpr hγ
  let K := Γ '' Icc l r
  have hK : IsCompact K := isCompact_Icc.image hΓ
  have hpK : p ∉ K := by
    rintro ⟨u, hu, heq⟩
    have hu0 : 0 < u := hl.trans_le hu.1
    have hu1 : u < 1 := hu.2.trans_lt hr
    have hucc : u ∈ Icc (0 : ℝ) 1 := ⟨hu0.le, hu1.le⟩
    have hΓu : Γ u = γ ⟨u, hucc⟩ := IccExtend_of_mem _ _ hucc
    have he : (⟨u, hucc⟩ : Icc (0 : ℝ) 1) = 0 :=
      hinj hu1 (by norm_num) (hΓu.symm.trans (heq.trans hγ0.symm))
    exact hu0.ne' (congrArg Subtype.val he)
  obtain ⟨ε, hε, hεK⟩ := Metric.mem_nhds_iff.mp (hK.isClosed.isOpen_compl.mem_nhds hpK)
  have h0target : (0 : ℂ) ∈ e.target := hep ▸ e.mapsTo hp
  have hsymm0 : e.symm (0 : ℂ) = p := by rw [← hep, e.left_inv hp]
  have hcont : ContinuousAt e.symm (0 : ℂ) := e.symm.continuousAt h0target
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ e.target ∧ e.symm z ∈ ball p ε := by
    have hpre : ∀ᶠ z in 𝓝 (0 : ℂ), e.symm z ∈ ball p ε := by
      apply hcont.tendsto.eventually
      rw [hsymm0]
      exact ball_mem_nhds p hε
    filter_upwards [e.open_target.mem_nhds h0target, hpre] with z hz ht
    exact ⟨hz, ht⟩
  obtain ⟨d, hd, hdnear⟩ := Metric.mem_nhds_iff.mp hnear
  let δ := min d (min R (min (cL * l) (cR * (1 - r))))
  have hδ : 0 < δ := lt_min hd (lt_min hR (lt_min (mul_pos hcL hl) (mul_pos hcR (sub_pos.mpr hr))))
  have hδd : δ ≤ d := min_le_left _ _
  have hδR : δ ≤ R := (min_le_right _ _).trans (min_le_left _ _)
  have hδL : δ ≤ cL * l :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδR' : δ ≤ cR * (1 - r) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδtarget : ball (0 : ℂ) δ ⊆ e.target := fun z hz => hball (lt_of_lt_of_le hz hδR)
  refine ⟨δ, hδ, hδtarget, ?_⟩
  intro z hz
  have hzt : z ∈ e.target := hδtarget hz
  have havoid : e.symm z ∉ K := hεK ((hdnear (lt_of_lt_of_le hz hδd)).2)
  constructor
  · rintro ⟨t, ht⟩
    by_cases htL : t.1 ≤ l
    · have hnonneg : 0 ≤ cL * t.1 := mul_nonneg hcL.le t.2.1
      have hradR : pointRadialSectorPoint (cL * t.1) 0 ∈ ball (0 : ℂ) R := by
        rw [mem_ball, dist_zero_right, pointRadialSectorPoint_norm hnonneg]
        exact (mul_le_mul_of_nonneg_left htL hcL.le).trans_lt hLrad
      have heq : pointRadialSectorPoint (cL * t.1) 0 = z :=
        e.symm.injOn (hball hradR) hzt ((hleft t htL).symm.trans ht)
      have hsmall : cL * t.1 < δ := by
        have hn := congrArg norm heq
        rw [pointRadialSectorPoint_norm hnonneg] at hn
        rw [hn]
        simpa only [mem_ball, dist_zero_right] using hz
      exact Or.inl ⟨cL * t.1, ⟨hnonneg, hsmall⟩, heq⟩
    by_cases htR : r ≤ t.1
    · have hnonneg : 0 ≤ cR * (1 - t.1) := mul_nonneg hcR.le (sub_nonneg.mpr t.2.2)
      have hradR : pointRadialSectorPoint (cR * (1 - t.1)) θ ∈ ball (0 : ℂ) R := by
        rw [mem_ball, dist_zero_right, pointRadialSectorPoint_norm hnonneg]
        exact (mul_le_mul_of_nonneg_left (by linarith) hcR.le).trans_lt hRrad
      have heq : pointRadialSectorPoint (cR * (1 - t.1)) θ = z :=
        e.symm.injOn (hball hradR) hzt ((hright t htR).symm.trans ht)
      have hsmall : cR * (1 - t.1) < δ := by
        have hn := congrArg norm heq
        rw [pointRadialSectorPoint_norm hnonneg] at hn
        rw [hn]
        simpa only [mem_ball, dist_zero_right] using hz
      exact Or.inr ⟨cR * (1 - t.1), ⟨hnonneg, hsmall⟩, heq⟩
    exact False.elim (havoid ⟨t.1, ⟨(lt_of_not_ge htL).le, (lt_of_not_ge htR).le⟩,
      (IccExtend_val _ γ t).trans ht⟩)
  · rintro (⟨ρ, hρ, hρz⟩ | ⟨ρ, hρ, hρz⟩)
    · have hρl : ρ / cL < l :=
        (div_lt_iff₀ hcL).mpr (by simpa only [mul_comm] using hρ.2.trans_le hδL)
      have hρ0 : 0 ≤ ρ / cL := div_nonneg hρ.1 hcL.le
      let t : Icc (0 : ℝ) 1 := ⟨ρ / cL, hρ0, hρl.le.trans (hlr.le.trans hr.le)⟩
      refine ⟨t, ?_⟩
      rw [hleft t hρl.le]
      have hmul : cL * t.1 = ρ := by dsimp [t]; field_simp [hcL.ne']
      rw [hmul]
      exact congrArg e.symm hρz
    · have hρr : ρ / cR < 1 - r :=
        (div_lt_iff₀ hcR).mpr (by simpa only [mul_comm] using hρ.2.trans_le hδR')
      have hρ0 : 0 ≤ ρ / cR := div_nonneg hρ.1 hcR.le
      have hrt : r < 1 - ρ / cR := by linarith
      let t : Icc (0 : ℝ) 1 := ⟨1 - ρ / cR, by linarith, by linarith⟩
      refine ⟨t, ?_⟩
      rw [hright t hrt.le]
      have hmul : cR * (1 - t.1) = ρ := by dsimp [t]; field_simp [hcR.ne'] <;> ring
      rw [hmul]
      exact congrArg e.symm hρz

end RepulsiveCoulomb
