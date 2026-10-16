module

public import LeanResearch.RepulsiveCoulomb.PointIncidentArcSeparation

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Choose an actual seam endpoint as cyclic origin.
Actual cross-piece separation excludes it from other occupied interiors;
short-interval polar injectivity excludes it from its own occupied interior.
Thus no passing halfdisk is split by the artificial cyclic cut. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem sectorPolar_injOn_short_interval {r width : ℝ} (hr : 0 < r)
    (hw : width ≤ Real.pi) (lo : ℝ) :
    InjOn (sectorPolar r) (Icc lo (lo + width)) := by
  intro θ hθ φ hφ he
  have hrot := congrArg (fun z : ℂ ↦ conePhase (-lo) * z) he
  rw [conePhase_mul_sectorPolar, conePhase_mul_sectorPolar] at hrot
  have hθrange : -lo + θ ∈ Ioc (-Real.pi) Real.pi :=
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hφrange : -lo + φ ∈ Ioc (-Real.pi) Real.pi :=
    ⟨by linarith [hφ.1, Real.pi_pos], by linarith [hφ.2]⟩
  have harg := congrArg Complex.arg hrot
  rw [sectorPolar_arg hr hθrange, sectorPolar_arg hr hφrange] at harg
  linarith

/-- Any chosen actual lower seam endpoint is outside every occupied open
angular arc, including its own. The assertion uses literal polar rays and
therefore survives all angle-period normalization and chart rotations. -/
theorem pointIncidentSeamOrigin_avoids_all_open_arcs
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {ι : Type*} (S : ι → PointActualAllocatedSector a y) (p : ℂ)
    (P : ∀ i, PointIncidentSectorSourcePatch (S i) p)
    (C : PointFlatLinkConeDisk a y p)
    (hdis : ∀ i j, i ≠ j → Disjoint (range (S i).map) (S j).openImage)
    {ρ : ℝ} (hρ : 0 < ρ) (hρP : ∀ i, ρ ≤ (P i).radius) (hρC : ρ ≤ C.radius)
    (lo : ι → ℝ) (forward : ι → Bool)
    (hpolar : ∀ i, (P i).PolarAt C (hρP i) (lo i) (forward i)) (i₀ : ι) :
    ∀ j φ, φ ∈ Ioo (lo j)
      (lo j + (P j).angle / (coalescedPointExponent a y p / 2 + 1)) →
      sectorPolar (ρ / 2) (lo i₀) ≠ sectorPolar (ρ / 2) φ := by
  classical
  let k := coalescedPointExponent a y p / 2 + 1
  have hk1 : 1 ≤ k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  have hk : 0 < k := lt_of_lt_of_le zero_lt_one hk1
  have hwidth (i : ι) : 0 < (P i).angle / k ∧ (P i).angle / k ≤ Real.pi := by
    refine ⟨div_pos (P i).angle_pos hk, (div_le_iff₀ hk).mpr ?_⟩
    nlinarith [(P i).angle_le_pi, Real.pi_pos]
  have hendpoint : lo i₀ ∈ Icc (lo i₀) (lo i₀ + (P i₀).angle / k) :=
    ⟨le_rfl, le_add_of_nonneg_right (hwidth i₀).1.le⟩
  intro j φ hφ
  by_cases he : i₀ = j
  · subst j
    intro hsame
    have hEq := sectorPolar_injOn_short_interval (half_pos hρ) (hwidth i₀).2 (lo i₀)
      hendpoint ⟨hφ.1.le, hφ.2.le⟩ hsame
    exact (ne_of_lt hφ.1) hEq
  · exact (P i₀).closed_arc_disjoint_open_arc (P j) ha C (hdis i₀ j he)
      hρ (hρP i₀) (hρP j) hρC (lo i₀) (lo j) (forward i₀) (forward j)
      (hpolar i₀) (hpolar j) hendpoint hφ

end RepulsiveCoulomb
