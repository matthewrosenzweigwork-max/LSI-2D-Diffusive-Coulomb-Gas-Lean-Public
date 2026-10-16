module

public import LeanResearch.RepulsiveCoulomb.FiniteLinkCellOwnership
public import LeanResearch.RepulsiveCoulomb.PointIncidentSeamOrigin
public import LeanResearch.RepulsiveCoulomb.OrderedEuclideanWedgeCover

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Normalize the actual directed common-chart arcs
at a derived safe seam ray. Periodicity transports the actual closed/open
separation to real intervals, yielding the constructed whole-cell ownership. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def normalizedIncidentLower (origin lo : ℝ) : ℝ :=
  toIcoMod (by positivity : 0 < 2 * Real.pi) 0 (lo - origin)

/-- The same actual ray after rotating the origin and reducing a full period.
No shorter representative or change of occupied width occurs. -/
theorem normalizedIncidentLower_polar (r origin lo t : ℝ) :
    conePhase origin * sectorPolar r (normalizedIncidentLower origin lo + t) =
      sectorPolar r (lo + t) := by
  let hT : 0 < 2 * Real.pi := by positivity
  have hrebase : sectorPolar r (normalizedIncidentLower origin lo + t) =
      sectorPolar r (lo - origin + t) := by
    unfold normalizedIncidentLower toIcoMod
    convert (sectorPolar_periodic r).sub_zsmul_eq (toIcoDiv hT 0 (lo - origin)) using 1 <;>
      congr 1 <;> ring
  rw [hrebase, conePhase_mul_sectorPolar]
  congr 1
  ring

theorem normalizedIncidentLower_no_wrap {ι : Type*} (lo width : ι → ℝ)
    (origin r : ℝ)
    (havoid : ∀ i θ, θ ∈ Ioo (lo i) (lo i + width i) →
      sectorPolar r origin ≠ sectorPolar r θ) :
    ∀ i, normalizedIncidentLower origin (lo i) + width i ≤ 2 * Real.pi := by
  intro i
  let b := normalizedIncidentLower origin (lo i)
  have hb : b ∈ Ico (0 : ℝ) (2 * Real.pi) := toIcoMod_mem_Ico' _ _
  apply flatLink_no_wrap_of_origin_avoided hb
  intro θ hθ he
  have hθ' : lo i + (θ - b) ∈ Ioo (lo i) (lo i + width i) := by
    constructor <;> linarith [hθ.1, hθ.2]
  apply havoid i (lo i + (θ - b)) hθ'
  have he' := congrArg (fun z : ℂ ↦ conePhase origin * z) he
  have hleft : conePhase origin * sectorPolar r 0 = sectorPolar r origin := by
    rw [conePhase_mul_sectorPolar, add_zero]
  have hangle : normalizedIncidentLower origin (lo i) + (θ - b) = θ := by
    dsimp [b]
    ring
  have hright : conePhase origin * sectorPolar r θ = sectorPolar r (lo i + (θ - b)) := by
    simpa only [hangle] using normalizedIncidentLower_polar r origin (lo i) (θ - b)
  rw [hleft, hright] at he'
  exact he'

theorem normalizedIncidentLower_separated {ι : Type*} (lo width : ι → ℝ)
    (origin r : ℝ)
    (hsep : ∀ i j, i ≠ j → ∀ θ ∈ Icc (lo i) (lo i + width i),
      ∀ φ ∈ Ioo (lo j) (lo j + width j), sectorPolar r θ ≠ sectorPolar r φ) :
    ∀ i j, i ≠ j →
      Disjoint (Icc (normalizedIncidentLower origin (lo i))
        (normalizedIncidentLower origin (lo i) + width i))
      (Ioo (normalizedIncidentLower origin (lo j))
        (normalizedIncidentLower origin (lo j) + width j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro θ hθi hθj
  let bi := normalizedIncidentLower origin (lo i)
  let bj := normalizedIncidentLower origin (lo j)
  apply hsep i j hij (lo i + (θ - bi))
    ⟨by dsimp [bi]; linarith [hθi.1], by dsimp [bi]; linarith [hθi.2]⟩
    (lo j + (θ - bj))
    ⟨by dsimp [bj]; linarith [hθj.1], by dsimp [bj]; linarith [hθj.2]⟩
  calc
    sectorPolar r (lo i + (θ - bi)) = conePhase origin * sectorPolar r θ := by
      have hangle : normalizedIncidentLower origin (lo i) + (θ - bi) = θ := by
        dsimp [bi]
        ring
      simpa only [hangle] using (normalizedIncidentLower_polar r origin (lo i) (θ - bi)).symm
    _ = sectorPolar r (lo j + (θ - bj)) := by
      have hangle : normalizedIncidentLower origin (lo j) + (θ - bj) = θ := by
        dsimp [bj]
        ring
      simpa only [hangle] using normalizedIncidentLower_polar r origin (lo j) (θ - bj)

/-- Rebased coordinates retain the very same actual source point and Boolean
orientation used to construct the physical branch, including passing pieces. -/
theorem PointIncidentSectorSourcePatch.normalized_polarAt
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {S : PointActualAllocatedSector a y} {p : ℂ}
    (P : PointIncidentSectorSourcePatch S p) (C : PointFlatLinkConeDisk a y p)
    {ρ : ℝ} {hρP : ρ ≤ P.radius} {lo : ℝ} {forward : Bool}
    (hpolar : P.PolarAt C hρP lo forward) (origin r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) ρ) (t : unitInterval) :
    C.chart (P.map (flatLinkSectorDiskPoint P.angle_pos.le P.angle_le_pi r
      ⟨hr.1, hr.2.trans hρP⟩ t)) =
      conePhase origin * sectorPolar r (normalizedIncidentLower origin lo +
        flatLinkOrientedAngle forward (P.angle / (coalescedPointExponent a y p / 2 + 1)) t) :=
  (hpolar r hr t).trans (normalizedIncidentLower_polar r origin lo _).symm

/-- From actual sector patches and their proved common-chart formulas, build
an explicit sorted partition and inject each entire occupied sector into one
cell. The direction Boolean remains the original geometric direction. -/
theorem exists_pointIncident_whole_cell_partition
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {ι : Type*} [Fintype ι] (S : ι → PointActualAllocatedSector a y) (p : ℂ)
    (P : ∀ i, PointIncidentSectorSourcePatch (S i) p)
    (C : PointFlatLinkConeDisk a y p)
    (hdis : ∀ i j, i ≠ j → Disjoint (range (S i).map) (S j).openImage)
    {ρ : ℝ} (hρ : 0 < ρ) (hρP : ∀ i, ρ ≤ (P i).radius) (hρC : ρ ≤ C.radius)
    (lo : ι → ℝ) (forward : ι → Bool)
    (hpolar : ∀ i, (P i).PolarAt C (hρP i) (lo i) (forward i)) (i₀ : ι) :
    ∃ N : ℕ, 0 < N ∧ ∃ u : Fin (N + 1) → ℝ,
      StrictMono u ∧ u 0 = 0 ∧ u (Fin.last N) = 2 * Real.pi ∧
      ∃ owner : ι ↪ Fin N, ∀ i,
        u (owner i).castSucc = normalizedIncidentLower (lo i₀) (lo i) ∧
        u (owner i).succ = normalizedIncidentLower (lo i₀) (lo i) +
          (P i).angle / (coalescedPointExponent a y p / 2 + 1) := by
  let k := coalescedPointExponent a y p / 2 + 1
  let b : ι → ℝ := fun i ↦ normalizedIncidentLower (lo i₀) (lo i)
  let w : ι → ℝ := fun i ↦ (P i).angle / k
  have hk : 0 < k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  have hw (i : ι) : 0 < w i := div_pos (P i).angle_pos hk
  have hb (i : ι) : b i ∈ Ico (0 : ℝ) (2 * Real.pi) := toIcoMod_mem_Ico' _ _
  have havoid := pointIncidentSeamOrigin_avoids_all_open_arcs ha y S p P C hdis
    hρ hρP hρC lo forward hpolar i₀
  have hnowrap := normalizedIncidentLower_no_wrap lo w (lo i₀) (ρ / 2) havoid
  have hsep := normalizedIncidentLower_separated lo w (lo i₀) (ρ / 2) (by
    intro i j hij θ hθ φ hφ
    exact (P i).closed_arc_disjoint_open_arc (P j) ha C (hdis i j hij)
      hρ (hρP i) (hρP j) hρC (lo i) (lo j) (forward i) (forward j)
      (hpolar i) (hpolar j) hθ hφ)
  exact exists_finiteLink_owned_partition (by positivity) b (fun i ↦ b i + w i)
    (fun i ↦ ⟨(hb i).1, (hb i).2.le⟩)
    (fun i ↦ ⟨le_trans (hb i).1 (le_add_of_nonneg_right (hw i).le), hnowrap i⟩)
    (fun i ↦ lt_add_of_pos_right _ (hw i)) hsep

end RepulsiveCoulomb
