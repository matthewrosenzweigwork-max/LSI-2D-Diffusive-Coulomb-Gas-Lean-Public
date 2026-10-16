import LeanResearch.RepulsiveCoulomb.PointLineFixedSideAllPoints
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Records-only, uncompiled. Full physical side widths are recovered from
actual oriented interval membership, including reflex intervals. No chord,
cosine, principal-angle truncation, or preassigned curvature mass is used. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

def lineClosedInitialSector (R θ : ℝ) : Set ℂ :=
  (pointDiskRay R 0 ∪ pointDiskRay R θ) ∪ pointOpenRadialSector R 0 θ

def lineClosedTerminalSector (R θ : ℝ) : Set ℂ :=
  (pointDiskRay R 0 ∪ pointDiskRay R θ) ∪ pointOpenRadialSector R θ (2 * Real.pi)

/-- A literal test ray detects the ENTIRE initial interval, not its shorter
angle or its cosine. -/
theorem lineClosedInitialSector_test_ray {R r θ φ : ℝ}
    (hr : 0 < r) (hrR : r < R) (hθ : 0 < θ) (hθ2 : θ < 2 * Real.pi)
    (hφ : 0 < φ) (hφ2 : φ < 2 * Real.pi) :
    pointRadialSectorPoint r φ ∈ lineClosedInitialSector R θ ↔ φ ≤ θ := by
  have hφI : φ ∈ Ico (0 : ℝ) (2 * Real.pi) := ⟨hφ.le, hφ2⟩
  have hθI : θ ∈ Ico (0 : ℝ) (2 * Real.pi) := ⟨hθ.le, hθ2⟩
  have h0I : (0 : ℝ) ∈ Ico 0 (2 * Real.pi) := ⟨le_rfl, by positivity⟩
  constructor
  · rintro ((⟨s, hs, he⟩ | ⟨s, hs, he⟩) | ⟨⟨s, ψ⟩, ⟨hs, hψ⟩, he⟩)
    · have heq := (pointRadialSectorPoint_angle_injective hr hs.1 hφI h0I he.symm).2
      linarith
    · exact (pointRadialSectorPoint_angle_injective hr hs.1 hφI hθI he.symm).2.le
    · have hψI : ψ ∈ Ico (0 : ℝ) (2 * Real.pi) := ⟨hψ.1.le, hψ.2.trans hθ2⟩
      have heq := (pointRadialSectorPoint_angle_injective hr hs.1.le hφI hψI he.symm).2
      exact heq.trans_le hψ.2.le
  · intro hle
    rcases hle.eq_or_lt with he | hlt
    · exact Or.inl (Or.inr ⟨r, ⟨hr.le, hrR⟩, by rw [he]⟩)
    · exact Or.inr ⟨(r, φ), ⟨⟨hr, hrR⟩, ⟨hφ, hlt⟩⟩, rfl⟩

/-- The complementary full interval retains its endpoint order as well. -/
theorem lineClosedTerminalSector_test_ray {R r θ φ : ℝ}
    (hr : 0 < r) (hrR : r < R) (hθ : 0 < θ) (hθ2 : θ < 2 * Real.pi)
    (hφ : 0 < φ) (hφ2 : φ < 2 * Real.pi) :
    pointRadialSectorPoint r φ ∈ lineClosedTerminalSector R θ ↔ θ ≤ φ := by
  have hφI : φ ∈ Ico (0 : ℝ) (2 * Real.pi) := ⟨hφ.le, hφ2⟩
  have hθI : θ ∈ Ico (0 : ℝ) (2 * Real.pi) := ⟨hθ.le, hθ2⟩
  have h0I : (0 : ℝ) ∈ Ico 0 (2 * Real.pi) := ⟨le_rfl, by positivity⟩
  constructor
  · rintro ((⟨s, hs, he⟩ | ⟨s, hs, he⟩) | ⟨⟨s, ψ⟩, ⟨hs, hψ⟩, he⟩)
    · have heq := (pointRadialSectorPoint_angle_injective hr hs.1 hφI h0I he.symm).2
      linarith
    · exact (pointRadialSectorPoint_angle_injective hr hs.1 hφI hθI he.symm).2.ge
    · have hψI : ψ ∈ Ico (0 : ℝ) (2 * Real.pi) := ⟨(hθ.trans hψ.1).le, hψ.2⟩
      have heq := (pointRadialSectorPoint_angle_injective hr hs.1.le hφI hψI he.symm).2
      exact hψ.1.le.trans_eq heq.symm
  · intro hle
    rcases hle.eq_or_lt with he | hlt
    · exact Or.inl (Or.inr ⟨r, ⟨hr.le, hrR⟩, by rw [he]⟩)
    · exact Or.inr ⟨(r, φ), ⟨⟨hr, hrR⟩, ⟨hlt, hφ2⟩⟩, rfl⟩

/-- Even agreement on an arbitrarily small punctured disk determines the full
ordered width. The test angle between the proposed endpoints detects any
strict discrepancy, including when either interval is reflex. -/
theorem lineClosedInitialSector_width_unique {r R S θ φ : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hrS : r ≤ S)
    (hθ : 0 < θ) (hθ2 : θ < 2 * Real.pi) (hφ : 0 < φ) (hφ2 : φ < 2 * Real.pi)
    (hset : ∀ z ∈ ball (0 : ℂ) r,
      z ∈ lineClosedInitialSector R θ ↔ z ∈ lineClosedInitialSector S φ) : θ = φ := by
  let b := (θ + φ) / 2
  have hb : 0 < b := by dsimp [b]; linarith
  have hb2 : b < 2 * Real.pi := by dsimp [b]; linarith
  have hhalf : 0 < r / 2 := by linarith
  have hz : pointRadialSectorPoint (r / 2) b ∈ ball (0 : ℂ) r := by
    rw [mem_ball, dist_zero_right, pointRadialSectorPoint_norm hhalf.le]
    linarith
  have htest := hset _ hz
  rw [lineClosedInitialSector_test_ray hhalf (by linarith) hθ hθ2 hb hb2,
    lineClosedInitialSector_test_ray hhalf (by linarith) hφ hφ2 hb hb2] at htest
  apply le_antisymm
  · by_contra h
    have hlt : φ < θ := lt_of_not_ge h
    have hbθ : b ≤ θ := by dsimp [b]; linarith
    have hbφ := htest.mp hbθ
    dsimp [b] at hbφ
    linarith
  · by_contra h
    have hlt : θ < φ := lt_of_not_ge h
    have hbφ : b ≤ φ := by dsimp [b]; linarith
    have hbθ := htest.mpr hbφ
    dsimp [b] at hbθ
    linarith

theorem lineClosedTerminalSector_width_unique {r R S θ φ : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hrS : r ≤ S)
    (hθ : 0 < θ) (hθ2 : θ < 2 * Real.pi) (hφ : 0 < φ) (hφ2 : φ < 2 * Real.pi)
    (hset : ∀ z ∈ ball (0 : ℂ) r,
      z ∈ lineClosedTerminalSector R θ ↔ z ∈ lineClosedTerminalSector S φ) : θ = φ := by
  let b := (θ + φ) / 2
  have hb : 0 < b := by dsimp [b]; linarith
  have hb2 : b < 2 * Real.pi := by dsimp [b]; linarith
  have hhalf : 0 < r / 2 := by linarith
  have hz : pointRadialSectorPoint (r / 2) b ∈ ball (0 : ℂ) r := by
    rw [mem_ball, dist_zero_right, pointRadialSectorPoint_norm hhalf.le]
    linarith
  have htest := hset _ hz
  rw [lineClosedTerminalSector_test_ray hhalf (by linarith) hθ hθ2 hb hb2,
    lineClosedTerminalSector_test_ray hhalf (by linarith) hφ hφ2 hb hb2] at htest
  apply le_antisymm
  · by_contra h
    have hlt : φ < θ := lt_of_not_ge h
    have hφb : φ ≤ b := by dsimp [b]; linarith
    have hθb := htest.mpr hφb
    dsimp [b] at hθb
    linarith
  · by_contra h
    have hlt : θ < φ := lt_of_not_ge h
    have hθb : θ ≤ b := by dsimp [b]; linarith
    have hφb := htest.mp hθb
    dsimp [b] at hφb
    linarith

/-- Actual side labels cannot be silently swapped in the same normalized
oriented chart: a small positive test angle distinguishes them. -/
theorem lineClosedInitialSector_ne_terminal_locally {r R S θ φ : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hrS : r ≤ S)
    (hθ : 0 < θ) (hθ2 : θ < 2 * Real.pi) (hφ : 0 < φ) (hφ2 : φ < 2 * Real.pi) :
    ¬ (∀ z ∈ ball (0 : ℂ) r,
      z ∈ lineClosedInitialSector R θ ↔ z ∈ lineClosedTerminalSector S φ) := by
  intro hset
  let b := min θ φ / 2
  have hb : 0 < b := by dsimp [b]; exact half_pos (lt_min hθ hφ)
  have hbθ : b < θ := by dsimp [b]; linarith [min_le_left θ φ, lt_min hθ hφ]
  have hbφ : b < φ := by dsimp [b]; linarith [min_le_right θ φ, lt_min hθ hφ]
  have hhalf : 0 < r / 2 := by linarith
  have hz : pointRadialSectorPoint (r / 2) b ∈ ball (0 : ℂ) r := by
    rw [mem_ball, dist_zero_right, pointRadialSectorPoint_norm hhalf.le]
    linarith
  have htest := hset _ hz
  rw [lineClosedInitialSector_test_ray hhalf (by linarith) hθ hθ2 hb (hbθ.trans hθ2),
    lineClosedTerminalSector_test_ray hhalf (by linarith) hφ hφ2 hb (hbθ.trans hθ2)] at htest
  exact (not_le_of_gt hbφ) (htest.mp hbθ.le)

/-- The exponent is the original/coalesced a, so the physical scale is
1+a/2. Equality of actual full intervals fixes both the physical width and
its signed boundary turn; no curvature mass equality is assumed. -/
theorem lineCap_full_physical_interval_and_turn_unique {r R S θ φ a : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hrS : r ≤ S)
    (hθ : 0 < θ) (hθ2 : θ < 2 * Real.pi) (hφ : 0 < φ) (hφ2 : φ < 2 * Real.pi)
    (hset : ∀ z ∈ ball (0 : ℂ) r,
      z ∈ lineClosedInitialSector R θ ↔ z ∈ lineClosedInitialSector S φ) :
    (1 + a / 2) * θ = (1 + a / 2) * φ ∧
      Real.pi - (1 + a / 2) * θ = Real.pi - (1 + a / 2) * φ := by
  rw [lineClosedInitialSector_width_unique hr hrR hrS hθ hθ2 hφ hφ2 hset]
  exact ⟨rfl, rfl⟩

end RepulsiveCoulomb
