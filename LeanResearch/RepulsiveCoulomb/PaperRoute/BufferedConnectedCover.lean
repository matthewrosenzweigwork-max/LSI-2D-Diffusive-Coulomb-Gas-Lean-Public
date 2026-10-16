import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Connected.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Finite connected buffered covers of actual planar continua

The centers are produced from compactness, with strict separation and a closed-radius
net. Ordinary planar volume proves the cardinal bound. Connectedness of the actual
set proves connectedness of the radius-two open-ball intersection graph. The final
producer assumes only compactness, connectedness, nontriviality, and a literal ball
buffer in the prescribed set. It assumes no cover or oscillation certificate.
-/

noncomputable section
open Set Metric MeasureTheory Function
open scoped ENNReal NNReal

namespace RepulsiveCoulomb.PaperRoute
namespace BufferedCover

/-- Compactness produces a finite strictly separated closed-radius net. The
non-strict cover radius must not be interpreted as an open-ball cover. -/
theorem exists_separated_net {K : Set ℂ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℂ, (↑S : Set ℂ) ⊆ K ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ε < dist x y) ∧
      ∀ x ∈ K, ∃ y ∈ S, dist x y ≤ ε := by
  let e : ℝ≥0 := ⟨ε, hε.le⟩
  have he : e ≠ 0 := by intro h; have := congrArg (fun z : ℝ≥0 => (z : ℝ)) h; exact hε.ne' this
  obtain ⟨N, _, hN, hc⟩ := exists_finite_isCover_of_isCompact (div_ne_zero he (by norm_num) : e / 2 ≠ 0) hK
  have hp : packingNumber e K ≠ ⊤ := by
    have h := packingNumber_two_mul_le_externalCoveringNumber (e / 2) K
    have heq : 2 * (e / 2) = e := by ring
    rw [heq] at h
    exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hN) (h.trans hc.externalCoveringNumber_le_encard)
  let S := maximalSeparatedSet e K
  have hfin : S.Finite := Set.encard_ne_top_iff.mp (by rw [encard_maximalSeparatedSet hp]; exact hp)
  refine ⟨hfin.toFinset, ?_, ?_, ?_⟩
  · simpa [S] using (maximalSeparatedSet_subset (ε := e) (A := K))
  · intro x hx y hy hxy
    have hs := (isSeparated_maximalSeparatedSet (ε := e) (A := K))
      (hfin.mem_toFinset.mp hx) (hfin.mem_toFinset.mp hy) hxy
    change (e : ℝ≥0∞) < edist x y at hs
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at hs
    exact ENNReal.ofReal_lt_ofReal_iff (dist_pos.mpr hxy) |>.mp hs
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := isCover_maximalSeparatedSet hp hx
    refine ⟨y, hfin.mem_toFinset.mpr hy, ?_⟩
    change edist x y ≤ (e : ℝ≥0∞) at hxy
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at hxy
    exact ENNReal.ofReal_le_ofReal_iff hε.le |>.mp hxy

/-- Real planar ball area, with the radius sign explicitly justified. -/
theorem volume_real_ball (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (ball c r) = Real.pi * r ^ 2 := by
  simp [measureReal_def, Complex.volume_ball, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, mul_comm]

/-- Disjoint radius-half balls, ordinary area additivity and monotonicity give
the literal planar packing inequality. No doubling hypothesis is used. -/
theorem separated_card_area_le {S : Finset ℂ} {ε R : ℝ} {c : ℂ}
    (hε : 0 < ε) (hR : 0 ≤ R)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ε < dist x y)
    (hbound : ∀ x ∈ S, dist x c ≤ R) :
    (S.card : ℝ) * (Real.pi * (ε / 2) ^ 2) ≤ Real.pi * (R + ε / 2) ^ 2 := by
  have hd : Pairwise (Disjoint on (fun i : S => ball (i : ℂ) (ε / 2))) := by
    intro i j hij
    apply ball_disjoint_ball
    have := hsep i i.property j j.property (fun h => hij (Subtype.ext h))
    linarith
  have hu : (⋃ i : S, ball (i : ℂ) (ε / 2)) ⊆ ball c (R + ε / 2) := by
    simp only [iUnion_subset_iff]
    intro i x hx
    have hx' : dist x i < ε / 2 := hx
    have hb := hbound i i.property
    exact lt_of_le_of_lt (dist_triangle x i c) (by linarith)
  have hsum := measureReal_iUnion_fintype (μ := volume) hd
    (fun _ => measurableSet_ball) (fun i => by rw [Complex.volume_ball]; finiteness)
  have hmono := measureReal_mono (μ := volume) hu (by rw [Complex.volume_ball]; finiteness)
  rw [hsum] at hmono
  simp only [volume_real_ball _ (by linarith : 0 ≤ ε / 2), Finset.sum_const,
    Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] at hmono
  rw [volume_real_ball _ (by linarith)] at hmono
  exact hmono

/-- The exact radius used by the buffered continuum construction. -/
def radius (K : Set ℂ) (T : ℝ) : ℝ := diam K / (16 * T)

/-- The radius-two open-ball intersection graph, expressed by the equivalent
strict center distance criterion in the plane. -/
def graph (S : Finset ℂ) (ε : ℝ) : SimpleGraph S where
  Adj i j := i ≠ j ∧ dist (i : ℂ) (j : ℂ) < 4 * ε
  symm := ⟨fun i j h => ⟨h.1.symm, by simpa [dist_comm] using h.2⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- Connectedness is proved from the actual connected covered set, using
open balls of radius `2ε`; a closed-radius `ε` net is sufficient. -/
theorem graph_connected {K : Set ℂ} (hK : IsConnected K) {S : Finset ℂ} {ε : ℝ}
    (hε : 0 < ε) (hsub : (↑S : Set ℂ) ⊆ K)
    (hnet : ∀ x ∈ K, ∃ y ∈ S, dist x y ≤ ε) : (graph S ε).Connected := by
  classical
  have hS : S.Nonempty := by
    obtain ⟨x, hx⟩ := hK.nonempty
    obtain ⟨y, hy, _⟩ := hnet x hx
    exact ⟨y, hy⟩
  let : Nonempty S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  refine ⟨?_⟩
  intro a b
  let G := graph S ε
  by_contra hab
  let A : Set ℂ := ⋃ i : S, ⋃ (_ : G.Reachable a i), ball (i : ℂ) (2 * ε)
  let B : Set ℂ := ⋃ i : S, ⋃ (_ : ¬ G.Reachable a i), ball (i : ℂ) (2 * ε)
  have hAo : IsOpen A := isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball
  have hBo : IsOpen B := isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball
  have hcover : K ⊆ A ∪ B := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnet x hx
    have hball : x ∈ ball y (2 * ε) := by exact lt_of_le_of_lt hxy (by linarith)
    by_cases hr : G.Reachable a ⟨y, hy⟩
    · exact Or.inl (by simp only [A, mem_iUnion]; exact ⟨⟨y, hy⟩, hr, hball⟩)
    · exact Or.inr (by simp only [B, mem_iUnion]; exact ⟨⟨y, hy⟩, hr, hball⟩)
  have ha : (K ∩ A).Nonempty := by
    refine ⟨a, hsub a.property, ?_⟩
    simp only [A, mem_iUnion]
    exact ⟨a, SimpleGraph.Reachable.refl _, mem_ball_self (by linarith)⟩
  have hb : (K ∩ B).Nonempty := by
    refine ⟨b, hsub b.property, ?_⟩
    simp only [B, mem_iUnion]
    exact ⟨b, hab, mem_ball_self (by linarith)⟩
  obtain ⟨x, _, hxA, hxB⟩ := hK.isPreconnected A B hAo hBo hcover ha hb
  simp only [A, mem_iUnion] at hxA
  simp only [B, mem_iUnion] at hxB
  obtain ⟨i, hi, hxi⟩ := hxA
  obtain ⟨j, hj, hxj⟩ := hxB
  have hij : i ≠ j := by intro h; exact hj (h ▸ hi)
  have hadj : G.Adj i j := by
    refine ⟨hij, ?_⟩
    have hxi' : dist (i : ℂ) x < 2 * ε := by simpa [dist_comm] using hxi
    have hxj' : dist x (j : ℂ) < 2 * ε := hxj
    exact lt_of_le_of_lt (dist_triangle (i : ℂ) x j) (by linarith)
  exact hj (hi.trans hadj.reachable)

/-- Every pair of vertices has an actual simple path of length strictly less
than the number of centers, including the zero-edge path on the diagonal. -/
theorem exists_bounded_path {S : Finset ℂ} {ε : ℝ} (h : (graph S ε).Connected)
    (i j : S) : ∃ p : (graph S ε).Walk i j, p.IsPath ∧ p.length < S.card := by
  obtain ⟨p, hp⟩ := (h.preconnected i j).exists_isPath
  exact ⟨p, hp, by simpa using hp.length_lt⟩

private theorem complex_midpoint_eq (x y : ℂ) : midpoint ℝ x y = (x + y) / 2 := by
  rw [midpoint_eq_smul_add]
  simp
  ring

/-- This graph is literally the intersection graph of the open radius-two
balls, with the diagonal excluded as required for a simple graph. -/
theorem graph_adj_iff_inter_nonempty {S : Finset ℂ} {ε : ℝ} (i j : S) :
    (graph S ε).Adj i j ↔ i ≠ j ∧
      (ball (i : ℂ) (2 * ε) ∩ ball (j : ℂ) (2 * ε)).Nonempty := by
  constructor
  · rintro ⟨hne, hdist⟩
    refine ⟨hne, (↑i + ↑j) / 2, ?_, ?_⟩
    · change dist (((i : ℂ) + (j : ℂ)) / 2) (i : ℂ) < 2 * ε
      rw [← complex_midpoint_eq, dist_midpoint_left]
      norm_num
      linarith
    · change dist (((i : ℂ) + (j : ℂ)) / 2) (j : ℂ) < 2 * ε
      rw [← complex_midpoint_eq, dist_midpoint_right]
      norm_num
      linarith
  · rintro ⟨hne, x, hxi, hxj⟩
    refine ⟨hne, ?_⟩
    have hxi' : dist (i : ℂ) x < 2 * ε := by simpa [dist_comm] using hxi
    have hxj' : dist x (j : ℂ) < 2 * ε := hxj
    exact lt_of_le_of_lt (dist_triangle (i : ℂ) x j) (by linarith)

/-- The literal midpoint ball lies in both enlarged balls on every edge. -/
theorem midpoint_ball_subset {x y : ℂ} {ε : ℝ} (h : dist x y < 4 * ε) :
    ball ((x + y) / 2) (2 * ε) ⊆ ball x (4 * ε) ∩ ball y (4 * ε) := by
  have hmx : dist ((x + y) / 2) x = dist x y / 2 := by
    rw [← complex_midpoint_eq]
    simp [dist_midpoint_left, div_eq_mul_inv, mul_comm]
  have hmy : dist ((x + y) / 2) y = dist x y / 2 := by
    rw [← complex_midpoint_eq]
    simp [dist_midpoint_right, div_eq_mul_inv, mul_comm]
  intro z hz
  have hz' : dist z ((x + y) / 2) < 2 * ε := hz
  constructor
  · have := dist_triangle z ((x + y) / 2) x
    rw [hmx] at this
    exact show dist z x < 4 * ε by linarith
  · have := dist_triangle z ((x + y) / 2) y
    rw [hmy] at this
    exact show dist z y < 4 * ε by linarith

/-- Exact finite, strictly positive physical area of the midpoint overlap. -/
theorem midpoint_ball_volume (x y : ℂ) {ε : ℝ} (hε : 0 < ε) :
    volume (ball ((x + y) / 2) (2 * ε)) = ENNReal.ofReal (4 * Real.pi * ε ^ 2) ∧
    0 < volume (ball ((x + y) / 2) (2 * ε)) ∧
    volume (ball ((x + y) / 2) (2 * ε)) < ⊤ := by
  have harea : 0 < 4 * Real.pi * ε ^ 2 := by positivity
  have heq : volume (ball ((x + y) / 2) (2 * ε)) =
      ENNReal.ofReal (4 * Real.pi * ε ^ 2) := by
    rw [Complex.volume_ball]
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    norm_num
    ring
  rw [heq]
  exact ⟨rfl, ENNReal.ofReal_pos.mpr harea, ENNReal.ofReal_lt_top⟩

/-- A proved geometric output. Its final producer below takes only actual set
hypotheses, never a pre-existing instance of these conclusions. -/
structure Data (K U : Set ℂ) (T : ℝ) where
  centers : Finset ℂ
  nonempty : centers.Nonempty
  centers_subset : (↑centers : Set ℂ) ⊆ K
  diam_pos : 0 < diam K
  ediam_lt_top : ediam K < ⊤
  radius_pos : 0 < radius K T
  separated : ∀ x ∈ centers, ∀ y ∈ centers, x ≠ y → radius K T < dist x y
  covers : ∀ x ∈ K, ∃ y ∈ centers, dist x y ≤ radius K T
  card_le : (centers.card : ℝ) ≤ (32 * T + 1) ^ 2
  connected : (graph centers (radius K T)).Connected
  closedBall_subset : ∀ x ∈ centers, closedBall x (4 * radius K T) ⊆ U

/-- The open radius-two balls genuinely cover K, despite the non-strict
radius-one net convention used in the construction. -/
theorem Data.open_cover {K U : Set ℂ} {T : ℝ} (d : Data K U T) :
    K ⊆ ⋃ i : d.centers, ball (i : ℂ) (2 * radius K T) := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := d.covers x hx
  exact mem_iUnion.mpr ⟨⟨y, hy⟩, lt_of_le_of_lt hxy (by linarith [d.radius_pos])⟩

theorem Data.bounded_path {K U : Set ℂ} {T : ℝ} (d : Data K U T)
    (i j : d.centers) : ∃ p : (graph d.centers (radius K T)).Walk i j,
      p.IsPath ∧ p.length < d.centers.card := exists_bounded_path d.connected i j

theorem Data.edge_overlap {K U : Set ℂ} {T : ℝ} (d : Data K U T)
    {i j : d.centers} (h : (graph d.centers (radius K T)).Adj i j) :
    ball (((i : ℂ) + (j : ℂ)) / 2) (2 * radius K T) ⊆
      ball (i : ℂ) (4 * radius K T) ∩ ball (j : ℂ) (4 * radius K T) :=
  midpoint_ball_subset h.2

theorem Data.overlap_volume {K U : Set ℂ} {T : ℝ} (d : Data K U T)
    (i j : d.centers) :
    volume (ball (((i : ℂ) + (j : ℂ)) / 2) (2 * radius K T)) =
      ENNReal.ofReal (4 * Real.pi * radius K T ^ 2) ∧
    0 < volume (ball (((i : ℂ) + (j : ℂ)) / 2) (2 * radius K T)) ∧
    volume (ball (((i : ℂ) + (j : ℂ)) / 2) (2 * radius K T)) < ⊤ :=
  midpoint_ball_volume i j d.radius_pos

/-- Ordinary real overlap area, retaining the same physical ball. -/
theorem Data.overlap_real_volume {K U : Set ℂ} {T : ℝ} (d : Data K U T)
    (i j : d.centers) :
    volume.real (ball (((i : ℂ) + (j : ℂ)) / 2) (2 * radius K T)) =
      4 * Real.pi * radius K T ^ 2 := by
  rw [volume_real_ball _ (by linarith [d.radius_pos])]
  ring

/-- Main geometric producer: actual compact connected nontrivial K, T ≥ 1,
and an actual diameter buffer produce the quantitative finite connected cover.
No doubling, covering, overlap, or path conclusion is assumed. -/
theorem exists_data {K U : Set ℂ} {T : ℝ}
    (hcompact : IsCompact K) (hconnected : IsConnected K) (hnontrivial : K.Nontrivial)
    (hT : 1 ≤ T)
    (hbuffer : ∀ x ∈ K, ball x (diam K / (2 * T)) ⊆ U) : Nonempty (Data K U T) := by
  have hTpos : 0 < T := by linarith
  have hR : 0 < diam K := Metric.diam_pos hnontrivial hcompact.isBounded
  have he : 0 < radius K T := div_pos hR (by positivity)
  obtain ⟨S, hsub, hsep, hnet⟩ := exists_separated_net hcompact he
  obtain ⟨c, hc⟩ := hconnected.nonempty
  have hSne : S.Nonempty := by obtain ⟨x, hx, _⟩ := hnet c hc; exact ⟨x, hx⟩
  have harea := separated_card_area_le he hR.le hsep
    (fun x hx => dist_le_diam_of_mem hcompact.isBounded (hsub hx) hc)
  have hscale : diam K = 16 * T * radius K T := by
    dsimp [radius]
    field_simp
  have houter : diam K + radius K T / 2 = (32 * T + 1) * (radius K T / 2) := by
    rw [hscale]
    ring
  rw [houter] at harea
  have harea' : (S.card : ℝ) * (Real.pi * (radius K T / 2) ^ 2) ≤
      (32 * T + 1) ^ 2 * (Real.pi * (radius K T / 2) ^ 2) := by nlinarith [harea]
  have hcard : (S.card : ℝ) ≤ (32 * T + 1) ^ 2 :=
    (mul_le_mul_iff_left₀ (by positivity : 0 < Real.pi * (radius K T / 2) ^ 2)).mp harea'
  have hrad : 4 * radius K T < diam K / (2 * T) := by
    change 4 * (diam K / (16 * T)) < diam K / (2 * T)
    calc
      4 * (diam K / (16 * T)) = diam K / (4 * T) := by ring
      _ < diam K / (2 * T) := div_lt_div_of_pos_left hR (by positivity) (by linarith)
  refine ⟨⟨S, hSne, hsub, hR, hcompact.isBounded.ediam_ne_top.lt_top, he,
    hsep, hnet, hcard, graph_connected hconnected he hsub hnet, ?_⟩⟩
  intro x hx z hz
  exact hbuffer x (hsub hx) (lt_of_le_of_lt hz hrad)

end BufferedCover
end RepulsiveCoulomb.PaperRoute
