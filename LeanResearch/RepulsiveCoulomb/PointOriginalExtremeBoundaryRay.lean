module

public import LeanResearch.RepulsiveCoulomb.PointCleanBoundaryEndRay
public import LeanResearch.RepulsiveCoulomb.PointGeometricCutState
public import Mathlib.Data.Finset.Max
public import Mathlib.Topology.Algebra.Group.ContinuousDiv

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Original-state finite extremum construction.
No complete boundary ray, unit-speed clock, or zero ambient exponent is an
input. The actual topological end and the all-pairs metric parametrization
are both constructed before the no-clean hypothesis is used. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- A constructed extreme marked boundary corner and its complete clean
outward metric end, with literal old-clock orientation and range. -/
structure PointExtremeBoundaryRay {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (P : Set ℂ) (ν α : ℂ →₀ ℝ) (β : ℝ → ℂ) (clock : ℂ → ℝ) where
  point : ℂ
  marked : point ∈ pointSignedMarked ν α
  point_frontier : point ∈ frontier P
  maximal : ∀ x, x ∈ pointSignedMarked ν α → x ∈ frontier P → clock x ≤ clock point
  ray : NNReal → ℂ
  metric : ∀ s t, (pointSmoothConformalEDist a y (ray s) (ray t)).toReal = dist s t
  start : ray 0 = point
  frontier : ∀ t, ray t ∈ _root_.frontier P
  range_eq : range ray = β '' Ici (clock point)
  closedEmbedding : IsClosedEmbedding ray
  proper : IsProperMap ray
  outward : ∀ t : NNReal, 0 < t → clock point < clock (ray t)
  clean_coeff : ∀ t : NNReal, 0 < t → ν (ray t) = 0 ∧ α (ray t) = 0
  clean : Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {point}) (range ray)
  allocation_zero : α point = 0
  turn_positive : 0 < ν point
  chart : PointRetainedConeNeighborhood a y P point
  admissible : chart.Admissible
  chart_coeff : ν point = Real.pi - chart.flatPhysicalWidth
  width_positive : 0 < chart.flatPhysicalWidth
  width_lt_pi : chart.flatPhysicalWidth < Real.pi

/-- Any genuine oriented boundary clock can be used. Reversing that clock
constructs the opposite extreme, without changing the original state. -/
theorem PointGeometricCutState.exists_extreme_boundary_ray_for_clock
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} (K : PointGeometricCutState a y P ν α)
    (hmarked : ∃ x, x ∈ pointSignedMarked ν α ∧ x ∈ frontier P)
    (hno : ¬ Nonempty K.CleanRay)
    (β : ℝ → ℂ) (hβ : IsClosedEmbedding β) (hfront : range β = frontier P)
    (clock : ℂ → ℝ) (hclock : ∀ t : ℝ, clock (β t) = t) :
    Nonempty (PointExtremeBoundaryRay a y P ν α β clock) := by
  classical
  let S := (pointSignedMarked ν α).filter (fun x ↦ x ∈ frontier P)
  have hS : S.Nonempty := by
    obtain ⟨x, hm, hf⟩ := hmarked
    exact ⟨x, Finset.mem_filter.mpr ⟨hm, hf⟩⟩
  obtain ⟨p, hpS, hpmax⟩ := Finset.exists_max_image S clock hS
  obtain ⟨hpm, hpf⟩ := Finset.mem_filter.mp hpS
  have hmax : ∀ x, x ∈ pointSignedMarked ν α → x ∈ frontier P → clock x ≤ clock p :=
    fun x hm hf ↦ hpmax x (Finset.mem_filter.mpr ⟨hm, hf⟩)
  have hβp : β (clock p) = p := by
    obtain ⟨t, rfl⟩ := hfront.symm ▸ hpf
    rw [hclock]
  let c := clock p
  let b : ℝ → ℂ := fun t ↦ β (c + t)
  have hb : IsClosedEmbedding b := hβ.comp (Homeomorph.addLeft c).isClosedEmbedding
  have hbrange : range b = range β := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨c + t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t - c, by dsimp [b]; congr 1; ring⟩
  have hbfront : range b = frontier P := hbrange.trans hfront
  have hb0 : b 0 = p := by simpa only [b, add_zero] using hβp
  have hbclean : ∀ t : ℝ, 0 < t → ν (b t) = 0 ∧ α (b t) = 0 := by
    intro t ht
    apply pointSigned_eq_zero_off_marked
    intro hm
    have hle := hmax (b t) hm (hbfront ▸ mem_range_self t)
    have he : clock (b t) = c + t := hclock (c + t)
    rw [he] at hle
    change c + t ≤ c at hle
    linarith
  have hboundary : ∀ q ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P q,
      ν q = Real.pi - C.flatPhysicalWidth := by
    intro q hq
    obtain ⟨C, _, he⟩ := K.boundary_coeff q hq
    exact ⟨C, he⟩
  obtain ⟨ρ, hρ, hρ0, hrange, hclosed, hproper, hρfront, hρclean, hdisj⟩ :=
    point_exists_clean_boundary_end_metric_ray ha y
      K.toPointRetainedSignedHalfplaneState.isClosed hboundary b hb hbfront hbclean
  have hstart : ρ 0 = p := hρ0.trans hb0
  have hα : α p = 0 := by
    by_contra hn
    apply hno
    refine ⟨{
      ray := ρ
      metric := hρ
      frontier := hρfront
      clean := hdisj
      budget_supported := ?_ }⟩
    rw [hstart]
    exact Finsupp.mem_support_iff.mpr hn
  have hνne : ν p ≠ 0 := by
    rcases (mem_pointSignedMarked ν α p).mp hpm with hn | hn
    · exact hn
    · exact False.elim (hn hα)
  have hνnonneg : 0 ≤ ν p := by
    have hdom := K.budget.dominates p
    have hneg : -ν p ≤ signedBudgetNeg (ν p) := le_max_left _ _
    rw [hα] at hdom
    linarith
  have hνpos : 0 < ν p := lt_of_le_of_ne hνnonneg (Ne.symm hνne)
  obtain ⟨C, hadm, hC⟩ := K.boundary_coeff p hpf
  have hwidthpos : 0 < C.flatPhysicalWidth := C.flatPhysicalWidth_pos
  have hwidthlt : C.flatPhysicalWidth < Real.pi := by linarith
  have hrange' : range ρ = β '' Ici (clock p) := by
    rw [hrange]
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨c + t, by change c ≤ c + t; exact le_add_of_nonneg_right ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t - c, by change 0 ≤ t - c; exact sub_nonneg.mpr ht, ?_⟩
      dsimp [b]
      congr 1
      ring
  have hout : ∀ t : NNReal, 0 < t → clock p < clock (ρ t) := by
    intro t ht
    obtain ⟨s, hs, he⟩ := hrange' ▸ mem_range_self t
    have hsp : s ≠ clock p := by
      intro heq
      have hz : ρ t = ρ 0 := by rw [← he, heq, hβp, hstart]
      exact (ne_of_gt ht) (hclosed.injective hz)
    rw [← he, hclock]
    exact lt_of_le_of_ne hs (Ne.symm hsp)
  exact ⟨{
    point := p
    marked := hpm
    point_frontier := hpf
    maximal := hmax
    ray := ρ
    metric := hρ
    start := hstart
    frontier := hρfront
    range_eq := hrange'
    closedEmbedding := hclosed
    proper := hproper
    outward := hout
    clean_coeff := hρclean
    clean := by rwa [hstart] at hdisj
    allocation_zero := hα
    turn_positive := hνpos
    chart := C
    admissible := hadm
    chart_coeff := hC
    width_positive := hwidthpos
    width_lt_pi := hwidthlt }⟩

/-- The actual ambient H supplies the clock. It is used only topologically;
the resulting ray uses constructed minimizing arclength. -/
theorem PointGeometricCutState.exists_positive_extreme_boundary_ray
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} (K : PointGeometricCutState a y P ν α)
    (hmarked : ∃ x, x ∈ pointSignedMarked ν α ∧ x ∈ frontier P)
    (hno : ¬ Nonempty K.CleanRay) :
    Nonempty (PointExtremeBoundaryRay a y P ν α
      (pointHalfplaneBoundaryClock K.ambient) (fun x ↦ (K.ambient x).re)) := by
  obtain ⟨_, hb, hrange, _⟩ := pointHalfplaneBoundaryClock_properties K.ambient K.region_eq
  apply K.exists_extreme_boundary_ray_for_clock ha y hmarked hno _ hb hrange
  intro t
  simp [pointHalfplaneBoundaryClock]

/-- The opposite end is obtained by reversing the same actual H-boundary
clock. Its `outward` field is strict decrease of H's real coordinate. -/
theorem PointGeometricCutState.exists_negative_extreme_boundary_ray
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} (K : PointGeometricCutState a y P ν α)
    (hmarked : ∃ x, x ∈ pointSignedMarked ν α ∧ x ∈ frontier P)
    (hno : ¬ Nonempty K.CleanRay) :
    Nonempty (PointExtremeBoundaryRay a y P ν α
      (fun t ↦ pointHalfplaneBoundaryClock K.ambient (-t))
      (fun x ↦ -(K.ambient x).re)) := by
  obtain ⟨_, hb, hrange, _⟩ := pointHalfplaneBoundaryClock_properties K.ambient K.region_eq
  have hb' : IsClosedEmbedding (fun t ↦ pointHalfplaneBoundaryClock K.ambient (-t)) :=
    hb.comp (Homeomorph.neg ℝ).isClosedEmbedding
  have hrange' : range (fun t ↦ pointHalfplaneBoundaryClock K.ambient (-t)) = frontier P := by
    rw [← hrange]
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨-t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨-t, by simp⟩
  apply K.exists_extreme_boundary_ray_for_clock ha y hmarked hno _ hb' hrange'
  intro t
  simp [pointHalfplaneBoundaryClock]

/-- Strict outward clock orientation gives the exact disjointness needed
when matching this end against an old compact edge and the opposite ray. -/
theorem PointExtremeBoundaryRay.positive_trace_disjoint_of_clock_le
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {ν α : ℂ →₀ ℝ}
    {β : ℝ → ℂ} {clock : ℂ → ℝ}
    (R : PointExtremeBoundaryRay a y P ν α β clock) {T : Set ℂ}
    (hT : ∀ x ∈ T, clock x ≤ clock R.point) :
    Disjoint (R.ray '' Ioi (0 : NNReal)) T := by
  apply disjoint_left.mpr
  rintro x ⟨t, ht, rfl⟩ hx
  exact (not_le_of_gt (R.outward t ht)) (hT _ hx)

end RepulsiveCoulomb
