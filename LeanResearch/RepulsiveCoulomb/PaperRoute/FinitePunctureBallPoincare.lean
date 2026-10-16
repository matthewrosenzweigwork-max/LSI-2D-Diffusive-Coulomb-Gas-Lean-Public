import LeanResearch.RepulsiveCoulomb.PaperRoute.EuclideanBallPoincare
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Planar ball Poincaré across finitely many punctures

The cutoff is explicit, and all differential norms are actual real Fréchet
norms. No weak derivative, ACL, or Poincaré certificate is a hypothesis.
-/

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace RepulsiveCoulomb.PaperRoute.FinitePunctureBall

/-- A Lipschitz cutoff vanishing on the epsilon-neighborhood of the punctures. -/
def cutoff (T : Finset ℂ) (ε : ℝ) (x : ℂ) : ℝ :=
  min 1 (max 0 ((infDist x (T : Set ℂ) - ε) / ε))

/-- The actual finite union on which the cutoff can change the scalar. -/
def punctureNeighborhood (T : Finset ℂ) (ε : ℝ) : Set ℂ :=
  ⋃ t ∈ T, ball t (3 * ε)

lemma cutoff_nonneg (T : Finset ℂ) (ε : ℝ) (x : ℂ) : 0 ≤ cutoff T ε x :=
  le_min (by norm_num) (le_max_left _ _)

lemma cutoff_le_one (T : Finset ℂ) (ε : ℝ) (x : ℂ) : cutoff T ε x ≤ 1 :=
  min_le_left _ _

lemma cutoff_eq_zero {T : Finset ℂ} {ε : ℝ} (hε : 0 < ε) {x : ℂ}
    (hx : infDist x (T : Set ℂ) ≤ ε) : cutoff T ε x = 0 := by
  have hq : (infDist x (T : Set ℂ) - ε) / ε ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hε.le
  simp [cutoff, max_eq_left hq]

lemma cutoff_eq_one {T : Finset ℂ} {ε : ℝ} (hε : 0 < ε) {x : ℂ}
    (hx : 2 * ε ≤ infDist x (T : Set ℂ)) : cutoff T ε x = 1 := by
  have hq : 1 ≤ (infDist x (T : Set ℂ) - ε) / ε :=
    (le_div_iff₀ hε).2 (by linarith)
  exact min_eq_left (hq.trans (le_max_right _ _))

lemma cutoff_lipschitz {T : Finset ℂ} {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith ⟨ε⁻¹, inv_nonneg.mpr hε.le⟩ (cutoff T ε) := by
  have hbase : LipschitzWith ⟨ε⁻¹, inv_nonneg.mpr hε.le⟩
      (fun x : ℂ => (infDist x (T : Set ℂ) - ε) / ε) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hd := (lipschitz_infDist_pt (T : Set ℂ)).dist_le_mul x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hd
    change |(infDist x (T : Set ℂ) - ε) / ε -
      (infDist y (T : Set ℂ) - ε) / ε| ≤ ε⁻¹ * dist x y
    rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hε]
    rw [div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hε.le)
  change LipschitzWith _ (fun x => min 1 (max 0 ((infDist x (T : Set ℂ) - ε) / ε)))
  exact (hbase.const_max 0).const_min 1

lemma cutoff_continuous {T : Finset ℂ} {ε : ℝ} (hε : 0 < ε) :
    Continuous (cutoff T ε) := (cutoff_lipschitz hε).continuous

lemma norm_fderiv_cutoff_le {T : Finset ℂ} {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    ‖fderiv ℝ (cutoff T ε) x‖ ≤ ε⁻¹ :=
  norm_fderiv_le_of_lipschitz ℝ (cutoff_lipschitz hε)

lemma infDist_le_of_notMem_neighborhood {T : Finset ℂ} (hT : T.Nonempty)
    {ε : ℝ} {x : ℂ} (hx : x ∉ punctureNeighborhood T ε) :
    3 * ε ≤ infDist x (T : Set ℂ) := by
  apply le_of_not_gt
  intro h
  obtain ⟨t, ht, hxt⟩ := (infDist_lt_iff (by simpa using hT)).1 h
  exact hx (by simpa [punctureNeighborhood, mem_ball] using
    (show ∃ t ∈ T, dist x t < 3 * ε from ⟨t, ht, hxt⟩))

lemma cutoff_eventuallyEq_one_of_lt {T : Finset ℂ} {ε : ℝ}
    (hε : 0 < ε) {x : ℂ} (hx : 2 * ε < infDist x (T : Set ℂ)) :
    cutoff T ε =ᶠ[𝓝 x] fun _ => 1 := by
  filter_upwards [(continuous_infDist_pt (T : Set ℂ)).continuousAt.preimage_mem_nhds
    (Ioi_mem_nhds hx)] with y hy
  exact cutoff_eq_one hε hy.le

lemma cutoff_eventuallyEq_one {T : Finset ℂ} (hT : T.Nonempty) {ε : ℝ}
    (hε : 0 < ε) {x : ℂ} (hx : x ∉ punctureNeighborhood T ε) :
    cutoff T ε =ᶠ[𝓝 x] fun _ => 1 :=
  cutoff_eventuallyEq_one_of_lt hε (by
    have := infDist_le_of_notMem_neighborhood hT hx
    linarith)

lemma cutoff_eq_one_of_notMem {T : Finset ℂ} (hT : T.Nonempty) {ε : ℝ}
    (hε : 0 < ε) {x : ℂ} (hx : x ∉ punctureNeighborhood T ε) :
    cutoff T ε x = 1 := (cutoff_eventuallyEq_one hT hε hx).eq_of_nhds

lemma fderiv_cutoff_eq_zero_of_notMem {T : Finset ℂ} (hT : T.Nonempty) {ε : ℝ}
    (hε : 0 < ε) {x : ℂ} (hx : x ∉ punctureNeighborhood T ε) :
    fderiv ℝ (cutoff T ε) x = 0 := by
  rw [(cutoff_eventuallyEq_one hT hε hx).fderiv_eq]
  simp

/-- The genuine continuous scalar used in the approximation. -/
def cutScalar (T : Finset ℂ) (ε : ℝ) (g : ℂ → ℝ) (x : ℂ) : ℝ := cutoff T ε x * g x

lemma cutScalar_continuous {T : Finset ℂ} {ε : ℝ} (hε : 0 < ε)
    {g : ℂ → ℝ} (hg : Continuous g) : Continuous (cutScalar T ε g) :=
  (cutoff_continuous hε).mul hg

lemma cutScalar_eventuallyEq_zero {T : Finset ℂ} {ε : ℝ} (hε : 0 < ε)
    (g : ℂ → ℝ) {t : ℂ} (ht : t ∈ T) :
    cutScalar T ε g =ᶠ[𝓝 t] fun _ => 0 := by
  filter_upwards [ball_mem_nhds t hε] with x hx
  have hd : infDist x (T : Set ℂ) ≤ ε :=
    (infDist_le_dist_of_mem ht).trans (mem_ball.mp hx).le
  simp [cutScalar, cutoff_eq_zero hε hd]

lemma cutScalar_eventuallyEq_self {T : Finset ℂ} {ε : ℝ} (hε : 0 < ε)
    (g : ℂ → ℝ) {x : ℂ} (hx : 2 * ε < infDist x (T : Set ℂ)) :
    cutScalar T ε g =ᶠ[𝓝 x] g := by
  filter_upwards [cutoff_eventuallyEq_one_of_lt hε hx] with y hy
  simp [cutScalar, hy]

/-- Ordinary real multiplication is locally Lipschitz by its actual C1 map. -/
theorem locallyLipschitz_real_mul :
    LocallyLipschitz (fun p : ℝ × ℝ => p.1 * p.2) := by
  have h : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 * p.2) :=
    contDiff_fst.mul contDiff_snd
  exact h.locallyLipschitz

/-- Restricting to the subtype avoids any missing within-composition interface. -/
theorem locallyLipschitzOn_real_mul {s : Set ℂ} {f g : ℂ → ℝ}
    (hf : LocallyLipschitzOn s f) (hg : LocallyLipschitzOn s g) :
    LocallyLipschitzOn s (fun x => f x * g x) := by
  apply locallyLipschitzOn_iff_restrict.mpr
  exact locallyLipschitz_real_mul.comp (hf.restrict.prodMk hg.restrict)

/-- A local zero cutoff removes all exceptional points at the level of actual
Lipschitz witnesses. hzero is discharged by the explicit distance cutoff. -/
theorem locallyLipschitz_cutoff_mul {S : Set ℂ} (hS : IsClosed S)
    {g χ : ℂ → ℝ} {K : ℝ≥0} (hχ : LipschitzWith K χ)
    (hg : LocallyLipschitzOn Sᶜ g)
    (hzero : ∀ x ∈ S, ∃ u ∈ 𝓝 x, ∀ y ∈ u, χ y = 0) :
    LocallyLipschitz (fun x => χ x * g x) := by
  have hoff : LocallyLipschitzOn Sᶜ (fun x => χ x * g x) :=
    locallyLipschitzOn_real_mul hχ.locallyLipschitz.locallyLipschitzOn hg
  intro x
  by_cases hx : x ∈ S
  · obtain ⟨u, hu, hχu⟩ := hzero x hx
    refine ⟨0, u, hu, ?_⟩
    intro y hy z hz
    simp [hχu y hy, hχu z hz]
  · obtain ⟨L, u, hu, hLip⟩ := hoff hx
    rw [nhdsWithin_eq_nhds.mpr (hS.isOpen_compl.mem_nhds hx)] at hu
    exact ⟨L, u, hu, hLip⟩

/-- The actual compact-set Lipschitz constant exists; it is not quantitative. -/
theorem exists_lipschitzOn_closedBall_of_locallyLipschitz
    {g : ℂ → ℝ} (hg : LocallyLipschitz g) (c : ℂ) (r : ℝ) :
    ∃ K, LipschitzOnWith K g (closedBall c r) :=
  LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall c r) hg.locallyLipschitzOn

/-- AE differentiability transfers from a sequence of actual Lipschitz
approximations agreeing as germs. The finite exceptional set is genuinely null. -/
theorem ae_differentiableAt_of_lipschitzOn_approximation_germs
    {g : ℂ → ℝ} (h : ℕ → ℂ → ℝ) {S : Set ℂ} (hS : S.Finite)
    (c : ℂ) (r : ℝ)
    (hLip : ∀ n, ∃ K, LipschitzOnWith K (h n) (closedBall c r))
    (hGerm : ∀ x ∈ ball c r, x ∉ S → ∃ n, h n =ᶠ[𝓝 x] g) :
    ∀ᵐ x ∂volume.restrict (ball c r), DifferentiableAt ℝ g x := by
  have hd (n : ℕ) : ∀ᵐ x : ℂ ∂volume,
      x ∈ ball c r → DifferentiableAt ℝ (h n) x := by
    obtain ⟨K, hK⟩ := hLip n
    filter_upwards [hK.ae_differentiableWithinAt_of_mem] with x hx hxB
    exact (hx (ball_subset_closedBall hxB)).differentiableAt
      (closedBall_mem_nhds_of_mem hxB)
  have hnot : ∀ᵐ x : ℂ ∂volume, x ∉ S := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hS.measure_zero volume
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (ae_all_iff.mpr hd), ae_restrict_of_ae hnot] with x hxB hx hxS
  obtain ⟨n, hn⟩ := hGerm x hxB hxS
  exact (hx n hxB).congr_of_eventuallyEq hn.symm


lemma cutScalar_locallyLipschitz {T : Finset ℂ} {ε : ℝ} (hε : 0 < ε)
    {g : ℂ → ℝ} (hg : LocallyLipschitzOn ((T : Set ℂ)ᶜ) g) :
    LocallyLipschitz (cutScalar T ε g) := by
  apply locallyLipschitz_cutoff_mul T.finite_toSet.isClosed (cutoff_lipschitz hε) hg
  intro t ht
  refine ⟨ball t ε, ball_mem_nhds t hε, ?_⟩
  intro x hx
  exact cutoff_eq_zero hε ((infDist_le_dist_of_mem ht).trans (mem_ball.mp hx).le)

lemma cutScalar_exists_lipschitzOn_closedBall {T : Finset ℂ} {ε : ℝ} (hε : 0 < ε)
    {g : ℂ → ℝ} (hg : LocallyLipschitzOn ((T : Set ℂ)ᶜ) g) (c : ℂ) (r : ℝ) :
    ∃ K, LipschitzOnWith K (cutScalar T ε g) (closedBall c r) :=
  exists_lipschitzOn_closedBall_of_locallyLipschitz (cutScalar_locallyLipschitz hε hg) c r

/-- Actual a.e. differentiability, obtained from the explicit cutoff germs. -/
theorem ae_differentiableAt_of_finite_punctures {T : Finset ℂ} (hT : T.Nonempty)
    {g : ℂ → ℝ} (hg : LocallyLipschitzOn ((T : Set ℂ)ᶜ) g) (c : ℂ) (r : ℝ) :
    ∀ᵐ x ∂volume.restrict (ball c r), DifferentiableAt ℝ g x := by
  apply ae_differentiableAt_of_lipschitzOn_approximation_germs
    (fun n => cutScalar T (1 / ((n : ℝ) + 1)) g) T.finite_toSet c r
  · intro n
    exact cutScalar_exists_lipschitzOn_closedBall (by positivity) hg c r
  · intro x hx hxT
    have hd : 0 < infDist x (T : Set ℂ) :=
      (T.finite_toSet.isClosed.notMem_iff_infDist_pos (by simpa using hT)).mp hxT
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hd)
    refine ⟨n, cutScalar_eventuallyEq_self (by positivity) g ?_⟩
    linarith

lemma isOpen_punctureNeighborhood (T : Finset ℂ) (ε : ℝ) :
    IsOpen (punctureNeighborhood T ε) := by
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball

lemma measurableSet_punctureNeighborhood (T : Finset ℂ) (ε : ℝ) :
    MeasurableSet (punctureNeighborhood T ε) :=
  (isOpen_punctureNeighborhood T ε).measurableSet

lemma measure_punctureNeighborhood_lt_top (T : Finset ℂ) (ε : ℝ) :
    volume (punctureNeighborhood T ε) < ∞ := by
  exact measure_biUnion_lt_top T.finite_toSet fun t _ =>
    measure_ball_lt_top (μ := volume) (x := t) (r := 3 * ε)

/-- Actual planar area, without pairwise disjointness. -/
lemma punctureNeighborhood_volumeReal_le (T : Finset ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) :
    volume.real (punctureNeighborhood T ε) ≤
      9 * Real.pi * (T.card : ℝ) * ε ^ 2 := by
  have hball (t : ℂ) :
      volume.real (ball t (3 * ε)) = 9 * Real.pi * ε ^ 2 := by
    rw [measureReal_def, Complex.volume_ball, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
      ENNReal.coe_toReal, NNReal.coe_real_pi]
    ring
  calc
    volume.real (punctureNeighborhood T ε)
        ≤ ∑ t ∈ T, volume.real (ball t (3 * ε)) :=
      measureReal_biUnion_finset_le T (fun t => ball t (3 * ε))
    _ = ∑ _t ∈ T, (9 * Real.pi * ε ^ 2) := by
      exact Finset.sum_congr rfl fun t _ => hball t
    _ = 9 * Real.pi * (T.card : ℝ) * ε ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Mean oscillation is 2-Lipschitz for the L1 distance on any finite
measure space. No positivity of the mass is needed. -/
theorem integral_abs_sub_average_stability
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {g h : α → ℝ} (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ x, |g x - (⨍ y, g y ∂μ)| ∂μ) ≤
      (∫ x, |h x - (⨍ y, h y ∂μ)| ∂μ) +
        2 * ∫ x, |g x - h x| ∂μ := by
  let A : ℝ := ⨍ y, g y ∂μ
  let B : ℝ := ⨍ y, h y ∂μ
  have hmean : |A - B| ≤ ⨍ y, |g y - h y| ∂μ := by
    change |(⨍ y, g y ∂μ) - (⨍ y, h y ∂μ)| ≤ _
    rw [← average_fun_sub hg hh]
    exact norm_integral_le_integral_norm (fun y => g y - h y)
  have hmeanInt : (∫ _x : α, |A - B| ∂μ) ≤
      ∫ x, |g x - h x| ∂μ := by
    calc
      (∫ _x : α, |A - B| ∂μ)
          ≤ ∫ _x : α, (⨍ y, |g y - h y| ∂μ) ∂μ :=
        integral_mono (integrable_const _) (integrable_const _) (fun _ => hmean)
      _ = ∫ x, |g x - h x| ∂μ :=
        integral_average μ (fun y => |g y - h y|)
  have hgi : Integrable (fun x => |g x - A|) μ :=
    (hg.sub (integrable_const A)).abs
  have hhi : Integrable (fun x => |h x - B|) μ :=
    (hh.sub (integrable_const B)).abs
  have hdiff : Integrable (fun x => |g x - h x|) μ := (hg.sub hh).abs
  have hpoint (x : α) :
      |g x - A| ≤ (|h x - B| + |g x - h x|) + |A - B| := by
    calc
      |g x - A| = |((h x - B) + (g x - h x)) + (B - A)| := by
        congr 1
        ring
      _ ≤ |(h x - B) + (g x - h x)| + |B - A| := abs_add_le _ _
      _ ≤ (|h x - B| + |g x - h x|) + |A - B| :=
        add_le_add (abs_add_le _ _) (le_of_eq (abs_sub_comm B A))
  change (∫ x, |g x - A| ∂μ) ≤
    (∫ x, |h x - B| ∂μ) + 2 * ∫ x, |g x - h x| ∂μ
  calc
    (∫ x, |g x - A| ∂μ)
        ≤ ∫ x, ((|h x - B| + |g x - h x|) + |A - B|) ∂μ :=
      integral_mono hgi ((hhi.add hdiff).add (integrable_const _)) hpoint
    _ = ((∫ x, |h x - B| ∂μ) + (∫ x, |g x - h x| ∂μ)) +
        (∫ _x : α, |A - B| ∂μ) := by
      rw [integral_add (f := fun x => |h x - B| + |g x - h x|)
        (g := fun _ => |A - B|) (hhi.add hdiff) (integrable_const _),
        integral_add hhi hdiff]
    _ ≤ (∫ x, |h x - B| ∂μ) + 2 * ∫ x, |g x - h x| ∂μ := by
      linarith [hmeanInt]

/-- Integrability for continuous scalar functions on any planar ball. -/
lemma continuous_integrableOn_ball {g : ℂ → ℝ} (hg : Continuous g)
    (c : ℂ) (r : ℝ) : IntegrableOn g (ball c r) :=
  (hg.continuousOn.integrableOn_compact (isCompact_closedBall c r)).mono_set
    ball_subset_closedBall

/-- The exact ball-level stability inequality needed for the cutoff. -/
theorem integral_abs_sub_average_stability_on_ball
    {g h : ℂ → ℝ} (hg : Continuous g) (hh : Continuous h)
    (c : ℂ) (r : ℝ) :
    (∫ x in ball c r, |g x - (⨍ y in ball c r, g y)|) ≤
      (∫ x in ball c r, |h x - (⨍ y in ball c r, h y)|) +
        2 * ∫ x in ball c r, |g x - h x| := by
  have : IsFiniteMeasure (volume.restrict (ball c r)) := ⟨by
    simpa using (measure_ball_lt_top (μ := volume) (x := c) (r := r))⟩
  exact integral_abs_sub_average_stability (volume.restrict (ball c r))
    (continuous_integrableOn_ball hg c r) (continuous_integrableOn_ball hh c r)



lemma integrable_puncture_indicator (T : Finset ℂ) (ε M : ℝ) :
    Integrable ((punctureNeighborhood T ε).indicator (fun _ : ℂ => M)) :=
  (integrable_indicator_iff (measurableSet_punctureNeighborhood T ε)).2
    (integrableOn_const (measure_punctureNeighborhood_lt_top T ε).ne)

lemma integral_ball_puncture_indicator_le (T : Finset ℂ) {ε M : ℝ}
    (hε : 0 ≤ ε) (hM : 0 ≤ M) (c : ℂ) (r : ℝ) :
    (∫ x in ball c r, (punctureNeighborhood T ε).indicator (fun _ : ℂ => M) x) ≤
      (9 * Real.pi * (T.card : ℝ) * ε ^ 2) * M := by
  calc
    _ ≤ ∫ x : ℂ, (punctureNeighborhood T ε).indicator (fun _ : ℂ => M) x :=
      setIntegral_le_integral (integrable_puncture_indicator T ε M)
        (Eventually.of_forall (fun x => indicator_nonneg (fun _ _ => hM) x))
    _ = volume.real (punctureNeighborhood T ε) * M := by
      rw [integral_indicator (measurableSet_punctureNeighborhood T ε)]
      simp [smul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (punctureNeighborhood_volumeReal_le T hε) hM

lemma abs_sub_cutScalar_le_indicator {T : Finset ℂ} (hT : T.Nonempty)
    {ε : ℝ} (hε : 0 < ε) {g : ℂ → ℝ} {x : ℂ} {M : ℝ}
    (hM : |g x| ≤ M) :
    |g x - cutScalar T ε g x| ≤
      (punctureNeighborhood T ε).indicator (fun _ : ℂ => M) x := by
  by_cases hx : x ∈ punctureNeighborhood T ε
  · rw [indicator_of_mem hx]
    have hχ0 := cutoff_nonneg T ε x
    have hχ1 := cutoff_le_one T ε x
    calc
      _ = (1 - cutoff T ε x) * |g x| := by
        rw [show g x - cutScalar T ε g x = (1 - cutoff T ε x) * g x by
          dsimp [cutScalar]; ring, abs_mul, abs_of_nonneg (sub_nonneg.mpr hχ1)]
      _ ≤ M := by nlinarith [mul_nonneg hχ0 (abs_nonneg (g x))]
  · simp [indicator_of_notMem hx, cutScalar, cutoff_eq_one_of_notMem hT hε hx]

/-- Actual differential estimate, with the cutoff error confined to its explicit finite union. -/
lemma norm_fderiv_cutScalar_le_indicator {T : Finset ℂ} (hT : T.Nonempty)
    {ε : ℝ} (hε : 0 < ε) {g : ℂ → ℝ} {x : ℂ} {M : ℝ}
    (hM : |g x| ≤ M) (hg : DifferentiableAt ℝ g x)
    (hχ : DifferentiableAt ℝ (cutoff T ε) x) :
    ‖fderiv ℝ (cutScalar T ε g) x‖ ≤ ‖fderiv ℝ g x‖ +
      (punctureNeighborhood T ε).indicator (fun _ : ℂ => M / ε) x := by
  by_cases hx : x ∈ punctureNeighborhood T ε
  · rw [indicator_of_mem hx]
    change ‖fderiv ℝ (fun y => cutoff T ε y * g y) x‖ ≤ _
    rw [fderiv_fun_mul hχ hg]
    calc
      _ ≤ ‖cutoff T ε x • fderiv ℝ g x‖ + ‖g x • fderiv ℝ (cutoff T ε) x‖ :=
        norm_add_le _ _
      _ = cutoff T ε x * ‖fderiv ℝ g x‖ + |g x| * ‖fderiv ℝ (cutoff T ε) x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (cutoff_nonneg T ε x)]
      _ ≤ ‖fderiv ℝ g x‖ + M * ε⁻¹ := by
        apply add_le_add
        · simpa using mul_le_mul_of_nonneg_right (cutoff_le_one T ε x)
            (norm_nonneg (fderiv ℝ g x))
        · exact mul_le_mul hM (norm_fderiv_cutoff_le hε x)
            (norm_nonneg _) ((abs_nonneg _).trans hM)
      _ = _ := by rw [div_eq_mul_inv]
  · have hlocal : cutScalar T ε g =ᶠ[𝓝 x] g := by
      filter_upwards [cutoff_eventuallyEq_one hT hε hx] with y hy
      simp [cutScalar, hy]
    rw [hlocal.fderiv_eq, indicator_of_notMem hx, add_zero]

/-- The explicit L1 approximation error tends to zero quadratically. -/
theorem integral_abs_sub_cutScalar_le {T : Finset ℂ} (hT : T.Nonempty)
    {ε : ℝ} (hε : 0 < ε) {g : ℂ → ℝ} (hg : Continuous g)
    {c : ℂ} {r M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ closedBall c r, |g x| ≤ M) :
    (∫ x in ball c r, |g x - cutScalar T ε g x|) ≤
      9 * Real.pi * (T.card : ℝ) * M * ε ^ 2 := by
  have hi : IntegrableOn (fun x => |g x - cutScalar T ε g x|) (ball c r) :=
    ((continuous_integrableOn_ball hg c r).sub
      (continuous_integrableOn_ball (cutScalar_continuous hε hg) c r)).abs
  calc
    _ ≤ ∫ x in ball c r, (punctureNeighborhood T ε).indicator (fun _ : ℂ => M) x := by
      apply integral_mono_ae hi (integrable_puncture_indicator T ε M).integrableOn
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact abs_sub_cutScalar_le_indicator hT hε (hM x (ball_subset_closedBall hx))
    _ ≤ (9 * Real.pi * (T.card : ℝ) * ε ^ 2) * M :=
      integral_ball_puncture_indicator_le T hε.le hM0 c r
    _ = _ := by ring

/-- The explicit actual-gradient approximation error tends to zero linearly. -/
theorem integral_norm_fderiv_cutScalar_le {T : Finset ℂ} (hT : T.Nonempty)
    {ε : ℝ} (hε : 0 < ε) {g : ℂ → ℝ}
    (hlocal : LocallyLipschitzOn ((T : Set ℂ)ᶜ) g)
    {c : ℂ} {r M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ closedBall c r, |g x| ≤ M)
    (hgrad : IntegrableOn (fun x => ‖fderiv ℝ g x‖) (ball c r)) :
    (∫ x in ball c r, ‖fderiv ℝ (cutScalar T ε g) x‖) ≤
      (∫ x in ball c r, ‖fderiv ℝ g x‖) + 9 * Real.pi * (T.card : ℝ) * M * ε := by
  obtain ⟨K, hK⟩ := cutScalar_exists_lipschitzOn_closedBall hε hlocal c r
  have hi := (EuclideanBall.integrableOn_ball_data_of_lipschitzOn_closedBall hK).2.2
  have herr := (integrable_puncture_indicator T ε (M / ε)).integrableOn (s := ball c r)
  calc
    _ ≤ ∫ x in ball c r, ‖fderiv ℝ g x‖ +
        (punctureNeighborhood T ε).indicator (fun _ : ℂ => M / ε) x := by
      apply integral_mono_ae hi (hgrad.add herr)
      filter_upwards [ae_restrict_mem measurableSet_ball,
        ae_differentiableAt_of_finite_punctures hT hlocal c r,
        ae_restrict_of_ae (cutoff_lipschitz hε).ae_differentiableAt] with x hx hdg hdχ
      exact norm_fderiv_cutScalar_le_indicator hT hε
        (hM x (ball_subset_closedBall hx)) hdg hdχ
    _ = (∫ x in ball c r, ‖fderiv ℝ g x‖) +
        ∫ x in ball c r, (punctureNeighborhood T ε).indicator (fun _ : ℂ => M / ε) x :=
      integral_add hgrad herr
    _ ≤ (∫ x in ball c r, ‖fderiv ℝ g x‖) +
        (9 * Real.pi * (T.card : ℝ) * ε ^ 2) * (M / ε) :=
      add_le_add_right (integral_ball_puncture_indicator_le T hε.le
        (div_nonneg hM0 hε.le) c r) _
    _ = _ := by field_simp


/-- The ordinary coefficient-eight ball Poincaré inequality extends across a
finite puncture set. The only analytic input beyond continuity and local
Lipschitzness is integrability of the actual real differential norm. -/
theorem integral_abs_sub_average_le_of_finite_punctures
    {g : ℂ → ℝ} (hg : Continuous g) (T : Finset ℂ)
    (hlocal : LocallyLipschitzOn ((T : Set ℂ)ᶜ) g)
    (c : ℂ) {r : ℝ} (hr : 0 < r)
    (hgrad : IntegrableOn (fun x => ‖fderiv ℝ g x‖) (ball c r)) :
    (∫ x in ball c r, |g x - (⨍ y in ball c r, g y)|) ≤
      8 * r * ∫ x in ball c r, ‖fderiv ℝ g x‖ := by
  rcases T.eq_empty_or_nonempty with hT | hT
  · subst T
    have hL : LocallyLipschitz g := by simpa using hlocal
    obtain ⟨K, hK⟩ := exists_lipschitzOn_closedBall_of_locallyLipschitz hL c r
    exact EuclideanBall.integral_abs_sub_average_le_of_lipschitzOn_closedBall hK hr
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall c r).bddAbove_image hg.abs.continuousOn
  let M : ℝ := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ x ∈ closedBall c r, |g x| ≤ M := by
    intro x hx
    exact (hM₀ (mem_image_of_mem (fun y => |g y|) hx)).trans (le_max_left _ _)
  let E : ℝ := ∫ x in ball c r, ‖fderiv ℝ g x‖
  let C : ℝ := 9 * Real.pi * (T.card : ℝ) * M
  have hbound (ε : ℝ) (hε : 0 < ε) :
      (∫ x in ball c r, |g x - (⨍ y in ball c r, g y)|) ≤
        8 * r * (E + C * ε) + 2 * (C * ε ^ 2) := by
    obtain ⟨K, hK⟩ := cutScalar_exists_lipschitzOn_closedBall hε hlocal c r
    have hPI := EuclideanBall.integral_abs_sub_average_le_of_lipschitzOn_closedBall hK hr
    have hD := integral_norm_fderiv_cutScalar_le hT hε hlocal hM0 hM hgrad
    have hL := integral_abs_sub_cutScalar_le hT hε hg hM0 hM
    calc
      _ ≤ (∫ x in ball c r, |cutScalar T ε g x -
          (⨍ y in ball c r, cutScalar T ε g y)|) +
          2 * ∫ x in ball c r, |g x - cutScalar T ε g x| :=
        integral_abs_sub_average_stability_on_ball hg (cutScalar_continuous hε hg) c r
      _ ≤ 8 * r * (∫ x in ball c r, ‖fderiv ℝ (cutScalar T ε g) x‖) +
          2 * ∫ x in ball c r, |g x - cutScalar T ε g x| :=
        add_le_add hPI le_rfl
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left hD (by positivity))
        (mul_le_mul_of_nonneg_left hL (by norm_num))
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n : ℕ =>
      8 * r * (E + C * (1 / ((n : ℝ) + 1))) +
        2 * (C * (1 / ((n : ℝ) + 1)) ^ 2)) atTop (𝓝 (8 * r * E)) := by
    convert ((tendsto_const_nhds.add (ht.const_mul C)).const_mul (8 * r)).add
      ((ht.pow 2).const_mul C |>.const_mul 2) using 1; simp
  exact ge_of_tendsto hlim (Eventually.of_forall (fun n =>
    hbound (1 / ((n : ℝ) + 1)) (by positivity)))

/-- Physical-gradient form, valid for every real radius, including empty balls. -/
theorem integral_abs_sub_average_le_gradient_of_finite_punctures
    {g : ℂ → ℝ} (hg : Continuous g) (T : Finset ℂ)
    (hlocal : LocallyLipschitzOn ((T : Set ℂ)ᶜ) g)
    (c : ℂ) (r : ℝ)
    (hgrad : IntegrableOn (fun x => ‖gradient g x‖) (ball c r)) :
    (∫ x in ball c r, |g x - (⨍ y in ball c r, g y)|) ≤
      8 * r * ∫ x in ball c r, ‖gradient g x‖ := by
  simp only [EuclideanBall.norm_gradient_eq_norm_fderiv] at hgrad ⊢
  by_cases hr : 0 < r
  · exact integral_abs_sub_average_le_of_finite_punctures hg T hlocal c hr hgrad
  · simp [ball_eq_empty.mpr (le_of_not_gt hr)]

end RepulsiveCoulomb.PaperRoute.FinitePunctureBall
