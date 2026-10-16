module

public import LeanResearch.RepulsiveCoulomb.MetricDyadicParameter

@[expose] public section

/-! Construction of geodesics in complete metric spaces with exact midpoints,
by consistent dyadic subdivision and limits. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb
variable {X : Type*} [MetricSpace X]

def metricMidpointSample (μ : X → X → X) (x z : X) (t : ℝ) (n : ℕ) : X :=
  metricMidpointGrid μ x z n (metricDyadicIndex n t)

theorem metricMidpointSample_step (μ : X → X → X)
    (hμ : ∀ x z, dist x (μ x z) = dist x z / 2 ∧ dist (μ x z) z = dist x z / 2)
    (x z : X) {t : ℝ} (ht : t ≤ 1) (n : ℕ) :
    dist (metricMidpointSample μ x z t n) (metricMidpointSample μ x z t (n + 1)) ≤
      dist x z / (2 : ℝ) ^ (n + 1) := by
  let k := metricDyadicIndex (n + 1) t
  have hk : k ≤ 2 ^ (n + 1) := metricDyadicIndex_le (n + 1) ht
  have hdiv : k / 2 = metricDyadicIndex n t := metricDyadicIndex_div_two n t
  change dist (metricMidpointGrid μ x z n (metricDyadicIndex n t))
    (metricMidpointGrid μ x z (n + 1) k) ≤ _
  rw [← hdiv]
  rcases Nat.mod_two_eq_zero_or_one k with he | ho
  · have hk' : k = 2 * (k / 2) := by omega
    conv_lhs => arg 2; rw [hk', metricMidpointGrid_even]
    simp only [dist_self]
    positivity
  · have hk' : k = 2 * (k / 2) + 1 := by omega
    have hlt : k / 2 < 2 ^ n := by rw [pow_succ'] at hk; omega
    conv_lhs => arg 2; rw [hk', metricMidpointGrid_odd]
    rw [(hμ _ _).1, metricMidpointGrid_adjacent μ hμ x z n (k / 2) hlt, pow_succ]
    exact le_of_eq (by ring)

theorem metricMidpointSample_cauchy (μ : X → X → X)
    (hμ : ∀ x z, dist x (μ x z) = dist x z / 2 ∧ dist (μ x z) z = dist x z / 2)
    (x z : X) {t : ℝ} (ht : t ≤ 1) : CauchySeq (metricMidpointSample μ x z t) := by
  apply cauchySeq_of_le_geometric (1 / 2 : ℝ) (dist x z) (by norm_num)
  intro n
  apply (metricMidpointSample_step μ hμ x z ht n).trans
  have hle : dist x z / (2 : ℝ) ^ (n + 1) ≤ dist x z / (2 : ℝ) ^ n := by
    apply div_le_div_of_nonneg_left dist_nonneg (by positivity)
    rw [pow_succ]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]
  convert hle using 1; simp [div_eq_mul_inv, inv_pow]

variable [CompleteSpace X]

def metricMidpointGeodesic (μ : X → X → X)
    (hμ : ∀ x z, dist x (μ x z) = dist x z / 2 ∧ dist (μ x z) z = dist x z / 2)
    (x z : X) (t : Icc (0 : ℝ) 1) : X :=
  Classical.choose (cauchySeq_tendsto_of_complete (metricMidpointSample_cauchy μ hμ x z t.2.2))

theorem metricMidpointGeodesic_tendsto (μ : X → X → X)
    (hμ : ∀ x z, dist x (μ x z) = dist x z / 2 ∧ dist (μ x z) z = dist x z / 2)
    (x z : X) (t : Icc (0 : ℝ) 1) :
    Tendsto (metricMidpointSample μ x z t) atTop (𝓝 (metricMidpointGeodesic μ hμ x z t)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (metricMidpointSample_cauchy μ hμ x z t.2.2))

theorem metricMidpointGeodesic_dist_ordered (μ : X → X → X)
    (hμ : ∀ x z, dist x (μ x z) = dist x z / 2 ∧ dist (μ x z) z = dist x z / 2)
    (x z : X) (s t : Icc (0 : ℝ) 1) (hst : s ≤ t) :
    dist (metricMidpointGeodesic μ hμ x z s) (metricMidpointGeodesic μ hμ x z t) =
      (t.1 - s.1) * dist x z := by
  have hlim := (metricMidpointGeodesic_tendsto μ hμ x z s).dist
    (metricMidpointGeodesic_tendsto μ hμ x z t)
  have hpar := ((metricDyadicIndex_scaled_tendsto t.2.1).sub
    (metricDyadicIndex_scaled_tendsto s.2.1)).mul_const (dist x z)
  apply tendsto_nhds_unique hlim
  convert hpar using 1
  funext n
  unfold metricMidpointSample
  rw [metricMidpointGrid_dist_eq μ hμ x z n _ _ (metricDyadicIndex_mono n hst)
    (metricDyadicIndex_le n t.2.2)]
  ring

theorem metricMidpointGeodesic_dist (μ : X → X → X)
    (hμ : ∀ x z, dist x (μ x z) = dist x z / 2 ∧ dist (μ x z) z = dist x z / 2)
    (x z : X) (s t : Icc (0 : ℝ) 1) :
    dist (metricMidpointGeodesic μ hμ x z s) (metricMidpointGeodesic μ hμ x z t) =
      |t.1 - s.1| * dist x z := by
  rcases le_total s t with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (show s.1 ≤ t.1 from h))]
    exact metricMidpointGeodesic_dist_ordered μ hμ x z s t h
  · rw [dist_comm, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (show t.1 ≤ s.1 from h))]
    exact metricMidpointGeodesic_dist_ordered μ hμ x z t s h

theorem metricMidpointGeodesic_zero (μ : X → X → X)
    (hμ : ∀ x z, dist x (μ x z) = dist x z / 2 ∧ dist (μ x z) z = dist x z / 2)
    (x z : X) : metricMidpointGeodesic μ hμ x z ⟨0, by norm_num⟩ = x := by
  apply tendsto_nhds_unique (metricMidpointGeodesic_tendsto μ hμ x z ⟨0, by norm_num⟩)
  have hsample : metricMidpointSample μ x z 0 = fun _ : ℕ ↦ x := by
    funext n
    simp [metricMidpointSample, metricDyadicIndex, metricMidpointGrid_zero]
  rw [hsample]
  exact tendsto_const_nhds

theorem metricMidpointGeodesic_one (μ : X → X → X)
    (hμ : ∀ x z, dist x (μ x z) = dist x z / 2 ∧ dist (μ x z) z = dist x z / 2)
    (x z : X) : metricMidpointGeodesic μ hμ x z ⟨1, by norm_num⟩ = z := by
  apply tendsto_nhds_unique (metricMidpointGeodesic_tendsto μ hμ x z ⟨1, by norm_num⟩)
  have hsample : metricMidpointSample μ x z 1 = fun _ : ℕ ↦ z := by
    funext n
    have hi : metricDyadicIndex n 1 = 2 ^ n := by
      unfold metricDyadicIndex
      rw [mul_one]
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using (Nat.floor_natCast (R := ℝ) (2 ^ n))
    simp only [metricMidpointSample, hi, metricMidpointGrid_last]
  rw [hsample]
  exact tendsto_const_nhds

theorem metricMidpointGeodesic_lipschitz (μ : X → X → X)
    (hμ : ∀ x z, dist x (μ x z) = dist x z / 2 ∧ dist (μ x z) z = dist x z / 2)
    (x z : X) : LipschitzWith ⟨dist x z, dist_nonneg⟩ (metricMidpointGeodesic μ hμ x z) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [metricMidpointGeodesic_dist]
  change |t.1 - s.1| * dist x z ≤ dist x z * |s.1 - t.1|
  rw [abs_sub_comm, mul_comm]

theorem exists_geodesic_of_exact_midpoints
    (hmid : ∀ x z : X, ∃ p, dist x p = dist x z / 2 ∧ dist p z = dist x z / 2)
    (x z : X) :
    ∃ γ : Icc (0 : ℝ) 1 → X,
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = z ∧ Continuous γ ∧
      ∀ s t, dist (γ s) (γ t) = |t.1 - s.1| * dist x z := by
  let μ : X → X → X := fun u v ↦ Classical.choose (hmid u v)
  have hμ : ∀ u v, dist u (μ u v) = dist u v / 2 ∧ dist (μ u v) v = dist u v / 2 :=
    fun u v ↦ Classical.choose_spec (hmid u v)
  exact ⟨metricMidpointGeodesic μ hμ x z, metricMidpointGeodesic_zero μ hμ x z,
    metricMidpointGeodesic_one μ hμ x z, (metricMidpointGeodesic_lipschitz μ hμ x z).continuous,
    metricMidpointGeodesic_dist μ hμ x z⟩

end RepulsiveCoulomb
