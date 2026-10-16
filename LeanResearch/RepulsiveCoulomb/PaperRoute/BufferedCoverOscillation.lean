module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.BufferedConnectedCover
public import LeanResearch.RepulsiveCoulomb.PaperRoute.EuclideanBallPoincare
public import LeanResearch.RepulsiveCoulomb.PaperRoute.FinitePunctureBallPoincare
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

@[expose] public section

/-!
# Oscillation on an actual buffered planar continuum

The cover, graph, midpoint overlaps and bounded paths are the outputs of the
ordinary planar geometry producer. The analytic argument integrates an actual
finite sum of ball indicators, using the real midpoint overlap area to compare
the literal ball averages. Its public producer discharges every ball Poincare
estimate using the proved Euclidean theorem.
-/

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace RepulsiveCoulomb.PaperRoute

/-- The buffer parameter is `T`, which will later be `H * (1 + H)`. -/
def bufferedOscillationConstant (T : ℝ) : ℝ :=
  258 * T * (32 * T + 1) ^ 2

namespace BufferedOscillation

/-- Telescoping is along a literal graph walk. -/
theorem abs_sub_le_walk_length {V : Type*} {G : SimpleGraph V}
    (m : V → ℝ) {b : ℝ}
    (hedge : ∀ ⦃i j⦄, G.Adj i j → |m i - m j| ≤ b)
    {i j : V} (p : G.Walk i j) : |m i - m j| ≤ (p.length : ℝ) * b := by
  induction p with
  | nil => simp
  | @cons i j k h p ih =>
      have htri : |m i - m k| ≤ |m i - m j| + |m j - m k| := by
        simpa only [sub_add_sub_cancel] using abs_add_le (m i - m j) (m j - m k)
      simpa only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one,
        add_mul, one_mul, add_comm] using htri.trans (add_le_add (hedge h) ih)

private theorem continuous_integrableOn_ball {g : ℂ → ℝ} (hg : Continuous g)
    (c : ℂ) (r : ℝ) : IntegrableOn g (ball c r) :=
  (hg.continuousOn.integrableOn_compact (isCompact_closedBall c r)).mono_set
    ball_subset_closedBall

/-- The reference is a genuine finite positive-mass ball average, with both
the scalar and its centered absolute oscillation integrable. -/
theorem referenceBall_data {g : ℂ → ℝ} (hg : Continuous g)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    0 < volume (ball c r) ∧ volume (ball c r) < ⊤ ∧
      IntegrableOn g (ball c r) ∧
      IntegrableOn (fun x => |g x - (⨍ y in ball c r, g y)|) (ball c r) :=
  ⟨measure_ball_pos volume c hr, measure_ball_lt_top,
    continuous_integrableOn_ball hg c r,
    continuous_integrableOn_ball ((hg.sub continuous_const).abs) c r⟩

/-- Oscillation integrability is genuine on every measurable subset of the
compact continuum, independently of the size or volume of the buffer set. -/
theorem integrableOn_abs_sub_const {K Ω : Set ℂ} (hK : IsCompact K)
    (hΩK : Ω ⊆ K) {g : ℂ → ℝ} (hg : Continuous g) (a : ℝ) :
    IntegrableOn (fun x => |g x - a|) Ω :=
  (((hg.sub continuous_const).abs).continuousOn.integrableOn_compact hK).mono_set hΩK

/-- Finite-cover analytic core. The public producers below supply `hpi` from
the actual ordinary ball theorem; this reusable core is not a PI producer. -/
theorem integral_abs_sub_rootMean_le_of_ballPI
    {K U Ω : Set ℂ} {T : ℝ} (hK : IsCompact K) (hT : 1 ≤ T)
    (d : BufferedCover.Data K U T) (hΩ : MeasurableSet Ω) (hΩK : Ω ⊆ K)
    {g : ℂ → ℝ} (hg : Continuous g)
    (hgrad : IntegrableOn (fun z => ‖fderiv ℝ g z‖) U)
    (hpi : ∀ i : d.centers,
      (∫ x in ball (i : ℂ) (4 * BufferedCover.radius K T),
        |g x - (⨍ y in ball (i : ℂ) (4 * BufferedCover.radius K T), g y)|) ≤
      32 * BufferedCover.radius K T *
        ∫ y in ball (i : ℂ) (4 * BufferedCover.radius K T), ‖fderiv ℝ g y‖)
    (i₀ : d.centers) :
    (∫ x in Ω,
      |g x - (⨍ y in ball (i₀ : ℂ) (4 * BufferedCover.radius K T), g y)|) ≤
      bufferedOscillationConstant T * diam K * ∫ y in U, ‖fderiv ℝ g y‖ := by
  classical
  let ε := BufferedCover.radius K T
  let R := diam K
  let N : ℝ := d.centers.card
  let E : ℝ := ∫ y in U, ‖fderiv ℝ g y‖
  let B (i : d.centers) := ball (i : ℂ) (4 * ε)
  let m (i : d.centers) := ⨍ y in B i, g y
  let a (i : d.centers) (x : ℂ) := |g x - m i|
  have hε : 0 < ε := d.radius_pos
  have hR : 0 < R := d.diam_pos
  have hTpos : 0 < T := by linarith
  have hE : 0 ≤ E := integral_nonneg fun _ => norm_nonneg _
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hB (i : d.centers) : B i ⊆ U :=
    ball_subset_closedBall.trans (d.closedBall_subset i i.property)
  have ha (i : d.centers) : IntegrableOn (a i) (B i) :=
    continuous_integrableOn_ball ((hg.sub continuous_const).abs) i (4 * ε)
  have hapi (i : d.centers) : (∫ x in B i, a i x) ≤ 32 * ε * E :=
    (hpi i).trans (mul_le_mul_of_nonneg_left
      (setIntegral_mono_set hgrad (Eventually.of_forall fun _ => norm_nonneg _)
        (Eventually.of_forall (hB i))) (by positivity))
  have hedge {i j : d.centers} (hij : (BufferedCover.graph d.centers ε).Adj i j) :
      |m i - m j| ≤ 16 / (Real.pi * ε) * E := by
    let O := ball (((i : ℂ) + (j : ℂ)) / 2) (2 * ε)
    have hOi : O ⊆ B i := fun x hx => (d.edge_overlap hij hx).1
    have hOj : O ⊆ B j := fun x hx => (d.edge_overlap hij hx).2
    have hvol : volume.real O = 4 * Real.pi * ε ^ 2 := d.overlap_real_volume i j
    have hconst : IntegrableOn (fun _ : ℂ => |m i - m j|) O :=
      continuous_integrableOn_ball continuous_const _ _
    have harea : 4 * Real.pi * ε ^ 2 * |m i - m j| ≤ 64 * ε * E := by
      calc
        _ = ∫ _x in O, |m i - m j| := by
          rw [setIntegral_const, smul_eq_mul, hvol]
        _ ≤ ∫ x in O, a i x + a j x := by
          apply setIntegral_mono_on hconst ((ha i).mono_set hOi |>.add ((ha j).mono_set hOj))
            measurableSet_ball
          intro x hx
          dsimp [a]
          calc
            |m i - m j| = |(g x - m j) + -(g x - m i)| := by congr 1; ring
            _ ≤ |g x - m j| + |-(g x - m i)| := abs_add_le _ _
            _ = _ := by rw [abs_neg]; ring
        _ = (∫ x in O, a i x) + ∫ x in O, a j x :=
          integral_add ((ha i).mono_set hOi) ((ha j).mono_set hOj)
        _ ≤ (∫ x in B i, a i x) + ∫ x in B j, a j x :=
          add_le_add
            (setIntegral_mono_set (ha i) (Eventually.of_forall fun _ => abs_nonneg _)
              (Eventually.of_forall hOi))
            (setIntegral_mono_set (ha j) (Eventually.of_forall fun _ => abs_nonneg _)
              (Eventually.of_forall hOj))
        _ ≤ 32 * ε * E + 32 * ε * E := add_le_add (hapi i) (hapi j)
        _ = _ := by ring
    have hc : 0 < 4 * Real.pi * ε ^ 2 := by positivity
    apply (mul_le_mul_iff_right₀ hc).mp
    calc
      (4 * Real.pi * ε ^ 2) * |m i - m j| ≤ 64 * ε * E := harea
      _ = (4 * Real.pi * ε ^ 2) * (16 / (Real.pi * ε) * E) := by
        field_simp
        ring
  let C := N * (16 / (Real.pi * ε) * E)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hroot (i : d.centers) : |m i - m i₀| ≤ C := by
    obtain ⟨p, _, hp⟩ := d.bounded_path i i₀
    exact (abs_sub_le_walk_length m (fun {_ _} h => hedge h) p).trans
      (mul_le_mul_of_nonneg_right (by change (p.length : ℝ) ≤ (d.centers.card : ℝ); exact_mod_cast hp.le) (by positivity))
  let f (i : d.centers) := (B i).indicator (a i)
  have hfi (i : d.centers) : Integrable (f i) := (ha i).integrable_indicator measurableSet_ball
  have hfn (i : d.centers) (x : ℂ) : 0 ≤ f i x := by
    exact indicator_nonneg (fun _ _ => abs_nonneg _) x
  have hsum : Integrable (fun x => ∑ i : d.centers, f i x) :=
    integrable_finsetSum _ (fun i _ => hfi i)
  have hpoint (x : ℂ) (hx : x ∈ Ω) :
      |g x - m i₀| ≤ (∑ i : d.centers, f i x) + C := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (d.open_cover (hΩK hx))
    have hxi : x ∈ B i := lt_trans hi (by change 2 * ε < 4 * ε; linarith)
    calc
      _ ≤ |g x - m i| + |m i - m i₀| := by
        simpa only [sub_add_sub_cancel] using abs_add_le (g x - m i) (m i - m i₀)
      _ ≤ a i x + C := add_le_add le_rfl (hroot i)
      _ = f i x + C := by simp only [f, indicator_of_mem hxi]
      _ ≤ _ := add_le_add (Finset.single_le_sum (fun j _ => hfn j x) (Finset.mem_univ i)) le_rfl
  have hΩball : Ω ⊆ closedBall (i₀ : ℂ) R := by
    intro x hx
    exact dist_le_diam_of_mem hK.isBounded (hΩK hx) (d.centers_subset i₀.property)
  have hmass : volume.real Ω ≤ Real.pi * R ^ 2 := by
    have h := measureReal_mono (μ := volume) hΩball (by rw [Complex.volume_closedBall]; finiteness)
    simpa [measureReal_def, Complex.volume_closedBall, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hR.le, mul_comm] using h
  have hconstΩ : IntegrableOn (fun _ : ℂ => C) Ω :=
    (continuous_const.continuousOn.integrableOn_compact hK).mono_set hΩK
  have hint : (∫ x in Ω, |g x - m i₀|) ≤
      N * (32 * ε + 16 * R ^ 2 / ε) * E := by
    calc
      _ ≤ ∫ x in Ω, (∑ i : d.centers, f i x) + C :=
        setIntegral_mono_on (integrableOn_abs_sub_const hK hΩK hg _) (hsum.integrableOn.add hconstΩ)
          hΩ hpoint
      _ = (∫ x in Ω, ∑ i : d.centers, f i x) + volume.real Ω * C := by
        rw [integral_add hsum.integrableOn hconstΩ, setIntegral_const, smul_eq_mul]
      _ ≤ (∫ x, ∑ i : d.centers, f i x) + (Real.pi * R ^ 2) * C :=
        add_le_add
          (setIntegral_le_integral hsum (Eventually.of_forall fun x =>
            Finset.sum_nonneg fun i _ => hfn i x))
          (mul_le_mul_of_nonneg_right hmass hC)
      _ = (∑ i : d.centers, ∫ x in B i, a i x) + (Real.pi * R ^ 2) * C := by
        rw [integral_finsetSum _ (fun i _ => hfi i)]
        simp only [f, B, integral_indicator measurableSet_ball]
      _ ≤ (∑ _i : d.centers, 32 * ε * E) + (Real.pi * R ^ 2) * C :=
        add_le_add (Finset.sum_le_sum fun i _ => hapi i) le_rfl
      _ = N * (32 * ε + 16 * R ^ 2 / ε) * E := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
        dsimp [C, N]
        field_simp
  have hinv : 1 / T ≤ T := by
    apply (div_le_iff₀ hTpos).mpr
    nlinarith [sq_nonneg (T - 1)]
  have hscale : 32 * ε + 16 * R ^ 2 / ε = (2 / T + 256 * T) * R := by
    dsimp [ε, R, BufferedCover.radius]
    field_simp
    ring
  have hcoefficient : 32 * ε + 16 * R ^ 2 / ε ≤ 258 * T * R := by
    rw [hscale]
    have htwo : 2 / T ≤ 2 * T := by
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [mul_le_mul_of_nonneg_right htwo hR.le]
  calc
    _ ≤ N * (32 * ε + 16 * R ^ 2 / ε) * E := hint
    _ ≤ N * (258 * T * R) * E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoefficient hN) hE
    _ ≤ (32 * T + 1) ^ 2 * (258 * T * R) * E :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right d.card_le (by positivity)) hE
    _ = _ := by dsimp [bufferedOscillationConstant, R, E]; ring

end BufferedOscillation

/-- Public producer for actual continuous locally Lipschitz target scalars.
The reference value is the actual mean over a selected enlarged cover ball. -/
theorem exists_ballMean_oscillation_le_of_locallyLipschitz
    {K U Ω : Set ℂ} {T : ℝ} (hK : IsCompact K)
    (hconn : IsConnected K) (hnt : K.Nontrivial) (hT : 1 ≤ T)
    (_hU : IsOpen U)
    (hbuffer : ∀ x ∈ K, ball x (diam K / (2 * T)) ⊆ U)
    (hΩ : MeasurableSet Ω) (hΩK : Ω ⊆ K)
    {g : ℂ → ℝ} (hg : Continuous g)
    (hlocal : LocallyLipschitzOn U g)
    (hgrad : IntegrableOn (fun z => ‖fderiv ℝ g z‖) U) :
    ∃ z ∈ K,
      closedBall z (4 * BufferedCover.radius K T) ⊆ U ∧
      (∫ x in Ω, |g x - (⨍ y in ball z (4 * BufferedCover.radius K T), g y)|) ≤
        bufferedOscillationConstant T * diam K * ∫ y in U, ‖fderiv ℝ g y‖ := by
  obtain ⟨d⟩ := BufferedCover.exists_data hK hconn hnt hT hbuffer
  obtain ⟨z, hz⟩ := d.nonempty
  refine ⟨z, d.centers_subset hz, d.closedBall_subset z hz, ?_⟩
  apply BufferedOscillation.integral_abs_sub_rootMean_le_of_ballPI hK hT d hΩ hΩK hg hgrad
    (i₀ := ⟨z, hz⟩)
  intro i
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (i : ℂ) (4 * BufferedCover.radius K T))
    (hlocal.mono (d.closedBall_subset i i.property))
  convert EuclideanBall.integral_abs_sub_average_le_of_lipschitzOn_closedBall hL
    (by linarith [d.radius_pos]) using 1; ring

/-- Public finite-puncture producer. Neither puncture cardinality nor a local
Lipschitz constant enters the quantitative continuum estimate. -/
theorem exists_ballMean_oscillation_le_of_finite_punctures
    {K U Ω : Set ℂ} {T : ℝ} (hK : IsCompact K)
    (hconn : IsConnected K) (hnt : K.Nontrivial) (hT : 1 ≤ T)
    (_hU : IsOpen U)
    (hbuffer : ∀ x ∈ K, ball x (diam K / (2 * T)) ⊆ U)
    (hΩ : MeasurableSet Ω) (hΩK : Ω ⊆ K)
    {g : ℂ → ℝ} (hg : Continuous g) (S : Finset ℂ)
    (hlocal : LocallyLipschitzOn ((S : Set ℂ)ᶜ) g)
    (hgrad : IntegrableOn (fun z => ‖fderiv ℝ g z‖) U) :
    ∃ z ∈ K,
      closedBall z (4 * BufferedCover.radius K T) ⊆ U ∧
      (∫ x in Ω, |g x - (⨍ y in ball z (4 * BufferedCover.radius K T), g y)|) ≤
        bufferedOscillationConstant T * diam K * ∫ y in U, ‖fderiv ℝ g y‖ := by
  obtain ⟨d⟩ := BufferedCover.exists_data hK hconn hnt hT hbuffer
  obtain ⟨z, hz⟩ := d.nonempty
  refine ⟨z, d.centers_subset hz, d.closedBall_subset z hz, ?_⟩
  apply BufferedOscillation.integral_abs_sub_rootMean_le_of_ballPI hK hT d hΩ hΩK hg hgrad
    (i₀ := ⟨z, hz⟩)
  intro i
  have hi := hgrad.mono_set
    (ball_subset_closedBall.trans (d.closedBall_subset i i.property))
  convert FinitePunctureBall.integral_abs_sub_average_le_of_finite_punctures
    hg S hlocal (i : ℂ) (by linarith [d.radius_pos]) hi using 1; ring

end RepulsiveCoulomb.PaperRoute
