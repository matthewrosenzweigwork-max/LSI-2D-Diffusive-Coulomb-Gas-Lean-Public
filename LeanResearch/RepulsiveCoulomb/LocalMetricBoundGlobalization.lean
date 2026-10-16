import LeanResearch.RepulsiveCoulomb.LocallyConstantSpeedInterval
import Mathlib.Topology.MetricSpace.Lipschitz

/-! SOURCE-ONLY, UNCOMPILED. Local pairwise bounds globalize along genuine
minimizing source segments. The subdivision is an open-cover subdivision in
parameter space, never a subdivision at seam crossings. Thus infinitely many
crossings introduce no premise and no exceptional class of curves. -/
noncomputable section
open Set
open scoped NNReal
namespace RepulsiveCoulomb

/-- The inequality version of the accepted locally constant-speed subdivision
argument, retaining the original sharp constant. -/
theorem interval_dist_le_of_local_bound {Y : Type*} [PseudoMetricSpace Y]
    {c : ℝ} {γ : Icc (0 : ℝ) 1 → Y}
    (hγ : ∀ t, ∃ U : Set (Icc (0 : ℝ) 1), IsOpen U ∧ t ∈ U ∧
      ∀ s ∈ U, ∀ t ∈ U, dist (γ s) (γ t) ≤ c * |t.1 - s.1|)
    (s t : Icc (0 : ℝ) 1) (hst : s ≤ t) :
    dist (γ s) (γ t) ≤ c * (t.1 - s.1) := by
  classical
  choose U hU hm hd using hγ
  let e : Icc s.1 t.1 → Icc (0 : ℝ) 1 :=
    fun r ↦ ⟨r.1, s.2.1.trans r.2.1, r.2.2.trans t.2.2⟩
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  obtain ⟨p, hp0, hpmono, ⟨N, hN⟩, hp⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hst
      (c := fun i ↦ e ⁻¹' U i) (fun i ↦ (hU i).preimage he) (by
        intro r _
        exact mem_iUnion.mpr ⟨e r, hm (e r)⟩)
  have hstep (n : ℕ) : dist (γ (e (p n))) (γ (e (p (n + 1)))) ≤
      c * ((p (n + 1)).1 - (p n).1) := by
    obtain ⟨i, hi⟩ := hp n
    have hn := hpmono (Nat.le_succ n)
    have hl := hi (show p n ∈ Icc (p n) (p (n + 1)) from ⟨le_rfl, hn⟩)
    have hr := hi (show p (n + 1) ∈ Icc (p n) (p (n + 1)) from ⟨hn, le_rfl⟩)
    simpa only [e, abs_of_nonneg (sub_nonneg.mpr
      (show (p n).1 ≤ (p (n + 1)).1 from hn))] using hd i _ hl _ hr
  have hbound (n : ℕ) :
      dist (γ (e (p 0))) (γ (e (p n))) ≤ c * ((p n).1 - (p 0).1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have htri := dist_triangle (γ (e (p 0))) (γ (e (p n))) (γ (e (p (n + 1))))
      have hnext := hstep n
      nlinarith
  have h0 : e (p 0) = s := Subtype.ext hp0
  have h1 : e (p N) = t := Subtype.ext (hN N le_rfl)
  have hb := hbound N
  rw [h0, h1, hp0, hN N le_rfl] at hb
  exact hb

/-- The sharp local Lipschitz constant globalizes on an actual geodesic
metric source. No global distance or variation inequality is assumed. -/
theorem lipschitzWith_of_local_dist_bound_of_segments
    {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y] {K : ℝ≥0} {F : X → Y}
    (hsegment : ∀ x z : X, ∃ γ : Icc (0 : ℝ) 1 → X,
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = z ∧ Continuous γ ∧
      ∀ s t, dist (γ s) (γ t) = |t.1 - s.1| * dist x z)
    (hlocal : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ u ∈ U, ∀ v ∈ U, dist (F u) (F v) ≤ K * dist u v) :
    LipschitzWith K F := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  obtain ⟨γ, h0, h1, hγ, hd⟩ := hsegment x z
  have hcomp : ∀ t, ∃ U : Set (Icc (0 : ℝ) 1), IsOpen U ∧ t ∈ U ∧
      ∀ s ∈ U, ∀ t ∈ U,
        dist (F (γ s)) (F (γ t)) ≤ (K * dist x z) * |t.1 - s.1| := by
    intro t
    obtain ⟨U, hU, htU, hdist⟩ := hlocal (γ t)
    refine ⟨γ ⁻¹' U, hU.preimage hγ, htU, fun s hs t ht ↦ ?_⟩
    have h := hdist (γ s) hs (γ t) ht
    rw [hd] at h
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  have h := interval_dist_le_of_local_bound hcomp
    ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ (by norm_num)
  simpa only [h0, h1, sub_zero, mul_one] using h

end RepulsiveCoulomb
