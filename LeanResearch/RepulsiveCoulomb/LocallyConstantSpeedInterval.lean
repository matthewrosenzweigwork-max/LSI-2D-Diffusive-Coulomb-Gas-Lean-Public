module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! Concrete compact-interval consequences of local constant-speed minimizing.
The metric may have no curvature sign and geodesics need not be unique. An
endpoint shortcut produces two actual minimizing restrictions at a retained
interior parameter, rather than postulating a global continuation theorem. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Every parameter has a relatively open interval neighborhood on which all
pairwise distances agree with a fixed multiple of parameter distance. -/
def LocallyConstantSpeedInterval {X : Type*} [PseudoMetricSpace X]
    (c : ℝ) (γ : Icc (0 : ℝ) 1 → X) : Prop :=
  ∀ t, ∃ U : Set (Icc (0 : ℝ) 1), IsOpen U ∧ t ∈ U ∧
    ∀ s ∈ U, ∀ t ∈ U, dist (γ s) (γ t) = c * |t.1 - s.1|

/-- Local constant-speed minimizing gives the global sharp constant-speed Lipschitz bound,
by a genuine finite open-cover subdivision and the polygon inequality. -/
theorem locallyConstantSpeedInterval_dist_le_of_le {X : Type*} [PseudoMetricSpace X]
    {c : ℝ} {γ : Icc (0 : ℝ) 1 → X} (hγ : LocallyConstantSpeedInterval c γ)
    (s t : Icc (0 : ℝ) 1) (hst : s ≤ t) : dist (γ s) (γ t) ≤ c * (t.1 - s.1) := by
  classical
  choose U hU hm hd using hγ
  let e : Icc s.1 t.1 → Icc (0 : ℝ) 1 :=
    fun r ↦ ⟨r.1, s.2.1.trans r.2.1, r.2.2.trans t.2.2⟩
  have he : Continuous e := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  obtain ⟨p, hp0, hpmono, ⟨N, hN⟩, hp⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hst
      (c := fun i ↦ e ⁻¹' U i) (fun i ↦ (hU i).preimage he) (by
        intro r _
        exact mem_iUnion.mpr ⟨e r, hm (e r)⟩)
  have hstep (n : ℕ) : dist (γ (e (p n))) (γ (e (p (n + 1)))) =
      c * ((p (n + 1)).1 - (p n).1) := by
    obtain ⟨i, hi⟩ := hp n
    have hn := hpmono (Nat.le_succ n)
    have hl := hi (show p n ∈ Icc (p n) (p (n + 1)) from ⟨le_rfl, hn⟩)
    have hr := hi (show p (n + 1) ∈ Icc (p n) (p (n + 1)) from ⟨hn, le_rfl⟩)
    simpa only [e, abs_of_nonneg (sub_nonneg.mpr (show (p n).1 ≤ (p (n + 1)).1 from hn))] using hd i _ hl _ hr
  have hbound (n : ℕ) : dist (γ (e (p 0))) (γ (e (p n))) ≤ c * ((p n).1 - (p 0).1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have htri := dist_triangle (γ (e (p 0))) (γ (e (p n))) (γ (e (p (n + 1))))
      rw [hstep] at htri
      nlinarith
  have h0 : e (p 0) = s := Subtype.ext hp0
  have h1 : e (p N) = t := Subtype.ext (hN N le_rfl)
  have hb := hbound N
  rw [h0, h1, hp0, hN N le_rfl] at hb
  exact hb

theorem locallyConstantSpeedInterval_dist_le {X : Type*} [PseudoMetricSpace X]
    {c : ℝ} {γ : Icc (0 : ℝ) 1 → X} (hγ : LocallyConstantSpeedInterval c γ)
    (s t : Icc (0 : ℝ) 1) : dist (γ s) (γ t) ≤ c * |t.1 - s.1| := by
  rcases le_total s t with h | h
  · simpa only [abs_of_nonneg (sub_nonneg.mpr (show s.1 ≤ t.1 from h))] using
      locallyConstantSpeedInterval_dist_le_of_le hγ s t h
  · rw [dist_comm, abs_sub_comm]
    simpa only [abs_of_nonneg (sub_nonneg.mpr (show t.1 ≤ s.1 from h))] using
      locallyConstantSpeedInterval_dist_le_of_le hγ t s h

/-- A minimizing prefix of a locally constant-speed curve is minimizing between
every two of its parameters; this follows from metric inequalities alone. -/
theorem locallyConstantSpeedInterval_prefix_distance {X : Type*} [PseudoMetricSpace X]
    {c : ℝ} {γ : Icc (0 : ℝ) 1 → X} (hγ : LocallyConstantSpeedInterval c γ)
    (u : Icc (0 : ℝ) 1)
    (hu : dist (γ ⟨0, by norm_num⟩) (γ u) = c * u.1)
    (s t : Icc (0 : ℝ) 1) (hs : s ≤ u) (ht : t ≤ u) :
    dist (γ s) (γ t) = c * |t.1 - s.1| := by
  suffices hh : ∀ s t : Icc (0 : ℝ) 1, s ≤ t → t ≤ u →
      dist (γ s) (γ t) = c * (t.1 - s.1) by
    rcases le_total s t with h | h
    · simpa only [abs_of_nonneg (sub_nonneg.mpr (show s.1 ≤ t.1 from h))] using hh s t h ht
    · rw [dist_comm, abs_sub_comm]
      simpa only [abs_of_nonneg (sub_nonneg.mpr (show t.1 ≤ s.1 from h))] using hh t s h hs
  intro s t hst htu
  apply le_antisymm (locallyConstantSpeedInterval_dist_le_of_le hγ s t hst)
  have h0s := locallyConstantSpeedInterval_dist_le_of_le hγ ⟨0, by norm_num⟩ s s.2.1
  have htu' := locallyConstantSpeedInterval_dist_le_of_le hγ t u htu
  have htri₁ := dist_triangle (γ ⟨0, by norm_num⟩) (γ s) (γ u)
  have htri₂ := dist_triangle (γ s) (γ t) (γ u)
  rw [hu] at htri₁
  change dist (γ ⟨0, by norm_num⟩) (γ s) ≤ c * (s.1 - 0) at h0s
  nlinarith

/-- If the full locally constant-speed curve has an endpoint shortcut, there is
an actual interior corner with a minimizing prefix and a minimizing next cell,
while their concatenation has a shortcut. No uniqueness is required. -/
theorem exists_locallyConstantSpeedInterval_shortcut_corner {X : Type*} [PseudoMetricSpace X]
    {c : ℝ} {γ : Icc (0 : ℝ) 1 → X} (hγ : LocallyConstantSpeedInterval c γ)
    (hshort : dist (γ ⟨0, by norm_num⟩) (γ ⟨1, by norm_num⟩) < c) :
    ∃ u v : Icc (0 : ℝ) 1, 0 < u.1 ∧ u < v ∧
      (∀ s t, s ≤ u → t ≤ u → dist (γ s) (γ t) = c * |t.1 - s.1|) ∧
      (∀ s ∈ Icc u v, ∀ t ∈ Icc u v, dist (γ s) (γ t) = c * |t.1 - s.1|) ∧
      dist (γ ⟨0, by norm_num⟩) (γ v) < c * v.1 := by
  classical
  have hγkeep := hγ
  choose U hU hm hd using hγ
  obtain ⟨p, hp0, hpmono, ⟨N, hN⟩, hp⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hU (by
      intro t _
      exact mem_iUnion.mpr ⟨t, hm t⟩)
  have hex : ∃ n, dist (γ ⟨0, by norm_num⟩) (γ (p n)) < c * (p n).1 := by
    refine ⟨N, ?_⟩
    rw [hN N le_rfl]
    change dist (γ ⟨0, by norm_num⟩) (γ ⟨1, by norm_num⟩) < c * 1
    simpa only [mul_one] using hshort
  let k := Nat.find hex
  have hk : dist (γ ⟨0, by norm_num⟩) (γ (p k)) < c * (p k).1 := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro he
    have hpzero : p 0 = ⟨0, by norm_num⟩ := hp0
    simp only [he, hpzero, dist_self, mul_zero] at hk
    exact (lt_irrefl (0 : ℝ)) hk
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hprev : ¬ dist (γ ⟨0, by norm_num⟩) (γ (p n)) < c * (p n).1 :=
    Nat.find_min hex (by omega)
  have hpre : dist (γ ⟨0, by norm_num⟩) (γ (p n)) = c * (p n).1 := by
    apply le_antisymm
    · simpa only [sub_zero] using
        locallyConstantSpeedInterval_dist_le_of_le hγkeep ⟨0, by norm_num⟩ (p n) (p n).2.1
    · exact le_of_not_gt hprev
  have hnv : p n ≤ p (n + 1) := hpmono (Nat.le_succ n)
  obtain ⟨i, hi⟩ := hp n
  have hcell : ∀ s ∈ Icc (p n) (p (n + 1)), ∀ t ∈ Icc (p n) (p (n + 1)),
      dist (γ s) (γ t) = c * |t.1 - s.1| := fun s hs t ht ↦ hd i s (hi hs) t (hi ht)
  have hnew : dist (γ ⟨0, by norm_num⟩) (γ (p (n + 1))) < c * (p (n + 1)).1 := by
    simpa only [hn] using hk
  have hnpos : 0 < (p n).1 := by
    by_contra hh
    have hnzero : p n = ⟨0, by norm_num⟩ :=
      Subtype.ext (le_antisymm (le_of_not_gt hh) (p n).2.1)
    have he := hcell (p n) ⟨le_rfl, hnv⟩ (p (n + 1)) ⟨hnv, le_rfl⟩
    rw [hnzero] at he
    simp only [sub_zero, abs_of_nonneg (p (n + 1)).2.1] at he
    nlinarith
  have hstrict : p n < p (n + 1) := by
    apply lt_of_le_of_ne hnv
    intro he
    rw [← he] at hnew
    nlinarith
  exact ⟨p n, p (n + 1), hnpos, hstrict,
    locallyConstantSpeedInterval_prefix_distance hγkeep (p n) hpre, hcell, hnew⟩

end RepulsiveCoulomb
