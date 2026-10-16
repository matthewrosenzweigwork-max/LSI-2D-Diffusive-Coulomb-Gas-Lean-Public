module

public import LeanResearch.RepulsiveCoulomb.FiniteLinkActualPartition

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Exact cell ownership is constructed from actual
closed/open interval separation. Each occupied interval is one whole cell;
all other cells are proved to avoid every occupied open interval. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem toIcoMod_zero_eq_self_or_zero {T x : ℝ} (hT : 0 < T)
    (hx : x ∈ Icc (0 : ℝ) T) : toIcoMod hT 0 x = x ∨ toIcoMod hT 0 x = 0 := by
  rcases lt_or_eq_of_le hx.2 with h | rfl
  · exact Or.inl ((toIcoMod_eq_self hT).mpr (by simpa using And.intro hx.1 h))
  · right
    simpa using toIcoMod_apply_right hT (0 : ℝ)

theorem finiteLinkEndpointSet_mem_of_endpoint
    {ι : Type*} [Fintype ι] {T : ℝ} (hT : 0 < T) (lo hi : ι → ℝ)
    (hlo : ∀ i, lo i ∈ Icc (0 : ℝ) T) (hhi : ∀ i, hi i ∈ Icc (0 : ℝ) T)
    (i : ι) : lo i ∈ finiteLinkEndpointSet hT lo hi ∧ hi i ∈ finiteLinkEndpointSet hT lo hi := by
  classical
  have endpoint {f : ι → ℝ} (hf : f = lo ∨ f = hi) (hb : f i ∈ Icc (0 : ℝ) T) :
      f i ∈ finiteLinkEndpointSet hT lo hi := by
    by_cases he : f i = T
    · rw [he]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · have hm : toIcoMod hT 0 (f i) = f i :=
        (toIcoMod_eq_self hT).mpr (by simpa using And.intro hb.1 (lt_of_le_of_ne hb.2 he))
      rw [← hm]
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      rcases hf with rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  exact ⟨endpoint (Or.inl rfl) (hlo i), endpoint (Or.inr rfl) (hhi i)⟩

theorem finiteLinkEndpointSet_clear_of_separated
    {ι : Type*} [Fintype ι] {T : ℝ} (hT : 0 < T) (lo hi : ι → ℝ)
    (hlo : ∀ i, lo i ∈ Icc (0 : ℝ) T) (hhi : ∀ i, hi i ∈ Icc (0 : ℝ) T)
    (hwidth : ∀ i, lo i < hi i)
    (hsep : ∀ i j, i ≠ j → Disjoint (Icc (lo i) (hi i)) (Ioo (lo j) (hi j))) :
    ∀ i x, x ∈ finiteLinkEndpointSet hT lo hi → ¬ (lo i < x ∧ x < hi i) := by
  classical
  intro i x hx hbetween
  have hexclude (j : ι) (hxj : x ∈ Icc (lo j) (hi j)) (hend : x = lo j ∨ x = hi j) : False := by
    by_cases he : j = i
    · subst j
      rcases hend with rfl | rfl
      · exact lt_irrefl _ hbetween.1
      · exact lt_irrefl _ hbetween.2
    · exact Set.disjoint_left.mp (hsep j i he) hxj hbetween
  simp only [finiteLinkEndpointSet, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact (not_lt_of_ge (hlo i).1) hbetween.1
  · exact (not_lt_of_ge (hhi i).2) hbetween.2
  · rcases toIcoMod_zero_eq_self_or_zero hT (hlo j) with he | he
    · exact hexclude j (by rw [he]; exact ⟨le_rfl, (hwidth j).le⟩) (Or.inl he)
    · rw [he] at hbetween
      exact (not_lt_of_ge (hlo i).1) hbetween.1
  · rcases toIcoMod_zero_eq_self_or_zero hT (hhi j) with he | he
    · exact hexclude j (by rw [he]; exact ⟨(hwidth j).le, le_rfl⟩) (Or.inr he)
    · rw [he] at hbetween
      exact (not_lt_of_ge (hlo i).1) hbetween.1

/-- The ownership embedding is produced by sorting actual endpoints, rather
than assumed as a cyclic-order certificate. -/
theorem exists_finiteLink_owned_partition
    {ι : Type*} [Fintype ι] {T : ℝ} (hT : 0 < T) (lo hi : ι → ℝ)
    (hlo : ∀ i, lo i ∈ Icc (0 : ℝ) T) (hhi : ∀ i, hi i ∈ Icc (0 : ℝ) T)
    (hwidth : ∀ i, lo i < hi i)
    (hsep : ∀ i j, i ≠ j → Disjoint (Icc (lo i) (hi i)) (Ioo (lo j) (hi j))) :
    ∃ N : ℕ, 0 < N ∧ ∃ u : Fin (N + 1) → ℝ,
      StrictMono u ∧ u 0 = 0 ∧ u (Fin.last N) = T ∧
      ∃ owner : ι ↪ Fin N, ∀ i,
        u (owner i).castSucc = lo i ∧ u (owner i).succ = hi i := by
  classical
  obtain ⟨N, hN, u, hu, hu0, huT, hrange⟩ := exists_finiteLink_actual_partition hT lo hi
  have hc (i : ι) : ∃ j : Fin N, u j.castSucc = lo i ∧ u j.succ = hi i := by
    obtain ⟨hl, hh⟩ := finiteLinkEndpointSet_mem_of_endpoint hT lo hi hlo hhi i
    exact finiteLink_interval_is_whole_cell u hu hrange hl hh (hwidth i)
      (finiteLinkEndpointSet_clear_of_separated hT lo hi hlo hhi hwidth hsep i)
  choose owner howner using hc
  have hinj : Function.Injective owner := by
    intro i j he
    by_contra hij
    have hl : lo i = lo j := (howner i).1.symm.trans (by rw [he]; exact (howner j).1)
    have hh : hi i = hi j := (howner i).2.symm.trans (by rw [he]; exact (howner j).2)
    have hmid : (lo i + hi i) / 2 ∈ Ioo (lo i) (hi i) := by
      constructor <;> linarith [hwidth i]
    exact Set.disjoint_left.mp (hsep i j hij) ⟨hmid.1.le, hmid.2.le⟩ (by rwa [← hl, ← hh])
  exact ⟨N, hN, u, hu, hu0, huT, ⟨owner, hinj⟩, howner⟩

/-- Distinct adjacent cells have disjoint open intervals, even at shared
endpoints. Hence an unowned cell is literal complement on its whole interior. -/
theorem finiteLink_open_cells_disjoint {N : ℕ} {u : Fin (N + 1) → ℝ}
    (hu : StrictMono u) {i j : Fin N} (hij : i ≠ j) :
    Disjoint (Ioo (u i.castSucc) (u i.succ)) (Ioo (u j.castSucc) (u j.succ)) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · have hle : i.succ ≤ j.castSucc := by change i.1 + 1 ≤ j.1; omega
    exact (not_lt_of_ge (hu.monotone hle)) (hxj.1.trans hxi.2)
  · have hle : j.succ ≤ i.castSucc := by change j.1 + 1 ≤ i.1; omega
    exact (not_lt_of_ge (hu.monotone hle)) (hxi.1.trans hxj.2)

theorem finiteLink_unowned_cell_is_complement
    {ι : Type*} {N : ℕ} {u : Fin (N + 1) → ℝ} (hu : StrictMono u)
    (lo hi : ι → ℝ) (owner : ι ↪ Fin N)
    (howner : ∀ i, u (owner i).castSucc = lo i ∧ u (owner i).succ = hi i)
    (j : Fin N) (hj : j ∉ range owner) :
    ∀ i, Disjoint (Ioo (u j.castSucc) (u j.succ)) (Ioo (lo i) (hi i)) := by
  intro i
  rw [← (howner i).1, ← (howner i).2]
  exact finiteLink_open_cells_disjoint hu (fun he ↦ hj ⟨i, he.symm⟩)

end RepulsiveCoulomb
