module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Tactic

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Construct the finite cyclic ordering of supplied
actual link endpoints by reducing their real lifts to one chosen period and
sorting. No ordering/subdivision is supplied as an input. The interval lemmas
prove coverage, absence of hidden endpoints, and constant occupation on every
open cell. Passing from occupied circular arcs to their cut-open intervals is
a separate geometric application; it is not silently included here. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Include the artificial cut at both ends, even if no seam passes there. -/
def finiteLinkEndpointSet {ι : Type*} [Fintype ι] {T : ℝ} (hT : 0 < T)
    (lo hi : ι → ℝ) : Finset ℝ :=
  insert 0 (insert T ((Finset.univ.image (fun i ↦ toIcoMod hT 0 (lo i))) ∪
    (Finset.univ.image (fun i ↦ toIcoMod hT 0 (hi i)))))

theorem finiteLinkEndpointSet_bounds {ι : Type*} [Fintype ι] {T : ℝ} (hT : 0 < T)
    (lo hi : ι → ℝ) {x : ℝ} (hx : x ∈ finiteLinkEndpointSet hT lo hi) :
    x ∈ Icc 0 T := by
  classical
  simp only [finiteLinkEndpointSet, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact ⟨le_rfl, hT.le⟩
  · exact ⟨hT.le, le_rfl⟩
  · exact ⟨(toIcoMod_mem_Ico' hT _).1, (toIcoMod_mem_Ico' hT _).2.le⟩
  · exact ⟨(toIcoMod_mem_Ico' hT _).1, (toIcoMod_mem_Ico' hT _).2.le⟩

/-- A concrete order embedding, with range exactly the constructed endpoints. -/
def finiteLinkEndpointOrder {ι : Type*} [Fintype ι] {T : ℝ} (hT : 0 < T)
    (lo hi : ι → ℝ) : Fin (finiteLinkEndpointSet hT lo hi).card ↪o ℝ :=
  (finiteLinkEndpointSet hT lo hi).orderEmbOfFin rfl

theorem finiteLinkEndpointOrder_range {ι : Type*} [Fintype ι] {T : ℝ}
    (hT : 0 < T) (lo hi : ι → ℝ) :
    range (finiteLinkEndpointOrder hT lo hi) = ↑(finiteLinkEndpointSet hT lo hi) :=
  Finset.range_orderEmbOfFin _ rfl

theorem finiteLinkEndpointOrder_boundary {ι : Type*} [Fintype ι] {T : ℝ}
    (hT : 0 < T) (lo hi : ι → ℝ) (i : ι) :
    (∃ j, finiteLinkEndpointOrder hT lo hi j = toIcoMod hT 0 (lo i)) ∧
    (∃ j, finiteLinkEndpointOrder hT lo hi j = toIcoMod hT 0 (hi i)) := by
  classical
  constructor
  · change toIcoMod hT 0 (lo i) ∈ range (finiteLinkEndpointOrder hT lo hi)
    rw [finiteLinkEndpointOrder_range]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
  · change toIcoMod hT 0 (hi i) ∈ range (finiteLinkEndpointOrder hT lo hi)
    rw [finiteLinkEndpointOrder_range]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))

/-- Consecutive sorted endpoints have no omitted seam endpoint between them. -/
theorem finiteLinkEndpointOrder_no_endpoint_between
    {ι : Type*} [Fintype ι] {T : ℝ} (hT : 0 < T) (lo hi : ι → ℝ)
    (i j : Fin (finiteLinkEndpointSet hT lo hi).card) (hnext : j.1 = i.1 + 1)
    {x : ℝ} (hx : x ∈ finiteLinkEndpointSet hT lo hi) :
    ¬ (finiteLinkEndpointOrder hT lo hi i < x ∧ x < finiteLinkEndpointOrder hT lo hi j) := by
  intro hbetween
  have hxr : x ∈ range (finiteLinkEndpointOrder hT lo hi) := by
    rw [finiteLinkEndpointOrder_range]
    exact hx
  obtain ⟨k, rfl⟩ := hxr
  have hik : i < k := (finiteLinkEndpointOrder hT lo hi).lt_iff_lt.mp hbetween.1
  have hkj : k < j := (finiteLinkEndpointOrder hT lo hi).lt_iff_lt.mp hbetween.2
  have hik' : i.1 < k.1 := hik
  have hkj' : k.1 < j.1 := hkj
  omega

/-- All genuine open cells of a finite subdivision, represented by their
actual endpoint pair. This is a finite type, not a hypothetical cell family. -/
def FiniteLinkGap (S : Finset ℝ) :=
  {p : {x // x ∈ S} × {x // x ∈ S} //
    p.1.1 < p.2.1 ∧ ∀ z ∈ S, ¬ (p.1.1 < z ∧ z < p.2.1)}

instance (S : Finset ℝ) : Finite (FiniteLinkGap S) := by
  unfold FiniteLinkGap
  infer_instance

def FiniteLinkGap.left {S : Finset ℝ} (G : FiniteLinkGap S) : ℝ := G.1.1.1
def FiniteLinkGap.right {S : Finset ℝ} (G : FiniteLinkGap S) : ℝ := G.1.2.1

/-- Every point in the whole link interval is either an endpoint or lies in
an actual adjacent-endpoint cell. Both bounding endpoints are constructed by
finite maximum/minimum, including when the seam set itself was empty. -/
theorem exists_finiteLinkGap_cover {S : Finset ℝ} {a b x : ℝ}
    (ha : a ∈ S) (hb : b ∈ S) (hx : x ∈ Icc a b) :
    x ∈ S ∨ ∃ G : FiniteLinkGap S, x ∈ Ioo G.left G.right := by
  classical
  by_cases hxS : x ∈ S
  · exact Or.inl hxS
  · right
    let L := S.filter (fun z ↦ z < x)
    let R := S.filter (fun z ↦ x < z)
    have hax : a < x := lt_of_le_of_ne hx.1 (fun he ↦ hxS (he ▸ ha))
    have hxb : x < b := lt_of_le_of_ne hx.2 (fun he ↦ hxS (he.symm ▸ hb))
    have hL : L.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, hax⟩⟩
    have hR : R.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hb, hxb⟩⟩
    let l := L.max' hL
    let r := R.min' hR
    have hl : l ∈ S ∧ l < x := Finset.mem_filter.mp (L.max'_mem hL)
    have hr : r ∈ S ∧ x < r := Finset.mem_filter.mp (R.min'_mem hR)
    have hclear : ∀ z ∈ S, ¬ (l < z ∧ z < r) := by
      intro z hz hbet
      rcases lt_trichotomy z x with hzx | rfl | hxz
      · have hzL : z ∈ L := Finset.mem_filter.mpr ⟨hz, hzx⟩
        exact (not_lt_of_ge (L.le_max' z hzL)) hbet.1
      · exact hxS hz
      · have hzR : z ∈ R := Finset.mem_filter.mpr ⟨hz, hxz⟩
        exact (not_lt_of_ge (R.min'_le z hzR)) hbet.2
    exact ⟨⟨(⟨l, hl.1⟩, ⟨r, hr.1⟩), hl.2.trans hr.2, hclear⟩, hl.2, hr.2⟩

/-- Every cut-open occupied interval is constant on each open cell once its
two actual endpoints have been inserted. Thus no hidden sector can start or
stop inside a cell. Complement cells need no special covering assumption. -/
theorem FiniteLinkGap.mem_Icc_iff {S : Finset ℝ} (G : FiniteLinkGap S)
    {u v x y : ℝ} (hu : u ∈ S) (hv : v ∈ S)
    (hx : x ∈ Ioo G.left G.right) (hy : y ∈ Ioo G.left G.right) :
    x ∈ Icc u v ↔ y ∈ Icc u v := by
  have step : ∀ x ∈ Ioo G.left G.right, ∀ y ∈ Ioo G.left G.right,
      x ∈ Icc u v → y ∈ Icc u v := by
    intro x hx y hy hxy
    constructor
    · by_contra hn
      have hyu : y < u := lt_of_not_ge hn
      exact G.2.2 u hu ⟨hy.1.trans hyu, hxy.1.trans_lt hx.2⟩
    · by_contra hn
      have hvy : v < y := lt_of_not_ge hn
      exact G.2.2 v hv ⟨hx.1.trans_le hxy.2, hvy.trans hy.2⟩
  exact ⟨step x hx y hy, step y hy x hx⟩

end RepulsiveCoulomb
