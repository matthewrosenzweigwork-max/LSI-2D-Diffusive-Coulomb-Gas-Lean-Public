import LeanResearch.RepulsiveCoulomb.PointRadialC1FiniteAssembly

/-! Construct the actual finite ordered macro-arc chain of every nonconstant
geodesic. All true vertices are source puncture times or endpoints; the exact
common-chart radial germs are retained in every C1 piece. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- The decomposition is constructed for the literal metric and its actual
geodesic. No finite-edge, smooth-boundary, or separation hypothesis is added. -/
theorem exists_pointConformal_finite_radial_C1_arc_chain {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p q : ℂ} (hpq : p ≠ q)
    (γ : Icc (0 : ℝ) 1 → ℂ)
    (hd : ∀ u v, (pointSmoothConformalEDist a y (γ u) (γ v)).toReal =
      |v.1 - u.1| * (pointSmoothConformalEDist a y p q).toReal) :
    ∃ es : List (PointRadialC1ArcPiece ha y γ),
      PointRadialC1ArcChain ha y γ ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ es ∧
      es.Nodup ∧ es ≠ [] ∧ (⋃ e ∈ es, e.curve '' Icc (0 : ℝ) 1) = range γ := by
  classical
  let P := (pointConformal_geodesic_puncture_times_finite ha y hpq γ hd).toFinset
  have hlocal : ∀ s t : Icc (0 : ℝ) 1, s < t →
      (∀ u ∈ Ioo s t, u ∉ P) →
      ∃ es : List (PointRadialC1ArcPiece ha y γ), PointRadialC1ArcChain ha y γ s t es := by
    intro s t hst hbad
    obtain ⟨e, hes, het⟩ := exists_pointRadialC1ArcPiece_of_puncture_gap ha y hpq γ hd s t hst (by
      intro u hu hγu
      apply hbad u hu
      simpa only [P, Set.Finite.mem_toFinset, mem_preimage] using hγu)
    refine ⟨[e], ?_⟩
    rw [← hes, ← het]
    exact .cons e (.nil e.finish)
  obtain ⟨es, hes⟩ := exists_pointRadialC1ArcChain_of_finite_exceptions ha y γ P hlocal
    ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ (by norm_num)
  have hempty : ∀ {u v : Icc (0 : ℝ) 1} {fs : List (PointRadialC1ArcPiece ha y γ)},
      PointRadialC1ArcChain ha y γ u v fs → fs = [] → u = v := by
    intro u v fs h
    cases h with
    | nil => intro _; rfl
    | cons e h => intro he; cases he
  have hne : es ≠ [] := by
    intro he
    have h01 := congrArg Subtype.val (hempty hes he)
    norm_num at h01
  have himage := hes.exact_image (by norm_num)
  have hI : Icc (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1) ⟨1, by norm_num⟩ = univ := by
    apply eq_univ_of_forall
    intro u
    exact u.2
  rw [hI, image_univ] at himage
  exact ⟨es, hes, hes.nodup, hne, himage⟩

end RepulsiveCoulomb
