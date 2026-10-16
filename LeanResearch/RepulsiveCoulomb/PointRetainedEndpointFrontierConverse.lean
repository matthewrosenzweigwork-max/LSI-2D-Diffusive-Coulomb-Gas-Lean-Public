import LeanResearch.RepulsiveCoulomb.PointFlatLinkFrontierEndpoint

/-! SOURCE-ONLY, UNCOMPILED. Converse to the old-frontier endpoint lemma.
A positive-radius endpoint of a PROPER full retained interval is genuinely on
the old frontier. Nearby exterior angular coordinates construct the required
noninteriority; no asserted boundary-ray continuation is assumed. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem PointRetainedConeNeighborhood.endpoint_mem_frontier
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p z : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) (hproper : C.hi-C.lo<2*Real.pi)
    (hzR : (pointSmoothConformalEDist a y z p).toReal<C.radius)
    {r θ : ℝ} (hr : 0<r) (hend : θ=C.lo ∨ θ=C.hi)
    (hchart : C.chart z=pointRadialSectorPoint r θ) : z∈frontier P := by
  have hθ : θ∈Icc C.lo C.hi:=by
    rcases hend with rfl | rfl
    · exact ⟨le_rfl,C.width_pos.le⟩
    · exact ⟨C.width_pos.le,le_rfl⟩
  have hrR : r<C.radius:=by
    have hn:=C.retainedWidth_chart_norm hzR.le
    rw [hchart,pointRadialSectorPoint_norm hr.le] at hn
    exact hn.trans_lt hzR
  have hzP : z∈P:=(C.retained z hzR.le).mpr ⟨r,⟨hr.le,hrR.le⟩,θ,hθ,hchart⟩
  refine ⟨subset_closure hzP,?_⟩
  intro hzI
  let γ : ℝ → ℂ:=fun φ ↦ C.chart.symm (pointRadialSectorPoint r φ)
  have hγtarget (φ : ℝ) : pointRadialSectorPoint r φ∈C.chart.target:=
    (C.retainedWidth_inverse (by rw [pointRadialSectorPoint_norm hr.le]; exact hrR.le)).1
  have hγc : Continuous γ:=C.chart.symm.continuousOn.comp_continuous
    (by unfold pointRadialSectorPoint; fun_prop) hγtarget
  have hγθ : γ θ=z:=by
    dsimp [γ]
    rw [← hchart,C.chart.left_inv (C.source hzR.le)]
  have hθU : θ∈γ ⁻¹' interior P:=by simpa only [mem_preimage,hγθ] using hzI
  obtain ⟨δ,hδ,hδU⟩:=Metric.mem_nhds_iff.mp
    ((isOpen_interior.preimage hγc).mem_nhds hθU)
  let gap:=2*Real.pi-(C.hi-C.lo)
  have hgap : 0<gap:=sub_pos.mpr hproper
  let ε:=min δ gap/3
  have hε : 0<ε:=div_pos (lt_min hδ hgap) (by norm_num)
  have hεδ : ε<δ:=by dsimp [ε]; linarith [min_le_left δ gap,lt_min hδ hgap]
  have hεgap : 2*ε<gap:=by dsimp [ε]; linarith [min_le_right δ gap,hgap]
  let φ:=if θ=C.lo then C.lo-ε else C.hi+ε
  have hφoutside : φ∉Icc C.lo C.hi:=by
    by_cases hθlo : θ=C.lo
    · dsimp [φ]; rw [if_pos hθlo]; intro hm; linarith [hm.1]
    · dsimp [φ]; rw [if_neg hθlo]; intro hm; linarith [hm.2]
  have hφθ : dist φ θ<δ:=by
    rw [Real.dist_eq]
    rcases hend with hθlo | hθhi
    · simp only [φ,if_pos hθlo,hθlo,sub_sub_cancel_left,abs_neg,abs_of_pos hε]
      exact hεδ
    · by_cases he : θ=C.lo
      · have hlh : C.lo=C.hi:=he.symm.trans hθhi
        exact False.elim (C.width_pos.ne hlh)
      · simp only [φ,if_neg he,hθhi,add_sub_cancel_left,abs_of_pos hε]
        exact hεδ
  have hγφP : γ φ∈P:=interior_subset (hδU hφθ)
  obtain ⟨_,hγφchart,hγφdist⟩:=C.retainedWidth_inverse
    (show ‖pointRadialSectorPoint r φ‖≤C.radius by rw [pointRadialSectorPoint_norm hr.le]; exact hrR.le)
  have hγR : (pointSmoothConformalEDist a y (γ φ) p).toReal≤C.radius:=by
    change (pointSmoothConformalEDist a y (C.chart.symm (pointRadialSectorPoint r φ)) p).toReal≤C.radius
    rw [hγφdist,pointRadialSectorPoint_norm hr.le]
    exact hrR.le
  obtain ⟨s,hs,ψ,hψ,he⟩:=(C.retained (γ φ) hγR).mp hγφP
  have hn:=congrArg norm (hγφchart.symm.trans he)
  rw [pointRadialSectorPoint_norm hr.le,pointRadialSectorPoint_norm hs.1] at hn
  subst s
  have hphase : Circle.exp φ=Circle.exp ψ:=by
    apply Subtype.ext
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne')
    exact hγφchart.symm.trans he
  have hφlo : C.lo-ε≤φ:=by dsimp [φ]; split_ifs <;> linarith [C.width_pos]
  have hφhi : φ≤C.hi+ε:=by dsimp [φ]; split_ifs <;> linarith [C.width_pos]
  have hφI : φ∈Ico (C.lo-ε) (C.lo-ε+2*Real.pi):=by
    refine ⟨hφlo,?_⟩
    dsimp [gap] at hεgap
    linarith
  have hψI : ψ∈Ico (C.lo-ε) (C.lo-ε+2*Real.pi):=by
    dsimp [gap] at hεgap
    constructor <;> linarith [hψ.1,hψ.2]
  have hφψ : φ=ψ:=(Circle.exp_injOn_Ico (a:=C.lo-ε)
    (b:=C.lo-ε+2*Real.pi) (by linarith)) hφI hψI hphase
  exact hφoutside (hφψ.symm ▸ hψ)

end RepulsiveCoulomb
