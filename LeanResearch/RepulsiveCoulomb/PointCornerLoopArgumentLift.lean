module

public import LeanResearch.RepulsiveCoulomb.PointRegularArcPointArgument

@[expose] public section

/-! A continuous loop with one-sided regular endpoint extensions has an
actual continuous boundary-point argument lift up to both sides of its corner.
Two divided differences remove the endpoint zeros. No global C1 regularity
or winding/sector value is assumed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

def pointCornerLoopPointVector (γ : ℝ → ℂ) (u : ℝ) : ℂ :=
  -dslope (dslope γ 0) 1 u

theorem closed_loop_dslope_one {γ : ℝ → ℂ} (hclose : γ 1 = γ 0) :
    dslope γ 0 1 = 0 := by
  rw [dslope_of_ne _ (show (1 : ℝ) ≠ 0 by norm_num), slope_def_module, hclose]
  simp

theorem hasDerivAt_closed_loop_dslope_one {γ : ℝ → ℂ}
    (hclose : γ 1 = γ 0) (hd : DifferentiableAt ℝ γ 1) :
    HasDerivAt (dslope γ 0) (deriv γ 1) 1 := by
  have hg : DifferentiableAt ℝ (dslope γ 0) 1 :=
    (differentiableAt_dslope_of_ne (show (1 : ℝ) ≠ 0 by norm_num)).mpr hd
  have hprod : HasDerivAt (fun u : ℝ => u • dslope γ 0 u) (deriv (dslope γ 0) 1) 1 := by
    convert! (hasDerivAt_id (1 : ℝ)).smul hg.hasDerivAt using 1 <;>
      simp [closed_loop_dslope_one hclose]
  have heq : (fun u : ℝ => u • dslope γ 0 u) = (fun u => γ u - γ 0) := by
    funext u
    simpa only [sub_zero] using sub_smul_dslope γ (0 : ℝ) u
  rw [heq] at hprod
  exact hg.hasDerivAt.congr_deriv (hprod.unique (hd.hasDerivAt.sub_const (γ 0)))

theorem pointCornerLoopPointVector_endpoints {γ : ℝ → ℂ}
    (hclose : γ 1 = γ 0) (hd : DifferentiableAt ℝ γ 1) :
    pointCornerLoopPointVector γ 0 = deriv γ 0 ∧
      pointCornerLoopPointVector γ 1 = -deriv γ 1 := by
  constructor
  · rw [pointCornerLoopPointVector, dslope_of_ne _ (show (0 : ℝ) ≠ 1 by norm_num),
      slope_def_module, dslope_same, closed_loop_dslope_one hclose]
    simp
  · rw [pointCornerLoopPointVector, dslope_same, (hasDerivAt_closed_loop_dslope_one hclose hd).deriv]

theorem pointCornerLoopPointVector_factor {γ : ℝ → ℂ} (hclose : γ 1 = γ 0) (u : ℝ) :
    (u * (1 - u)) • pointCornerLoopPointVector γ u = γ u - γ 0 := by
  have hg := sub_smul_dslope (dslope γ 0) 1 u
  rw [closed_loop_dslope_one hclose, sub_zero] at hg
  calc
    (u * (1 - u)) • pointCornerLoopPointVector γ u =
        u • ((u - 1) • dslope (dslope γ 0) 1 u) := by
      rw [pointCornerLoopPointVector, smul_neg, ← neg_smul, smul_smul]
      congr 1
      ring
    _ = u • dslope γ 0 u := by rw [hg]
    _ = γ u - γ 0 := by simpa only [sub_zero] using sub_smul_dslope γ (0 : ℝ) u

/-- Construct a nonvanishing continuous vector field with the exact boundary
point-chord direction in the open interval and actual tangent directions at
the two endpoints. Internal corners cause no difficulty. -/
theorem pointCornerLoopPointVector_continuous_nonzero {γ : ℝ → ℂ}
    (hc : ContinuousOn γ (Icc (0 : ℝ) 1)) (hclose : γ 1 = γ 0)
    (hd0 : DifferentiableAt ℝ γ 0) (hd1 : DifferentiableAt ℝ γ 1)
    (hne0 : deriv γ 0 ≠ 0) (hne1 : deriv γ 1 ≠ 0)
    (havoid : ∀ u ∈ Ioo (0 : ℝ) 1, γ u ≠ γ 0) :
    ContinuousOn (pointCornerLoopPointVector γ) (Icc (0 : ℝ) 1) ∧
      ∀ u ∈ Icc (0 : ℝ) 1, pointCornerLoopPointVector γ u ≠ 0 := by
  have hgc : ContinuousOn (dslope γ 0) (Icc (0 : ℝ) 1) := by
    intro u hu
    by_cases hu0 : u = 0
    · subst u
      exact (continuousAt_dslope_same.mpr hd0).continuousWithinAt
    exact (continuousWithinAt_dslope_of_ne hu0).mpr (hc u hu)
  have hfc : ContinuousOn (pointCornerLoopPointVector γ) (Icc (0 : ℝ) 1) := by
    intro u hu
    apply ContinuousWithinAt.neg
    by_cases hu1 : u = 1
    · subst u
      exact (continuousAt_dslope_same.mpr
        (hasDerivAt_closed_loop_dslope_one hclose hd1).differentiableAt).continuousWithinAt
    exact (continuousWithinAt_dslope_of_ne hu1).mpr (hgc u hu)
  refine ⟨hfc, ?_⟩
  intro u hu
  by_cases hu0 : u = 0
  · subst u
    rw [(pointCornerLoopPointVector_endpoints hclose hd1).1]
    exact hne0
  by_cases hu1 : u = 1
  · subst u
    rw [(pointCornerLoopPointVector_endpoints hclose hd1).2]
    exact neg_ne_zero.mpr hne1
  intro hzero
  have hf := pointCornerLoopPointVector_factor hclose u
  rw [hzero, smul_zero] at hf
  exact havoid u ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), lt_of_le_of_ne hu.2 hu1⟩
    (sub_eq_zero.mp hf.symm)

/-- Construct the endpoint-extended argument lift itself, rather than
assuming that the argument of the vanishing chord extends continuously. -/
theorem exists_corner_loop_point_argument_lift {γ : ℝ → ℂ}
    (hc : ContinuousOn γ (Icc (0 : ℝ) 1)) (hclose : γ 1 = γ 0)
    (hd0 : DifferentiableAt ℝ γ 0) (hd1 : DifferentiableAt ℝ γ 1)
    (hne0 : deriv γ 0 ≠ 0) (hne1 : deriv γ 1 ≠ 0)
    (havoid : ∀ u ∈ Ioo (0 : ℝ) 1, γ u ≠ γ 0) :
    ∃ ψ : Icc (0 : ℝ) 1 → ℝ, Continuous ψ ∧
      (∀ u : Icc (0 : ℝ) 1, u.1 ∈ Ioo (0 : ℝ) 1 →
        Complex.exp ((ψ u : ℂ) * Complex.I) = (γ u - γ 0) / (‖γ u - γ 0‖ : ℂ)) ∧
      Complex.exp ((ψ 0 : ℂ) * Complex.I) = deriv γ 0 / (‖deriv γ 0‖ : ℂ) ∧
      Complex.exp ((ψ 1 : ℂ) * Complex.I) = -deriv γ 1 / (‖-deriv γ 1‖ : ℂ) := by
  obtain ⟨hvc, hvne⟩ := pointCornerLoopPointVector_continuous_nonzero
    hc hclose hd0 hd1 hne0 hne1 havoid
  obtain ⟨ψ, hψ, hlift⟩ := exists_interval_euclidean_angle_lift
    hvc.domRestrict (fun u => hvne u u.2)
  simp only [Set.domRestrict_apply] at hlift
  refine ⟨ψ, hψ, ?_, ?_, ?_⟩
  · intro u hu
    rw [hlift]
    have hdir := euclideanDirection_smul_pos (hvne u u.2) (mul_pos hu.1 (sub_pos.mpr hu.2))
    have he := congrArg (fun z : Circle => (z : ℂ)) hdir
    simpa only [euclideanDirection_coe, pointCornerLoopPointVector_factor hclose] using he.symm
  · simpa [(pointCornerLoopPointVector_endpoints hclose hd1).1] using hlift 0
  · simpa [(pointCornerLoopPointVector_endpoints hclose hd1).2] using hlift 1

/-- Local endpoint extensions suffice to construct the boundary-point lift
of the actual C0 interval loop. The rest of the loop need not be smooth. -/
theorem exists_corner_loop_point_argument_of_endpoint_germs
    (γ : Icc (0 : ℝ) 1 → ℂ) (hγ : Continuous γ) (hclose : γ 0 = γ 1)
    (havoid : ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 → γ t ≠ γ 0)
    {l r : ℝ} (hl : 0 < l) (hlr : l < r) (hr : r < 1)
    (L R : ℝ → ℂ) (hL : DifferentiableAt ℝ L 0) (hR : DifferentiableAt ℝ R 1)
    (hLn : deriv L 0 ≠ 0) (hRn : deriv R 1 ≠ 0)
    (hleft : ∀ t : Icc (0 : ℝ) 1, t.1 ≤ l → γ t = L t)
    (hright : ∀ t : Icc (0 : ℝ) 1, r ≤ t.1 → γ t = R t) :
    ∃ ψ : Icc (0 : ℝ) 1 → ℝ, Continuous ψ ∧
      ∀ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 →
        Complex.exp ((ψ t : ℂ) * Complex.I) = (γ t - γ 0) / (‖γ t - γ 0‖ : ℂ) := by
  let Γ := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) γ
  let f : ℝ → ℂ := fun u => if u ≤ l then L u else if r ≤ u then R u else Γ u
  have hΓ : Continuous Γ := continuous_IccExtend_iff.mpr hγ
  have hagree (t : Icc (0 : ℝ) 1) : f t = γ t := by
    dsimp [f]
    split_ifs with htL htR
    · exact (hleft t htL).symm
    · exact (hright t htR).symm
    · exact IccExtend_val _ _ t
  have hfc : ContinuousOn f (Icc (0 : ℝ) 1) := by
    apply hΓ.continuousOn.congr
    intro u hu
    exact (hagree ⟨u, hu⟩).trans (IccExtend_of_mem _ _ hu).symm
  have hleftN : f =ᶠ[𝓝 (0 : ℝ)] L := by
    filter_upwards [Iio_mem_nhds hl] with u hu
    have hul : u < l := hu
    simp only [f, if_pos hul.le]
  have hrightN : f =ᶠ[𝓝 (1 : ℝ)] R := by
    filter_upwards [Ioi_mem_nhds (hlr.trans hr), Ioi_mem_nhds hr] with u huL huR
    have hlu : l < u := huL
    have hru : r < u := huR
    simp only [f, if_neg (not_le_of_gt hlu), if_pos hru.le]
  have hfd0 : DifferentiableAt ℝ f 0 := hL.congr_of_eventuallyEq hleftN
  have hfd1 : DifferentiableAt ℝ f 1 := hR.congr_of_eventuallyEq hrightN
  have hfn0 : deriv f 0 ≠ 0 := by rw [hleftN.deriv_eq]; exact hLn
  have hfn1 : deriv f 1 ≠ 0 := by rw [hrightN.deriv_eq]; exact hRn
  have hfzero : f 0 = γ 0 := hagree 0
  have hfone : f 1 = γ 1 := hagree 1
  have hfcclose : f 1 = f 0 := hfone.trans (hclose.symm.trans hfzero.symm)
  have hfavoid (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : f u ≠ f 0 := by
    have ha := hagree ⟨u, ⟨hu.1.le, hu.2.le⟩⟩
    rw [ha, hfzero]
    exact havoid ⟨u, ⟨hu.1.le, hu.2.le⟩⟩ hu
  obtain ⟨ψ, hψ, hlift, _, _⟩ := exists_corner_loop_point_argument_lift
    hfc hfcclose hfd0 hfd1 hfn0 hfn1 hfavoid
  refine ⟨ψ, hψ, ?_⟩
  intro t ht
  simpa only [hagree t, hfzero] using hlift t ht

end RepulsiveCoulomb
