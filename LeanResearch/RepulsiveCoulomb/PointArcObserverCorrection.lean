import LeanResearch.RepulsiveCoulomb.JordanArgumentHomotopy

/-! A moving observer near a point avoided by a compact actual arc has a
single, constructed principal correction to every argument lift. This gives
the uniform branch and endpoint-increment limit needed when a boundary atom
is approached from the actual outside Jordan region. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

def pointArcObserverArgument {X : Type*} (γ : X → ℂ) (ψ : X → ℝ)
    (p w : ℂ) (t : X) : ℝ := ψ t + Complex.arg ((γ t - w) / (γ t - p))

/-- Compact avoidance constructs one observer disk valid for the whole arc,
not separate neighborhoods that might depend on the arc parameter. -/
theorem exists_uniform_arc_observer_slit_disk {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (γ : X → ℂ) (hγ : Continuous γ)
    (p : ℂ) (hp : ∀ t, γ t ≠ p) :
    ∃ R : ℝ, 0 < R ∧ ∀ w ∈ ball p R, ∀ t,
      γ t ≠ w ∧ 0 < ((γ t - w) / (γ t - p)).re := by
  have hpc : p ∈ (range γ)ᶜ := by rintro ⟨t, ht⟩; exact hp t ht
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp
    ((isCompact_range hγ).isClosed.isOpen_compl.mem_nhds hpc)
  have hmin (t : X) : R ≤ ‖γ t - p‖ := by
    by_contra hn
    have hm : γ t ∈ ball p R := by
      rw [mem_ball, dist_eq_norm]
      exact lt_of_not_ge hn
    exact hball hm (mem_range_self t)
  refine ⟨R, hR, ?_⟩
  intro w hw t
  have hwp : ‖p - w‖ < R := by simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hw
  have hden : γ t - p ≠ 0 := sub_ne_zero.mpr (hp t)
  have hnorm : ‖(p - w) / (γ t - p)‖ < 1 := by
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hden)).mpr (hwp.trans_le (hmin t))
  have hratio : (γ t - w) / (γ t - p) = 1 + (p - w) / (γ t - p) := by
    field_simp [hden]
    ring
  have hre : 0 < ((γ t - w) / (γ t - p)).re := by
    rw [hratio, Complex.add_re, Complex.one_re]
    have h := (abs_le.mp (Complex.abs_re_le_norm ((p - w) / (γ t - p)))).1
    linarith
  refine ⟨?_, hre⟩
  intro heq
  rw [heq, sub_self, zero_div, Complex.zero_re] at hre
  exact (lt_irrefl 0) hre

/-- The small-observer branch is an actual continuous argument lift of the
shifted physical chord. Its phase correction is the literal chord ratio. -/
theorem pointArcObserverArgument_continuous_lift {X : Type*}
    [TopologicalSpace X] {γ : X → ℂ} (hγ : Continuous γ)
    {ψ : X → ℝ} (hψ : Continuous ψ) {p w : ℂ}
    (hp : ∀ t, γ t ≠ p) (hw : ∀ t, γ t ≠ w)
    (hre : ∀ t, 0 < ((γ t - w) / (γ t - p)).re)
    (hψlift : ∀ t, Complex.exp ((ψ t : ℂ) * Complex.I) =
      (γ t - p) / (‖γ t - p‖ : ℂ)) :
    Continuous (pointArcObserverArgument γ ψ p w) ∧
      ∀ t, Complex.exp ((pointArcObserverArgument γ ψ p w t : ℂ) * Complex.I) =
        (γ t - w) / (‖γ t - w‖ : ℂ) := by
  have hratio : Continuous (fun t => (γ t - w) / (γ t - p)) :=
    (hγ.sub continuous_const).div (hγ.sub continuous_const) (fun t => sub_ne_zero.mpr (hp t))
  have hc : Continuous (fun t => Complex.arg ((γ t - w) / (γ t - p))) :=
    Complex.continuousOn_arg.comp_continuous hratio (fun t => Or.inl (hre t))
  refine ⟨hψ.add hc, ?_⟩
  intro t
  have hdir : Circle.exp (ψ t) = euclideanDirection (γ t - p) (sub_ne_zero.mpr (hp t)) :=
    Circle.ext (hψlift t)
  have he : Circle.exp (pointArcObserverArgument γ ψ p w t) =
      euclideanDirection (γ t - w) (sub_ne_zero.mpr (hw t)) := by
    rw [pointArcObserverArgument, Circle.exp_add, hdir,
      circle_exp_arg_vector_ratio _ _ (sub_ne_zero.mpr (hw t)) (sub_ne_zero.mpr (hp t))]
    rw [mul_comm, div_mul_cancel]
  exact congrArg (fun z : Circle => (z : ℂ)) he

/-- The actual corrected endpoint increment converges to the original arc
increment as the observer tends to the avoided point. -/
theorem pointArcObserverArgument_increment_tendsto {X : Type*}
    (γ : X → ℂ) (ψ : X → ℝ) {p : ℂ} (a b : X)
    (ha : γ a ≠ p) (hb : γ b ≠ p) :
    Tendsto (fun w : ℂ => pointArcObserverArgument γ ψ p w b -
      pointArcObserverArgument γ ψ p w a) (𝓝 p) (𝓝 (ψ b - ψ a)) := by
  have hc (t : X) (ht : γ t ≠ p) :
      ContinuousAt (fun w : ℂ => Complex.arg ((γ t - w) / (γ t - p))) p := by
    have hslit : (γ t - p) / (γ t - p) ∈ Complex.slitPlane := by
      rw [div_self (sub_ne_zero.mpr ht)]
      simp
    exact (Complex.continuousAt_arg hslit).comp
      (f := fun w : ℂ => (γ t - w) / (γ t - p))
      ((continuous_const.sub continuous_id).continuousAt.div_const _)
  have hcont : ContinuousAt (fun w : ℂ => pointArcObserverArgument γ ψ p w b -
      pointArcObserverArgument γ ψ p w a) p :=
    (continuousAt_const.add (hc b hb)).sub (continuousAt_const.add (hc a ha))
  have hlim := hcont.tendsto
  simpa only [pointArcObserverArgument, div_self (sub_ne_zero.mpr ha),
    div_self (sub_ne_zero.mpr hb), Complex.arg_one, add_zero] using hlim

end RepulsiveCoulomb
