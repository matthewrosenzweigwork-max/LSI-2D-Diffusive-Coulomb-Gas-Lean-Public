import LeanResearch.RepulsiveCoulomb.DbarBranchCompactMargin

/-! A genuine local weak system with compactly supported L2 values extends
to the global compact-coefficient system by one proper cutoff. The same
coefficient extension agrees with all original coefficients and derivatives
near the support, rather than imposing independent component derivatives. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

def coulombRealKernelLocalize {N : ℕ}
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤)
    {R : ℝ} (hR : 0 < R) : TestFunction (coulombDomain N) ℝ ⊤ :=
  ⟨fun z => φ z * coulombMetricCutoff R z,
    φ.contDiff.mul (coulombMetricCutoff_contDiff hR),
    (coulombMetricCutoff_hasCompactSupport hR).mul_left,
    tsupport_mul_subset_right.trans (coulombMetricCutoffTest (N := N) hR).tsupport_subset⟩

theorem coulombRealKernelLocalize_eventuallyEq {N : ℕ}
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤)
    {R : ℝ} (hR : 0 < R) {z : CoulombConfig N}
    (hz : z ∈ coulombGraphRadiusSublevel N R) :
    (coulombRealKernelLocalize φ hR : CoulombConfig N → ℝ) =ᶠ[𝓝 z] φ := by
  filter_upwards [(coulombGraphRadiusSublevel_isOpen N R).mem_nhds hz] with w hw
  change φ w * coulombMetricCutoff R w = φ w
  rw [coulombMetricCutoff_eq_one hR hw.1 hw.2.le, mul_one]

def DbarLocalWeakSystem {N : ℕ} {ι κ δ : Type*} [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → CoulombConfig N → ℂ) (B : κ → ι → CoulombConfig N → ℂ)
    (v : δ → CoulombConfig N) (u : ι → CoulombConfig N → ℂ) (g : κ → CoulombConfig N → ℂ) : Prop :=
  ∀ a (φ : TestFunction (coulombDomain N) ℝ ⊤), (∫ x, φ x • g a x) =
    -(∑ b, ∑ d, ∫ x, ((fderiv ℝ (φ : CoulombConfig N → ℝ) x (v d)) • A a b d x +
      φ x • fderiv ℝ (A a b d) x (v d)) * u b x) +
      ∑ b, ∫ x, φ x • (B a b x * u b x)

theorem dbarLocalWeakSystem_compact_extension {N : ℕ} {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (A : κ → ι → δ → CoulombConfig N → ℂ) (B : κ → ι → CoulombConfig N → ℂ)
    (hA : ∀ a b d z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (A a b d) z)
    (hB : ∀ a b z, z ∈ coulombDomain N → ContDiffAt ℝ (⊤ : ℕ∞) (B a b) z)
    (v : δ → CoulombConfig N)
    (u : ι → Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (g : κ → Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (hweak : DbarLocalWeakSystem A B v (fun b => (u b : CoulombConfig N → ℂ))
      (fun a => (g a : CoulombConfig N → ℂ)))
    {K : Set (CoulombConfig N)} {R : ℝ} (hR : 0 < R)
    (hKR : K ⊆ coulombGraphRadiusSublevel N R)
    (hu : ∀ b, ∀ᵐ x ∂volume, x ∉ K → u b x = 0)
    (hg : ∀ a, ∀ᵐ x ∂volume, x ∉ K → g a x = 0) :
    DbarVolumeWeakSystem
      (fun a b d => coulombCoefficientExtensionGlobal (A a b d) (hA a b d) hR)
      (fun a b => coulombCoefficientExtensionGlobal (B a b) (hB a b) hR) v u g := by
  intro a φ
  let φloc := coulombRealKernelLocalize φ hR
  have hval (x : CoulombConfig N) (hx : x ∈ K) : φloc x = φ x :=
    (coulombRealKernelLocalize_eventuallyEq φ hR (hKR hx)).eq_of_nhds
  have hder (x : CoulombConfig N) (hx : x ∈ K) :
      fderiv ℝ (φloc : CoulombConfig N → ℝ) x = fderiv ℝ (φ : CoulombConfig N → ℝ) x :=
    (coulombRealKernelLocalize_eventuallyEq φ hR (hKR hx)).fderiv_eq
  have hleft : (∫ x, φloc x • g a x) = ∫ x, φ x • g a x := by
    apply integral_congr_ae
    filter_upwards [hg a] with x hx
    by_cases h : x ∈ K
    · rw [hval x h]
    · rw [hx h, smul_zero, smul_zero]
  have hfirst (b : ι) (d : δ) :
      (∫ x, ((dbarRealKernelDerivative (v d) φ x) •
        coulombCoefficientExtensionGlobal (A a b d) (hA a b d) hR x +
        φ x • dbarVolumeCoreDerivative (v d)
          (coulombCoefficientExtensionGlobal (A a b d) (hA a b d) hR) x) * u b x) =
      ∫ x, ((fderiv ℝ (φloc : CoulombConfig N → ℝ) x (v d)) • A a b d x +
        φloc x • fderiv ℝ (A a b d) x (v d)) * u b x := by
    apply integral_congr_ae
    filter_upwards [hu b] with x hx
    by_cases h : x ∈ K
    · rw [dbarRealKernelDerivative_apply, dbarVolumeCoreDerivative_apply,
        hval x h, hder x h]
      change ((fderiv ℝ (φ : CoulombConfig N → ℝ) x (v d)) •
        coulombCoefficientExtension (A a b d) (hA a b d) hR x +
        φ x • fderiv ℝ (coulombCoefficientExtension (A a b d) (hA a b d) hR : CoulombConfig N → ℂ) x (v d)) * u b x = _
      rw [coulombCoefficientExtension_eq _ _ _ (hKR h),
        coulombCoefficientExtension_fderiv _ _ _ (hKR h)]
    · rw [hx h, mul_zero, mul_zero]
  have hzero (b : ι) :
      (∫ x, φ x • (coulombCoefficientExtensionGlobal (B a b) (hB a b) hR x * u b x)) =
        ∫ x, φloc x • (B a b x * u b x) := by
    apply integral_congr_ae
    filter_upwards [hu b] with x hx
    by_cases h : x ∈ K
    · rw [hval x h]
      change φ x • (coulombCoefficientExtension (B a b) (hB a b) hR x * u b x) = _
      rw [coulombCoefficientExtension_eq _ _ _ (hKR h)]
    · rw [hx h, mul_zero, mul_zero, smul_zero, smul_zero]
  simp_rw [hfirst, hzero]
  rw [← hleft]
  exact hweak a φloc

end RepulsiveCoulomb
