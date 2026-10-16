import LeanResearch.RepulsiveCoulomb.PaperRoute.LogSmoothConvolution
import LeanResearch.RepulsiveCoulomb.PointConformalDensity

/-!
# Finite-point distributional curvature

Additive source; validation status is recorded in separate evidence.
The weighted geometry endpoint does not yet select this identity.
No existing geometry proof is claimed to use this identity.

Target: the unlabelled display at canonical.tex lines 409--412,
  -Delta log(rho) = -pi * sum_j a_j delta_(y_j), rho = sqrt(rawPointWeight a y).

Only the sealed planar fundamental solution and its sealed reflected-Laplacian
calculus helper are reused. Translation, genuine local/test-product
integrability, the actual finite sum, and a.e. identification with the literal
logarithm of rho are made explicit below. The equality is stated on every
compactly supported C2 real test function with the physical real Laplacian.
The finite logarithmic-sum pairing allows arbitrary real coefficients; only the
literal density identification needs the original nonnegative exponents.
Empty families, zero coefficients, and coincident sites require no exclusions.

This proves the exact test identity, not a SignedMeasure/Distribution equality
with the existing cone-angle measure. Such packaging and a consumer that makes
it load-bearing in the geometry route remain separate verification tasks.
-/

noncomputable section
open MeasureTheory Real Set Filter InnerProductSpace
open scoped Topology ContDiff BigOperators

namespace RepulsiveCoulomb.PaperRoute.PointCurvature

/-- The actual translated logarithmic kernel is locally integrable, including
at its source point. Its chosen finite value at that point is immaterial. -/
theorem translated_negative_log_locallyIntegrable (y : ℂ) :
    LocallyIntegrable (fun x : ℂ => -Real.log ‖x - y‖) volume := by
  have hp : Integrable (fun x : ℂ => max (-Real.log ‖x - y‖) 0) := by
    apply (logPositive_integrable.comp_sub_left y).congr
    filter_upwards with x
    rw [norm_sub_rev]
  have hc : Continuous (fun x : ℂ => Real.log (max 1 ‖x - y‖)) :=
    (continuous_const.max (continuous_id.sub continuous_const).norm).log
      (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
  have he : (fun x : ℂ => -Real.log ‖x - y‖) =
      (fun x : ℂ => max (-Real.log ‖x - y‖) 0) -
        (fun x : ℂ => Real.log (max 1 ‖x - y‖)) := by
    funext x
    exact planarLogKernel_split (x - y)
  rw [he]
  exact hp.locallyIntegrable.sub hc.locallyIntegrable

/-- Translation of the sealed fundamental solution, with actual product
integrability. Reflection is used only as a volume-preserving change of
variables; both signs in the second derivative cancel. -/
theorem translated_negative_log_pairing {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (y : ℂ) :
    Integrable (fun x : ℂ => (-Real.log ‖x - y‖) * Laplacian.laplacian φ x) ∧
      (∫ x : ℂ, (-Real.log ‖x - y‖) * Laplacian.laplacian φ x) =
        (-2 * Real.pi) * φ y := by
  have ht : ContDiff ℝ 2 (fun z : ℂ => φ (y - z)) :=
    hφ.comp (contDiff_const.sub contDiff_id)
  have htc : HasCompactSupport (fun z : ℂ => φ (y - z)) :=
    hφc.comp_homeomorph (Homeomorph.subLeft y)
  obtain ⟨hti, hte⟩ := log_fundamental_solution ht htc
  have hrow : Integrable
      (fun x : ℂ => (-Real.log ‖x - y‖) * Laplacian.laplacian φ x) := by
    apply (hti.comp_sub_left y).congr
    filter_upwards with x
    rw [laplacian_comp_sub_left hφ, sub_sub_self]
    simp only [norm_sub_rev]
  have he : (∫ z : ℂ, (-Real.log ‖z‖) * Laplacian.laplacian φ (y - z)) =
      ∫ x : ℂ, (-Real.log ‖x - y‖) * Laplacian.laplacian φ x := by
    calc
      (∫ z : ℂ, (-Real.log ‖z‖) * Laplacian.laplacian φ (y - z)) =
          ∫ z : ℂ, (-Real.log ‖(y - z) - y‖) * Laplacian.laplacian φ (y - z) := by
        apply integral_congr_ae
        filter_upwards with z
        have hz : (y - z) - y = -z := by abel
        simp only [hz, norm_neg]
      _ = _ := integral_sub_left_eq_self
        (fun x : ℂ => (-Real.log ‖x - y‖) * Laplacian.laplacian φ x) volume y
  refine ⟨hrow, ?_⟩
  have hte' : (∫ z : ℂ, (-Real.log ‖z‖) * Laplacian.laplacian φ (y - z)) =
      (-2 * Real.pi) * φ y := by
    simpa only [laplacian_comp_sub_left hφ, sub_zero] using hte
  exact he.symm.trans hte'

/-- Genuine local integrability of the existing finite logarithmic sum.
No sign, separation, cardinality-lower-bound, or positive-mass assumption. -/
theorem pointConformalLog_locallyIntegrable {m : ℕ}
    (a : Fin m → ℝ) (y : Fin m → ℂ) :
    LocallyIntegrable (pointConformalLog a y) volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hi (j : Fin m) : IntegrableOn (fun x : ℂ => Real.log ‖x - y j‖) K := by
    have hn := (translated_negative_log_locallyIntegrable (y j)).neg.integrableOn_isCompact hK
    change IntegrableOn (fun x : ℂ => -(-Real.log ‖x - y j‖)) K at hn
    simpa only [neg_neg] using hn
  have hs : IntegrableOn (fun x : ℂ => ∑ j, a j * Real.log ‖x - y j‖) K :=
    integrable_finsetSum _ (fun j _ => (hi j).const_mul (a j))
  exact hs.const_mul (1 / 2 : ℝ)

/-- The finite-sum version of the exact curvature display. The minus sign on
the left is the distributional minus Laplacian, and (1/2)*(-2*pi)=-pi. -/
theorem negative_pointConformalLog_pairing {m : ℕ}
    (a : Fin m → ℝ) (y : Fin m → ℂ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x : ℂ => (-pointConformalLog a y x) * Laplacian.laplacian φ x) ∧
      (∫ x : ℂ, (-pointConformalLog a y x) * Laplacian.laplacian φ x) =
        -Real.pi * ∑ j, a j * φ (y j) := by
  have hi (j : Fin m) : Integrable
      (fun x : ℂ => (a j / 2) * ((-Real.log ‖x - y j‖) * Laplacian.laplacian φ x)) :=
    (translated_negative_log_pairing hφ hφc (y j)).1.const_mul (a j / 2)
  have he : (fun x : ℂ => (-pointConformalLog a y x) * Laplacian.laplacian φ x) =
      (fun x : ℂ => ∑ j, (a j / 2) *
        ((-Real.log ‖x - y j‖) * Laplacian.laplacian φ x)) := by
    funext x
    calc
      (-pointConformalLog a y x) * Laplacian.laplacian φ x =
          ((-1 / 2 : ℝ) * ∑ j, a j * Real.log ‖x - y j‖) *
            Laplacian.laplacian φ x := by
        unfold pointConformalLog
        ring
      _ = ∑ j, ((-1 / 2 : ℝ) * (a j * Real.log ‖x - y j‖)) *
          Laplacian.laplacian φ x := by
        rw [Finset.mul_sum, Finset.sum_mul]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
  refine ⟨?_, ?_⟩
  · rw [he]
    exact integrable_finsetSum _ (fun j _ => hi j)
  · rw [he, integral_finsetSum Finset.univ (fun j _ => hi j)]
    calc
      (∑ j, ∫ x : ℂ, (a j / 2) *
          ((-Real.log ‖x - y j‖) * Laplacian.laplacian φ x)) =
          ∑ j, (a j / 2) * ((-2 * Real.pi) * φ (y j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [integral_const_mul, (translated_negative_log_pairing hφ hφc (y j)).2]
      _ = -Real.pi * ∑ j, a j * φ (y j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring

/-- The logarithm of the literal conformal density agrees a.e. with the
existing finite logarithmic sum. Repeated sites and zero exponents are allowed;
only the finite site set is discarded, and it has zero planar volume. -/
theorem log_pointConformalDensity_ae {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    (fun x : ℂ => Real.log (pointConformalDensity a y x)) =ᵐ[volume]
      pointConformalLog a y := by
  have hsites : ∀ᵐ x : ℂ, ∀ j : Fin m, x ≠ y j :=
    ae_all_iff.mpr (fun j => volume.ae_ne (y j))
  filter_upwards [hsites] with x hx
  have hxp : x ∉ pointPunctures a y := by
    rintro ⟨j, hj, he⟩
    exact hx j he
  rw [← exp_pointConformalLog ha y hxp, Real.log_exp]

/-- The literal logarithmic density, not merely a formal sum, is locally
integrable and therefore defines its usual distribution. -/
theorem log_pointConformalDensity_locallyIntegrable {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    LocallyIntegrable (fun x : ℂ => Real.log (pointConformalDensity a y x)) volume :=
  (pointConformalLog_locallyIntegrable a y).congr (log_pointConformalDensity_ae ha y).symm

/-- Exact compact-C2 test identity for the original manuscript's
`-Delta log(rho) = -pi sum_j a_j delta_(y_j)` with literal rho.
The integral has actual integrability; no totalized nonintegrable integral is used. -/
theorem negative_log_pointConformalDensity_pairing {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x : ℂ => (-Real.log (pointConformalDensity a y x)) *
      Laplacian.laplacian φ x) ∧
      (∫ x : ℂ, (-Real.log (pointConformalDensity a y x)) * Laplacian.laplacian φ x) =
        -Real.pi * ∑ j, a j * φ (y j) := by
  have he : (fun x : ℂ => (-Real.log (pointConformalDensity a y x)) *
      Laplacian.laplacian φ x) =ᵐ[volume]
      (fun x : ℂ => (-pointConformalLog a y x) * Laplacian.laplacian φ x) := by
    filter_upwards [log_pointConformalDensity_ae ha y] with x hx
    rw [hx]
  obtain ⟨hi, hv⟩ := negative_pointConformalLog_pairing a y hφ hφc
  exact ⟨hi.congr he.symm, (integral_congr_ae he).trans hv⟩

/-- Conventional distributional notation: minus the pairing of log(rho) with
the physical Laplacian of the test function has the exact negative pi atoms. -/
theorem pointConformalDensity_distributional_curvature {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x : ℂ => Real.log (pointConformalDensity a y x) *
      Laplacian.laplacian φ x) ∧
      -(∫ x : ℂ, Real.log (pointConformalDensity a y x) * Laplacian.laplacian φ x) =
        -Real.pi * ∑ j, a j * φ (y j) := by
  obtain ⟨hi, hv⟩ := negative_log_pointConformalDensity_pairing ha y hφ hφc
  refine ⟨?_, ?_⟩
  · have hn := hi.neg
    change Integrable (fun x : ℂ => -((-Real.log (pointConformalDensity a y x)) *
      Laplacian.laplacian φ x)) at hn
    simpa only [neg_mul, neg_neg] using hn
  · simpa only [neg_mul, integral_neg] using hv

end RepulsiveCoulomb.PaperRoute.PointCurvature
