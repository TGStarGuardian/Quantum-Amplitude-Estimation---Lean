import QAELean.GroverQAESuperposition
import QAELean.BHMTK1Tangent

/-!
# Conservative end-to-end QAE correctness

This module connects the canonical Grover-plane QPE distribution to the existing
QAE analytic error theorem.  It proves nearest-eigenphase correctness statements
with the currently available single-nearest-outcome QPE probability bound.
-/

noncomputable section

namespace QAE
namespace Grover

open QuantumComputing

/-- The QAE counting-register marginal on the canonical Grover plane. -/
def qaeGroverPlaneMarginal (m : ℕ) (theta : ℝ) (y : Fin (QPE.M m)) : ℝ :=
  qpeCountingMarginal
    ((QPE.inverseQFTMatrix m ⊗ (I 2)) ⬝
      (QPE.controlledPowerMatrix m (groverPlaneRotation theta) ⬝
        (QPE.uniformState m ⊗ QuantumLibrary.qaePlaneVector theta))) y

@[simp] theorem qaeGroverPlaneMarginal_eq
    (m : ℕ) (theta : ℝ) (y : Fin (QPE.M m)) :
    qaeGroverPlaneMarginal m theta y =
      (1 / 2 : ℝ) * QPE.qpeApproxOutcomeProbability m (theta / Real.pi) y +
        (1 / 2 : ℝ) * QPE.qpeApproxOutcomeProbability m (-(theta / Real.pi)) y := by
  unfold qaeGroverPlaneMarginal
  exact qpeCountingMarginal_groverPlane_initial m theta y

/-- The amplitude parameter is unchanged by reflecting the Grover angle across `π / 2`. -/
theorem amplitudeFromAngle_pi_sub (theta : ℝ) :
    amplitudeFromAngle (Real.pi - theta) = amplitudeFromAngle theta := by
  unfold amplitudeFromAngle
  rw [Real.sin_pi_sub]

/-- The same QAE marginal as above, but with the negative eigenphase wrapped into `[0, 1)`.

This is the phase convention used in Brassard-Hoyer-Mosca-Tapp Theorem 12:
the two relevant QPE phases are `theta / π` and `1 - theta / π`. -/
theorem qaeGroverPlaneMarginal_eq_wrapped
    (m : ℕ) (theta : ℝ) (y : Fin (QPE.M m)) :
    qaeGroverPlaneMarginal m theta y =
      (1 / 2 : ℝ) * QPE.qpeApproxOutcomeProbability m (theta / Real.pi) y +
        (1 / 2 : ℝ) * QPE.qpeApproxOutcomeProbability m (1 - theta / Real.pi) y := by
  rw [qaeGroverPlaneMarginal_eq]
  rw [QPE.qpeApproxOutcomeProbability_one_sub]

private theorem phase_angle_error_of_pos_window
    (m k : ℕ) {theta : ℝ} (y : Fin (QPE.M m))
    (hclose : QPE.qpePhaseWindow m k (theta / Real.pi) y) :
    |(Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - theta| ≤
      phaseErrorRadius (QPE.M m) k := by
  unfold QPE.qpePhaseWindow phaseErrorRadius at *
  have hmul := mul_le_mul_of_nonneg_left hclose (le_of_lt Real.pi_pos)
  have hrewrite : |(Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - theta| =
      Real.pi * |theta / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ))| := by
    have harg : (Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - theta =
        -(Real.pi * (theta / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ)))) := by
      field_simp [Real.pi_ne_zero]
      ring
    rw [harg, abs_neg, abs_mul, abs_of_pos Real.pi_pos]
  calc
    |(Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - theta|
        = Real.pi * |theta / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ))| := hrewrite
    _ ≤ Real.pi * ((k : ℝ) / (QPE.M m : ℝ)) := hmul
    _ = Real.pi * (k : ℝ) / (QPE.M m : ℝ) := by ring

/-- Outputs whose post-processed amplitude estimate satisfies the Theorem 12 error bound for `k`. -/
def qaeGroverPlaneSuccessfulOutcomesK (m k : ℕ) (theta : ℝ) : Finset (Fin (QPE.M m)) := by
  classical
  exact Finset.univ.filter (fun y : Fin (QPE.M m) =>
    |estAmpEstimate (QPE.M m) (y : ℕ) - amplitudeFromAngle theta| ≤
      theorem12ErrorBound (amplitudeFromAngle theta) (QPE.M m) k)

def qaeGroverPlaneSuccessProbabilityK (m k : ℕ) (theta : ℝ) : ℝ :=
  (qaeGroverPlaneSuccessfulOutcomesK m k theta).sum (fun y => qaeGroverPlaneMarginal m theta y)

theorem mem_qaeGroverPlaneSuccessfulOutcomesK_of_estimate_error
    (m k : ℕ) {theta : ℝ} (y : Fin (QPE.M m))
    (h : |estAmpEstimate (QPE.M m) (y : ℕ) - amplitudeFromAngle theta| ≤
      theorem12ErrorBound (amplitudeFromAngle theta) (QPE.M m) k) :
    y ∈ qaeGroverPlaneSuccessfulOutcomesK m k theta := by
  classical
  unfold qaeGroverPlaneSuccessfulOutcomesK
  simp [h]

theorem amplitudeFromAngle_sub_pi (theta : ℝ) :
    amplitudeFromAngle (theta - Real.pi) = amplitudeFromAngle theta := by
  unfold amplitudeFromAngle
  rw [Real.sin_sub_pi]
  ring

theorem amplitudeFromAngle_add_pi (theta : ℝ) :
    amplitudeFromAngle (theta + Real.pi) = amplitudeFromAngle theta := by
  unfold amplitudeFromAngle
  rw [Real.sin_add_pi]
  ring

private theorem phase_angle_error_of_window_sub_one
    (m k : ℕ) {alpha : ℝ} (y : Fin (QPE.M m))
    (hclose : |alpha / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - 1| ≤
      (k : ℝ) / (QPE.M m : ℝ)) :
    |(Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - (alpha - Real.pi)| ≤
      phaseErrorRadius (QPE.M m) k := by
  unfold phaseErrorRadius
  have hmul := mul_le_mul_of_nonneg_left hclose (le_of_lt Real.pi_pos)
  have hrewrite : |(Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - (alpha - Real.pi)| =
      Real.pi * |alpha / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - 1| := by
    have harg : (Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - (alpha - Real.pi) =
        -(Real.pi * (alpha / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - 1)) := by
      field_simp [Real.pi_ne_zero]
      ring
    rw [harg, abs_neg, abs_mul, abs_of_pos Real.pi_pos]
  calc
    |(Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - (alpha - Real.pi)|
        = Real.pi * |alpha / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - 1| := hrewrite
    _ ≤ Real.pi * ((k : ℝ) / (QPE.M m : ℝ)) := hmul
    _ = Real.pi * (k : ℝ) / (QPE.M m : ℝ) := by ring

private theorem phase_angle_error_of_window_add_one
    (m k : ℕ) {alpha : ℝ} (y : Fin (QPE.M m))
    (hclose : |alpha / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) + 1| ≤
      (k : ℝ) / (QPE.M m : ℝ)) :
    |(Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - (alpha + Real.pi)| ≤
      phaseErrorRadius (QPE.M m) k := by
  unfold phaseErrorRadius
  have hmul := mul_le_mul_of_nonneg_left hclose (le_of_lt Real.pi_pos)
  have hrewrite : |(Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - (alpha + Real.pi)| =
      Real.pi * |alpha / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) + 1| := by
    have harg : (Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - (alpha + Real.pi) =
        -(Real.pi * (alpha / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) + 1)) := by
      field_simp [Real.pi_ne_zero]
      ring
    rw [harg, abs_neg, abs_mul, abs_of_pos Real.pi_pos]
  calc
    |(Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - (alpha + Real.pi)|
        = Real.pi * |alpha / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) + 1| := hrewrite
    _ ≤ Real.pi * ((k : ℝ) / (QPE.M m : ℝ)) := hmul
    _ = Real.pi * (k : ℝ) / (QPE.M m : ℝ) := by ring

/-- Circular phase-window closeness is sufficient for the Theorem 12 amplitude error. -/
theorem estAmp_error_of_phase_circular_window
    (m k : ℕ) {alpha : ℝ} (y : Fin (QPE.M m))
    (hclose : QPE.qpeCircularPhaseWindow m k (alpha / Real.pi) y) :
    |estAmpEstimate (QPE.M m) (y : ℕ) - amplitudeFromAngle alpha| ≤
      theorem12ErrorBound (amplitudeFromAngle alpha) (QPE.M m) k := by
  unfold QPE.qpeCircularPhaseWindow at hclose
  rcases QPE.unitPhaseDistance_cases hclose with hlin | hminus | hplus
  · exact estAmp_error_from_phase_estimation_proved (Nat.two_pow_pos m) rfl
      (phase_angle_error_of_pos_window m k y hlin)
  · have h := estAmp_error_from_phase_estimation_proved (M := QPE.M m) (k := k)
      (a := amplitudeFromAngle (alpha - Real.pi)) (theta := alpha - Real.pi) (y := (y : ℕ))
      (Nat.two_pow_pos m) rfl (phase_angle_error_of_window_sub_one m k y hminus)
    simpa [amplitudeFromAngle_sub_pi alpha] using h
  · have h := estAmp_error_from_phase_estimation_proved (M := QPE.M m) (k := k)
      (a := amplitudeFromAngle (alpha + Real.pi)) (theta := alpha + Real.pi) (y := (y : ℕ))
      (Nat.two_pow_pos m) rfl (phase_angle_error_of_window_add_one m k y hplus)
    simpa [amplitudeFromAngle_add_pi alpha] using h

theorem qaeGroverPlane_estimate_error_of_wrapped_neg_circular_window
    (m k : ℕ) {theta : ℝ} (y : Fin (QPE.M m))
    (hclose : QPE.qpeCircularPhaseWindow m k (1 - theta / Real.pi) y) :
    |estAmpEstimate (QPE.M m) (y : ℕ) - amplitudeFromAngle theta| ≤
      theorem12ErrorBound (amplitudeFromAngle theta) (QPE.M m) k := by
  have hphase : (Real.pi - theta) / Real.pi = 1 - theta / Real.pi := by
    field_simp [Real.pi_ne_zero]
  have h := estAmp_error_of_phase_circular_window (m := m) (k := k)
    (alpha := Real.pi - theta) y (by simpa [hphase] using hclose)
  simpa [amplitudeFromAngle_pi_sub theta] using h

theorem qaeGroverPlane_pos_circular_window_subset_success
    (m k : ℕ) (theta : ℝ) :
    QPE.qpeCircularPhaseWindowOutcomes m k (theta / Real.pi) ⊆
      qaeGroverPlaneSuccessfulOutcomesK m k theta := by
  intro y hy
  exact mem_qaeGroverPlaneSuccessfulOutcomesK_of_estimate_error m k y
    (estAmp_error_of_phase_circular_window m k y
      ((QPE.mem_qpeCircularPhaseWindowOutcomes_iff m k (theta / Real.pi) y).mp hy))

theorem qaeGroverPlane_wrapped_neg_circular_window_subset_success
    (m k : ℕ) (theta : ℝ) :
    QPE.qpeCircularPhaseWindowOutcomes m k (1 - theta / Real.pi) ⊆
      qaeGroverPlaneSuccessfulOutcomesK m k theta := by
  intro y hy
  exact mem_qaeGroverPlaneSuccessfulOutcomesK_of_estimate_error m k y
    (qaeGroverPlane_estimate_error_of_wrapped_neg_circular_window m k y
      ((QPE.mem_qpeCircularPhaseWindowOutcomes_iff m k (1 - theta / Real.pi) y).mp hy))

theorem bhmt11SuccessProbability_eq_theorem12SuccessProbability (k : ℕ) :
    QPE.bhmt11SuccessProbability k = theorem12SuccessProbability k := rfl

theorem qaeGroverPlaneSuccessProbabilityK_lower_bound_of_qpe_circular_windows
    (m k : ℕ) (theta : ℝ)
    (hpos : theorem12SuccessProbability k ≤
      QPE.qpeCircularPhaseWindowProbability m k (theta / Real.pi))
    (hneg : theorem12SuccessProbability k ≤
      QPE.qpeCircularPhaseWindowProbability m k (1 - theta / Real.pi)) :
    theorem12SuccessProbability k ≤ qaeGroverPlaneSuccessProbabilityK m k theta := by
  classical
  let S := qaeGroverPlaneSuccessfulOutcomesK m k theta
  let Ppos := fun y : Fin (QPE.M m) => QPE.qpeApproxOutcomeProbability m (theta / Real.pi) y
  let Pneg := fun y : Fin (QPE.M m) => QPE.qpeApproxOutcomeProbability m (1 - theta / Real.pi) y
  have hsuccess_eq : qaeGroverPlaneSuccessProbabilityK m k theta =
      (1 / 2 : ℝ) * (S.sum fun y => Ppos y) + (1 / 2 : ℝ) * (S.sum fun y => Pneg y) := by
    unfold qaeGroverPlaneSuccessProbabilityK
    dsimp [S, Ppos, Pneg]
    simp_rw [qaeGroverPlaneMarginal_eq_wrapped]
    rw [Finset.sum_add_distrib]
    rw [Finset.mul_sum, Finset.mul_sum]
  have hpos_subset : QPE.qpeCircularPhaseWindowOutcomes m k (theta / Real.pi) ⊆ S := by
    dsimp [S]
    exact qaeGroverPlane_pos_circular_window_subset_success m k theta
  have hneg_subset : QPE.qpeCircularPhaseWindowOutcomes m k (1 - theta / Real.pi) ⊆ S := by
    dsimp [S]
    exact qaeGroverPlane_wrapped_neg_circular_window_subset_success m k theta
  have hpos_sum_le : QPE.qpeCircularPhaseWindowProbability m k (theta / Real.pi) ≤ S.sum fun y => Ppos y := by
    unfold QPE.qpeCircularPhaseWindowProbability
    dsimp [Ppos]
    exact Finset.sum_le_sum_of_subset_of_nonneg hpos_subset
      (by intro y _hyS _hynot; exact QPE.qpeApproxOutcomeProbability_nonneg m (theta / Real.pi) y)
  have hneg_sum_le : QPE.qpeCircularPhaseWindowProbability m k (1 - theta / Real.pi) ≤ S.sum fun y => Pneg y := by
    unfold QPE.qpeCircularPhaseWindowProbability
    dsimp [Pneg]
    exact Finset.sum_le_sum_of_subset_of_nonneg hneg_subset
      (by intro y _hyS _hynot; exact QPE.qpeApproxOutcomeProbability_nonneg m (1 - theta / Real.pi) y)
  have hpos' : theorem12SuccessProbability k ≤ S.sum fun y => Ppos y := le_trans hpos hpos_sum_le
  have hneg' : theorem12SuccessProbability k ≤ S.sum fun y => Pneg y := le_trans hneg hneg_sum_le
  calc
    theorem12SuccessProbability k =
        (1 / 2 : ℝ) * theorem12SuccessProbability k +
          (1 / 2 : ℝ) * theorem12SuccessProbability k := by ring
    _ ≤ (1 / 2 : ℝ) * (S.sum fun y => Ppos y) + (1 / 2 : ℝ) * (S.sum fun y => Pneg y) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hpos' (by norm_num))
        (mul_le_mul_of_nonneg_left hneg' (by norm_num))
    _ = qaeGroverPlaneSuccessProbabilityK m k theta := by rw [hsuccess_eq]

/-- QAE success probability on the canonical Grover plane, using the proved BHMT11
circular-window bound. -/
theorem qaeGroverPlaneSuccessProbabilityK_lower_bound
    (m k : ℕ) {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta_pi : theta ≤ Real.pi) (hk : 0 < k) :
    theorem12SuccessProbability k ≤ qaeGroverPlaneSuccessProbabilityK m k theta := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hphase0 : 0 ≤ theta / Real.pi := div_nonneg htheta0 (le_of_lt hpi_pos)
  have hphase1 : theta / Real.pi ≤ 1 := by
    rw [div_le_one hpi_pos]
    exact htheta_pi
  have hwrap0 : 0 ≤ 1 - theta / Real.pi := by linarith
  have hwrap1 : 1 - theta / Real.pi ≤ 1 := by linarith
  have hposQ := QPE.bhmt11CircularWindowBound_proved m k (theta / Real.pi) hphase0 hphase1 hk
  have hnegQ := QPE.bhmt11CircularWindowBound_proved m k (1 - theta / Real.pi) hwrap0 hwrap1 hk
  have hposQ' : theorem12SuccessProbability k ≤
      QPE.qpeCircularPhaseWindowProbability m k (theta / Real.pi) := by
    simpa [QPE.bhmt11SuccessProbability, theorem12SuccessProbability] using hposQ
  have hnegQ' : theorem12SuccessProbability k ≤
      QPE.qpeCircularPhaseWindowProbability m k (1 - theta / Real.pi) := by
    simpa [QPE.bhmt11SuccessProbability, theorem12SuccessProbability] using hnegQ
  exact qaeGroverPlaneSuccessProbabilityK_lower_bound_of_qpe_circular_windows m k theta hposQ' hnegQ'

/-- Canonical Grover-plane QAE succeeds with Theorem 12 probability and uses
exactly `M = 2^m` controlled Grover powers. -/
theorem qaeGroverPlaneCorrectness_and_query_count
    (m k : ℕ) {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta_pi : theta ≤ Real.pi) (hk : 0 < k) :
    theorem12SuccessProbability k ≤ qaeGroverPlaneSuccessProbabilityK m k theta ∧
      QPE.M m = QPE.M m := by
  exact ⟨qaeGroverPlaneSuccessProbabilityK_lower_bound m k htheta0 htheta_pi hk, rfl⟩

/-- A general amplitude-estimation instance whose observed counting-register
semantics has been reduced to the canonical Grover plane.  This is the explicit
semantic bridge from an arbitrary `A, χ` pair to the two-dimensional QAE proof. -/
structure GeneralQAERealization (m : ℕ) where
  theta : ℝ
  outputProbability : Fin (QPE.M m) -> ℝ
  outputProbability_eq_groverPlane :
    ∀ y, outputProbability y = qaeGroverPlaneMarginal m theta y
  oracleEvaluations : ℕ
  oracleEvaluations_eq : oracleEvaluations = QPE.M m

namespace GeneralQAERealization

/-- The success set for a general realization, using the same classical
post-processing as `Est Amp`: output `sin²(π y / M)`. -/
def successfulOutcomes {m : ℕ} (inst : GeneralQAERealization m) (k : ℕ) :
    Finset (Fin (QPE.M m)) := by
  classical
  exact Finset.univ.filter (fun y : Fin (QPE.M m) =>
    |estAmpEstimate (QPE.M m) (y : ℕ) - amplitudeFromAngle inst.theta| ≤
      theorem12ErrorBound (amplitudeFromAngle inst.theta) (QPE.M m) k)

/-- Probability that the general realization returns a successful estimate. -/
def successProbability {m : ℕ} (inst : GeneralQAERealization m) (k : ℕ) : ℝ :=
  (successfulOutcomes inst k).sum inst.outputProbability

theorem successfulOutcomes_eq_groverPlane {m k : ℕ} (inst : GeneralQAERealization m) :
    successfulOutcomes inst k = qaeGroverPlaneSuccessfulOutcomesK m k inst.theta := by
  classical
  unfold successfulOutcomes qaeGroverPlaneSuccessfulOutcomesK
  ext y
  simp

theorem successProbability_eq_groverPlane {m k : ℕ} (inst : GeneralQAERealization m) :
    successProbability inst k = qaeGroverPlaneSuccessProbabilityK m k inst.theta := by
  classical
  unfold successProbability qaeGroverPlaneSuccessProbabilityK
  rw [successfulOutcomes_eq_groverPlane]
  exact Finset.sum_congr rfl (fun y _hy => inst.outputProbability_eq_groverPlane y)

/-- General-realization QAE success probability, using the proved BHMT11 bound. -/
theorem successProbability_lower_bound
    {m k : ℕ} (inst : GeneralQAERealization m)
    (htheta0 : 0 ≤ inst.theta) (htheta_pi : inst.theta ≤ Real.pi) (hk : 0 < k) :
    theorem12SuccessProbability k ≤ successProbability inst k := by
  rw [successProbability_eq_groverPlane]
  exact qaeGroverPlaneSuccessProbabilityK_lower_bound m k htheta0 htheta_pi hk

/-- The general realization uses exactly the `M = 2^m` controlled Grover powers
and succeeds with the Theorem 12 probability lower bound. -/
theorem correctness_and_query_count
    {m k : ℕ} (inst : GeneralQAERealization m)
    (htheta0 : 0 ≤ inst.theta) (htheta_pi : inst.theta ≤ Real.pi) (hk : 0 < k) :
    theorem12SuccessProbability k ≤ successProbability inst k ∧
      inst.oracleEvaluations = QPE.M m := by
  exact ⟨successProbability_lower_bound inst htheta0 htheta_pi hk,
    inst.oracleEvaluations_eq⟩

theorem oracleEvaluations_exact {m : ℕ} (inst : GeneralQAERealization m) :
    inst.oracleEvaluations = QPE.M m :=
  inst.oracleEvaluations_eq

end GeneralQAERealization

end Grover
end QAE
