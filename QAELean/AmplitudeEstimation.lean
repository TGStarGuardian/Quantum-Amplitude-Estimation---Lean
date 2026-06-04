import Mathlib

/-!
# Quantum amplitude estimation

This file formalizes the parts of Brassard, Hoyer, Mosca, and Tapp,
"Quantum Amplitude Amplification and Estimation", that are essential for
quantum amplitude estimation.

The paper's QAE proof has two layers:

* the quantum layer prepares a phase-estimation sample for the Grover iterate
  `Q = -A S0 A^{-1} Sχ`;
* the analytic layer converts a phase error for `θ` into an amplitude error for
  `a = sin^2 θ`.

The declarations below keep the quantum layer abstract and formalize the
paper's contract for the analytic layer.  This makes the statement reusable
with a concrete finite-dimensional quantum library that supplies the Fourier
transform, controlled powers, and measurement distribution.
-/

noncomputable section

namespace QAE

abbrev Operator (State : Type u) := State -> State

/-- The Grover iterate used throughout the paper:
`Q(A, χ) = - A S0 A^{-1} Sχ`. -/
def groverIterate {State : Type u} [Neg State]
    (A Ainv Szero Schi : Operator State) : Operator State :=
  fun psi => - A (Szero (Ainv (Schi psi)))

/-- Minimal operator data needed before specializing to matrices or linear maps. -/
structure AmplificationData (State : Type u) [Neg State] where
  A : Operator State
  Ainv : Operator State
  Szero : Operator State
  Schi : Operator State
  zero : State

namespace AmplificationData

/-- The `Q` operator associated with the input algorithm and predicate. -/
def Q {State : Type u} [Neg State] (data : AmplificationData State) : Operator State :=
  groverIterate data.A data.Ainv data.Szero data.Schi

end AmplificationData

/-- The amplitude corresponding to the phase angle `θ`: `a = sin^2 θ`. -/
def amplitudeFromAngle (theta : ℝ) : ℝ :=
  Real.sin theta ^ 2

/-- The classical post-processing in `Est Amp(A, χ, M)`: output `sin^2(π y / M)`. -/
def estAmpEstimate (M y : ℕ) : ℝ :=
  amplitudeFromAngle (Real.pi * (y : ℝ) / (M : ℝ))

/-- The phase radius `π k / M` used in the proof of Theorem 12. -/
def phaseErrorRadius (M k : ℕ) : ℝ :=
  Real.pi * (k : ℝ) / (M : ℝ)

/-- The amplitude-error bound from Theorem 12, written via `ε = π k / M`.

Expanded, this is
`2πk sqrt(a(1-a))/M + k^2π^2/M^2`.
-/
def theorem12ErrorBound (a : ℝ) (M k : ℕ) : ℝ :=
  2 * phaseErrorRadius M k * Real.sqrt (a * (1 - a)) +
    phaseErrorRadius M k ^ 2

/-- The probability lower bound stated in Theorem 12. -/
def theorem12SuccessProbability (k : ℕ) : ℝ :=
  if k = 1 then
    8 / Real.pi ^ 2
  else
    1 - 1 / (2 * ((k : ℝ) - 1))

/-- The conclusion promised for a single QAE output. -/
structure EstAmpGuarantee (a aHat : ℝ) (M k : ℕ) : Prop where
  estimate_mem_unit_interval : 0 ≤ aHat ∧ aHat ≤ 1
  error_bound : |aHat - a| ≤ theorem12ErrorBound a M k

/-- The analytic lemma used by the paper as Lemma 7.

The present file proves this analytic ingredient and then uses it in the
Theorem 12 post-processing bounds.
-/
def PaperLemma7 : Prop :=
  ∀ {a theta thetaHat epsilon : ℝ},
    0 ≤ epsilon ->
    a = amplitudeFromAngle theta ->
    |thetaHat - theta| ≤ epsilon ->
      |amplitudeFromAngle thetaHat - a| ≤
        2 * epsilon * Real.sqrt (a * (1 - a)) + epsilon ^ 2

/-- The square-root factor in Lemma 7 is exactly `|sin θ cos θ|`. -/
theorem sqrt_amplitude_complement_eq_abs_sin_mul_cos (theta : ℝ) :
    Real.sqrt (amplitudeFromAngle theta * (1 - amplitudeFromAngle theta)) =
      |Real.sin theta * Real.cos theta| := by
  unfold amplitudeFromAngle
  rw [← Real.cos_sq']
  have hsq : Real.sin theta ^ 2 * Real.cos theta ^ 2 =
      (Real.sin theta * Real.cos theta) ^ 2 := by
    ring
  rw [hsq]
  rw [Real.sqrt_sq_eq_abs]

/-- Trigonometric expansion used in the proof of Lemma 7. -/
theorem sin_sq_add_sub_sin_sq (theta delta : ℝ) :
    Real.sin (theta + delta) ^ 2 - Real.sin theta ^ 2 =
      2 * (Real.sin theta * Real.cos theta) * Real.sin delta * Real.cos delta +
        (Real.cos theta ^ 2 - Real.sin theta ^ 2) * Real.sin delta ^ 2 := by
  rw [Real.sin_add]
  nlinarith [Real.sin_sq_add_cos_sq delta]

/-- The coefficient of the second-order term in Lemma 7 has absolute value at most one. -/
theorem abs_cos_sq_sub_sin_sq_le_one (theta : ℝ) :
    |Real.cos theta ^ 2 - Real.sin theta ^ 2| ≤ 1 := by
  have h : Real.cos theta ^ 2 - Real.sin theta ^ 2 = Real.cos (2 * theta) := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq theta]
  rw [h]
  exact Real.abs_cos_le_one _

/-- Formal proof of the paper's Lemma 7 analytic amplitude-error bound. -/
theorem paperLemma7_bound {a theta thetaHat epsilon : ℝ}
    (heps : 0 ≤ epsilon)
    (ha : a = amplitudeFromAngle theta)
    (hPhase : |thetaHat - theta| ≤ epsilon) :
      |amplitudeFromAngle thetaHat - a| ≤
        2 * epsilon * Real.sqrt (a * (1 - a)) + epsilon ^ 2 := by
  subst a
  let delta := thetaHat - theta
  have hthetaHat : thetaHat = theta + delta := by
    dsimp [delta]
    ring
  have hsqrtd : Real.sqrt (amplitudeFromAngle theta * (1 - amplitudeFromAngle theta)) =
      |Real.sin theta * Real.cos theta| := sqrt_amplitude_complement_eq_abs_sin_mul_cos theta
  have hdelta : |delta| ≤ epsilon := by
    simpa [delta] using hPhase
  have hdelta_nonneg : 0 ≤ |delta| := abs_nonneg _
  have hterm1 :
      |2 * (Real.sin theta * Real.cos theta) * Real.sin delta * Real.cos delta| ≤
        2 * |Real.sin theta * Real.cos theta| * |delta| := by
    calc
      |2 * (Real.sin theta * Real.cos theta) * Real.sin delta * Real.cos delta|
          = 2 * |Real.sin theta * Real.cos theta| * |Real.sin delta| * |Real.cos delta| := by
              rw [abs_mul, abs_mul, abs_mul]
              norm_num
      _ ≤ 2 * |Real.sin theta * Real.cos theta| * |delta| * |Real.cos delta| := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := delta)) (by positivity))
                (abs_nonneg _)
      _ ≤ 2 * |Real.sin theta * Real.cos theta| * |delta| * 1 := by
              exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one delta) (by positivity)
      _ = 2 * |Real.sin theta * Real.cos theta| * |delta| := by ring
  have hterm1eps :
      |2 * (Real.sin theta * Real.cos theta) * Real.sin delta * Real.cos delta| ≤
        2 * epsilon * |Real.sin theta * Real.cos theta| := by
    calc
      |2 * (Real.sin theta * Real.cos theta) * Real.sin delta * Real.cos delta|
          ≤ 2 * |Real.sin theta * Real.cos theta| * |delta| := hterm1
      _ ≤ 2 * |Real.sin theta * Real.cos theta| * epsilon := by
          gcongr
      _ = 2 * epsilon * |Real.sin theta * Real.cos theta| := by ring
  have hsin_sq_le : Real.sin delta ^ 2 ≤ |delta| ^ 2 := by
    have h := Real.abs_sin_le_abs (x := delta)
    simpa [sq_abs] using (sq_le_sq.mpr h)
  have hdelta_sq_le : |delta| ^ 2 ≤ epsilon ^ 2 := by
    nlinarith [hdelta, hdelta_nonneg, heps]
  have hterm2 :
      |(Real.cos theta ^ 2 - Real.sin theta ^ 2) * Real.sin delta ^ 2| ≤ epsilon ^ 2 := by
    calc
      |(Real.cos theta ^ 2 - Real.sin theta ^ 2) * Real.sin delta ^ 2|
          = |Real.cos theta ^ 2 - Real.sin theta ^ 2| * (Real.sin delta ^ 2) := by
              rw [abs_mul]
              rw [abs_of_nonneg (sq_nonneg (Real.sin delta))]
      _ ≤ 1 * |delta| ^ 2 := by
              exact mul_le_mul (abs_cos_sq_sub_sin_sq_le_one theta) hsin_sq_le
                (sq_nonneg _) (by norm_num)
      _ ≤ epsilon ^ 2 := by
              simpa using hdelta_sq_le
  have hdiff :
      amplitudeFromAngle thetaHat - amplitudeFromAngle theta =
        2 * (Real.sin theta * Real.cos theta) * Real.sin delta * Real.cos delta +
          (Real.cos theta ^ 2 - Real.sin theta ^ 2) * Real.sin delta ^ 2 := by
    unfold amplitudeFromAngle
    rw [hthetaHat]
    exact sin_sq_add_sub_sin_sq theta delta
  calc
    |amplitudeFromAngle thetaHat - amplitudeFromAngle theta|
        = |2 * (Real.sin theta * Real.cos theta) * Real.sin delta * Real.cos delta +
          (Real.cos theta ^ 2 - Real.sin theta ^ 2) * Real.sin delta ^ 2| := by
            rw [hdiff]
    _ ≤ |2 * (Real.sin theta * Real.cos theta) * Real.sin delta * Real.cos delta| +
          |(Real.cos theta ^ 2 - Real.sin theta ^ 2) * Real.sin delta ^ 2| := abs_add_le _ _
    _ ≤ 2 * epsilon * |Real.sin theta * Real.cos theta| + epsilon ^ 2 := by
          nlinarith [hterm1eps, hterm2]
    _ = 2 * epsilon * Real.sqrt (amplitudeFromAngle theta * (1 - amplitudeFromAngle theta)) + epsilon ^ 2 := by
          rw [hsqrtd]

/-- The paper's Lemma 7 as a reusable proof object. -/
theorem paperLemma7 : PaperLemma7 := by
  intro a theta thetaHat epsilon heps ha hPhase
  exact paperLemma7_bound heps ha hPhase

/-- Phase-estimation success event needed by QAE.

Theorem 11 of the paper supplies this event for the inverse Fourier
measurement of `|S_M(ω)⟩`.  Theorem 12 then applies it with `ω = θ / π`.
-/
structure PhaseEstimationEvent (theta thetaHat : ℝ) (M k : ℕ) : Type where
  phase_error : |thetaHat - theta| ≤ phaseErrorRadius M k
  event_probability : ℝ
  probability_lower_bound : theorem12SuccessProbability k ≤ event_probability

/-- Theorem 12's analytic core using the proved Lemma 7. -/
theorem theorem12_from_phase_estimation_proved
    {a theta thetaHat : ℝ} {M k : ℕ}
    (hM : 0 < M)
    (ha : a = amplitudeFromAngle theta)
    (hPhase : |thetaHat - theta| ≤ phaseErrorRadius M k) :
    |amplitudeFromAngle thetaHat - a| ≤ theorem12ErrorBound a M k := by
  have hEpsNonneg : 0 ≤ phaseErrorRadius M k := by
    unfold phaseErrorRadius
    positivity
  simpa [theorem12ErrorBound] using paperLemma7 hEpsNonneg ha hPhase

/-- QAE post-processing error using the proved Lemma 7. -/
theorem estAmp_error_from_phase_estimation_proved
    {a theta : ℝ} {M k y : ℕ}
    (hM : 0 < M)
    (ha : a = amplitudeFromAngle theta)
    (hPhase : |(Real.pi * (y : ℝ) / (M : ℝ)) - theta| ≤ phaseErrorRadius M k) :
    |estAmpEstimate M y - a| ≤ theorem12ErrorBound a M k := by
  simpa [estAmpEstimate] using
    theorem12_from_phase_estimation_proved hM ha hPhase

/-- Approximate counting is QAE with `a = t / N`; the estimate is `N * aHat`. -/
def countEstimate (N M y : ℕ) : ℝ :=
  (N : ℝ) * estAmpEstimate M y

/-- Counting error bound obtained directly from Theorem 12 before algebraic
simplification to the paper's Theorem 13 display. -/
def countErrorBound (N t M k : ℕ) : ℝ :=
  (N : ℝ) * theorem12ErrorBound ((t : ℝ) / (N : ℝ)) M k

/-- The counting consequence of the amplitude-estimation bound. -/
theorem count_error_from_estAmp_error
    {N t M k y : ℕ}
    (hN : 0 < N)
    (hAmp :
      |estAmpEstimate M y - ((t : ℝ) / (N : ℝ))| ≤
        theorem12ErrorBound ((t : ℝ) / (N : ℝ)) M k) :
    |countEstimate N M y - (t : ℝ)| ≤ countErrorBound N t M k := by
  unfold countEstimate countErrorBound
  have hMul :=
    mul_le_mul_of_nonneg_left hAmp (by positivity : 0 ≤ (N : ℝ))
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  have hAbs :
      |(N : ℝ) * estAmpEstimate M y - (t : ℝ)| =
        (N : ℝ) * |estAmpEstimate M y - ((t : ℝ) / (N : ℝ))| := by
    calc
      |(N : ℝ) * estAmpEstimate M y - (t : ℝ)|
          = |(N : ℝ) * (estAmpEstimate M y - ((t : ℝ) / (N : ℝ)))| := by
              congr 1
              field_simp [hNne]
      _ = |(N : ℝ)| * |estAmpEstimate M y - ((t : ℝ) / (N : ℝ))| := by
              rw [abs_mul]
      _ = (N : ℝ) * |estAmpEstimate M y - ((t : ℝ) / (N : ℝ))| := by
              rw [abs_of_nonneg]
              positivity
  rwa [hAbs]

end QAE
