import QAELean.AmplitudeEstimation

/-!
# Iterative quantum amplitude estimation

This module formalizes the theorem-level interface of Grinko, Gacon, Zoufal,
and Woerner, "Iterative Quantum Amplitude Estimation" (`arXiv:1912.05559`).

The paper's IQAE proof relies on adaptive quantum sampling, confidence
intervals, and a finite union bound over rounds.  We keep the quantum sampling
and numerical search routines as explicit contracts, and prove the deterministic
parts that turn those contracts into the final accuracy guarantees stated in
Theorem 1 and Theorem 2.
-/

noncomputable section

namespace QAE
namespace IQAE

/-- The two confidence interval methods considered in the IQAE paper. -/
inductive ConfidenceMethod where
  | chernoffHoeffding
  | clopperPearson
  deriving DecidableEq, Repr

/-- A closed interval of real numbers, used for angle and amplitude intervals. -/
structure ClosedInterval where
  lo : ℝ
  hi : ℝ

namespace ClosedInterval

/-- Interval width. -/
def width (I : ClosedInterval) : ℝ :=
  I.hi - I.lo

/-- Midpoint used by IQAE after it returns `[a_l, a_u]`. -/
def midpoint (I : ClosedInterval) : ℝ :=
  (I.lo + I.hi) / 2

/-- Membership in a closed interval. -/
def Contains (I : ClosedInterval) (x : ℝ) : Prop :=
  I.lo ≤ x ∧ x ≤ I.hi

/-- If `x` lies in an interval of width at most `2ε`, then the midpoint estimates
`x` to error at most `ε`.  This is the deterministic last step in Theorems 1
and 2. -/
theorem midpoint_error_of_contains_of_width
    {I : ClosedInterval} {x epsilon : ℝ}
    (hx : I.Contains x)
    (hwidth : I.width ≤ 2 * epsilon) :
    |I.midpoint - x| ≤ epsilon := by
  rw [abs_le]
  constructor
  · unfold midpoint width at *
    nlinarith [hx.2, hwidth]
  · unfold midpoint width at *
    nlinarith [hx.1, hwidth]

end ClosedInterval

/-- The angle multiplier `K = 4k + 2` used in IQAE. -/
def thetaFactor (k : ℕ) : ℝ :=
  4 * (k : ℝ) + 2

/-- Probability of measuring `|1⟩` after applying `Q^k A`, equation (5). -/
def amplifiedSuccessProbability (theta : ℝ) (k : ℕ) : ℝ :=
  amplitudeFromAngle (((2 * (k : ℝ)) + 1) * theta)

/-- The cosine parameter estimated by IQAE via `sin²(x) = (1 - cos(2x))/2`. -/
def cosineParameter (theta : ℝ) (k : ℕ) : ℝ :=
  Real.cos (thetaFactor k * theta)

/-- Equation (5) rewritten in the cosine form used by Algorithm 1. -/
theorem amplifiedSuccessProbability_eq_one_sub_cosine_div_two
    (theta : ℝ) (k : ℕ) :
    amplifiedSuccessProbability theta k = (1 - cosineParameter theta k) / 2 := by
  unfold amplifiedSuccessProbability amplitudeFromAngle cosineParameter thetaFactor
  have harg : (4 * (k : ℝ) + 2) * theta = 2 * ((2 * (k : ℝ) + 1) * theta) := by
    ring
  rw [harg]
  rw [Real.sin_sq_eq_half_sub]
  ring

/-- Base-2 logarithm, used in the paper's bounds. -/
def log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

/-- `T(ε) = log₂(π / (8ε))`, before applying the ceiling in Algorithm 1. -/
def roundBudgetReal (epsilon : ℝ) : ℝ :=
  log2 (Real.pi / (8 * epsilon))

/-- The logarithmic factor common to Theorems 1 and 2. -/
def theoremLogFactor (epsilon alpha : ℝ) : ℝ :=
  Real.log ((2 / alpha) * log2 (Real.pi / (4 * epsilon)))

/-- Equation (6): Chernoff-Hoeffding sufficient shot bound. -/
def chernoffHoeffdingNMax (epsilon alpha : ℝ) : ℝ :=
  32 / (1 - 2 * Real.sin (Real.pi / 14)) ^ 2 * theoremLogFactor epsilon alpha

/-- Equation (C9): Clopper-Pearson sufficient shot bound for the paper's fixed
regime `alpha = 0.05`, `epsilon ≥ 2^(-200)`. -/
def clopperPearsonNMax (epsilon alpha : ℝ) : ℝ :=
  69 * theoremLogFactor epsilon alpha

/-- The number of shots allowed by the selected confidence method. -/
def nMax : ConfidenceMethod -> ℝ -> ℝ -> ℝ
  | .chernoffHoeffding, epsilon, alpha => chernoffHoeffdingNMax epsilon alpha
  | .clopperPearson, epsilon, alpha => clopperPearsonNMax epsilon alpha

/-- Equation (9): Theorem 1 query bound for Chernoff-Hoeffding IQAE. -/
def chernoffHoeffdingOracleBound (epsilon alpha : ℝ) : ℝ :=
  50 / epsilon * theoremLogFactor epsilon alpha

/-- Equation (C3): Theorem 2 query bound for Clopper-Pearson IQAE. -/
def clopperPearsonOracleBound (epsilon alpha : ℝ) : ℝ :=
  14 / epsilon * theoremLogFactor epsilon alpha

/-- The oracle bound associated with a confidence interval method. -/
def oracleBound : ConfidenceMethod -> ℝ -> ℝ -> ℝ
  | .chernoffHoeffding, epsilon, alpha => chernoffHoeffdingOracleBound epsilon alpha
  | .clopperPearson, epsilon, alpha => clopperPearsonOracleBound epsilon alpha

/-- Assumptions specific to Theorem 2's Clopper-Pearson statement. -/
def ClopperPearsonRegime (epsilon alpha : ℝ) : Prop :=
  alpha = 0.05 ∧ (2 : ℝ) ^ (-(200 : ℤ)) ≤ epsilon

/-- The Chernoff-Hoeffding radius used in Algorithm 1, line 20. -/
def chernoffHoeffdingRadius (shots : ℕ) (rounds : ℝ) (alpha : ℝ) : ℝ :=
  Real.sqrt ((1 / (2 * (shots : ℝ))) * Real.log ((2 * rounds) / alpha))

/-- The clipped Chernoff-Hoeffding amplitude interval, Algorithm 1 lines 20-22. -/
def chernoffHoeffdingInterval
    (aHat : ℝ) (shots : ℕ) (rounds alpha : ℝ) : ClosedInterval where
  lo := max 0 (aHat - chernoffHoeffdingRadius shots rounds alpha)
  hi := min 1 (aHat + chernoffHoeffdingRadius shots rounds alpha)

/-- If the empirical estimate is within the CH radius of the true Bernoulli
parameter, then the clipped interval used by Algorithm 1 contains the parameter. -/
theorem contains_of_abs_sub_le_chernoffHoeffdingRadius
    {p aHat : ℝ} {shots : ℕ} {rounds alpha : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (h : |aHat - p| ≤ chernoffHoeffdingRadius shots rounds alpha) :
    (chernoffHoeffdingInterval aHat shots rounds alpha).Contains p := by
  unfold chernoffHoeffdingInterval ClosedInterval.Contains
  constructor
  · apply max_le
    · exact hp0
    · have hupper := (abs_le.mp h).2
      nlinarith
  · apply le_min
    · exact hp1
    · have hlower := (abs_le.mp h).1
      nlinarith

/-- A minimal finite union-bound contract for the per-round confidence failures
used in the IQAE proof. -/
theorem sum_failure_prob_le_alpha
    {T : ℕ} {failureProb : Fin T -> ℝ} {alpha : ℝ}
    (hT : 0 < T)
    (hround : ∀ i, failureProb i ≤ alpha / (T : ℝ)) :
    (∑ i : Fin T, failureProb i) ≤ alpha := by
  classical
  calc
    (∑ i : Fin T, failureProb i) ≤ ∑ _i : Fin T, alpha / (T : ℝ) := by
      exact Finset.sum_le_sum (fun i _hi => hround i)
    _ = alpha := by
      have hTne : (T : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hT)
      have hsumconst : (∑ _i : Fin T, alpha / (T : ℝ)) = (T : ℝ) * (alpha / (T : ℝ)) := by
        simp
      rw [hsumconst]
      field_simp [hTne]

/-- Half-plane used by `FindNextK`: upper `[0,π]` or lower `[π,2π]`. -/
inductive HalfPlane where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- Membership in one of the two half-planes. -/
def HalfPlane.Contains : HalfPlane -> ℝ -> Prop
  | .upper, x => 0 ≤ x ∧ x ≤ Real.pi
  | .lower, x => Real.pi ≤ x ∧ x ≤ 2 * Real.pi

/-- Reduction of an angle modulo `2π`, written with `floor` to mirror
Algorithm 2's circle arithmetic. -/
def modTwoPi (x : ℝ) : ℝ :=
  x - (2 * Real.pi) * (⌊x / (2 * Real.pi)⌋ : ℝ)

/-- A feasible `K = 4k + 2` candidate for Algorithm 2: it has the right residue
class, is large enough relative to the previous factor, and puts both scaled
endpoints in one half-plane after reduction modulo `2π`. -/
structure FeasibleThetaFactor (I : ClosedInterval) (oldk : ℕ) (r : ℝ) (K : ℕ) : Prop where
  residue : K % 4 = 2
  growth : r * thetaFactor oldk ≤ (K : ℝ)
  width_bound : (K : ℝ) * I.width ≤ Real.pi
  halfPlane_exists :
    ∃ halfPlane : HalfPlane,
      halfPlane.Contains (modTwoPi ((K : ℝ) * I.lo)) ∧
        halfPlane.Contains (modTwoPi ((K : ℝ) * I.hi))

/-- The specification implemented by `FindNextK`: either it keeps the old power,
or it returns a feasible larger `K`.  This abstracts away the executable search
loop while preserving the theorem-relevant contract. -/
structure FindNextKResult (I : ClosedInterval) (oldk : ℕ) (r : ℝ) where
  nextk : ℕ
  halfPlane : HalfPlane
  either_old_or_feasible :
    nextk = oldk ∨ FeasibleThetaFactor I oldk r (4 * nextk + 2)

/-- If `FindNextK` does not keep the old power, the returned factor is feasible
in exactly the sense needed by the IQAE proof. -/
theorem feasible_of_findNextK_progress
    {I : ClosedInterval} {oldk : ℕ} {r : ℝ} {result : FindNextKResult I oldk r}
    (hprogress : result.nextk ≠ oldk) :
    FeasibleThetaFactor I oldk r (4 * result.nextk + 2) := by
  rcases result.either_old_or_feasible with h | h
  · exact False.elim (hprogress h)
  · exact h

/-- The data that Theorems 1 and 2 assert about a completed IQAE run.  The
probability fields are real-valued event bounds, not a full measure-theoretic
model of the quantum experiment. -/
structure RunCertificate (method : ConfidenceMethod) (epsilon alpha : ℝ) where
  shots : ℕ
  shots_pos : 1 ≤ shots
  shots_le_nMax : (shots : ℝ) ≤ nMax method epsilon alpha
  rounds : ℕ
  rounds_le_budget : (rounds : ℝ) ≤ Int.ceil (roundBudgetReal epsilon)
  max_iterations_per_round : ℝ
  max_iterations_per_round_le : max_iterations_per_round ≤ nMax method epsilon alpha / (shots : ℝ)
  thetaInterval : ClosedInterval
  theta_width : thetaInterval.width ≤ 2 * epsilon
  theta_failure_probability : ℝ
  theta_failure_probability_le : theta_failure_probability ≤ alpha
  amplitudeInterval : ClosedInterval
  amplitude_width : amplitudeInterval.width ≤ 2 * epsilon
  amplitude_failure_probability : ℝ
  amplitude_failure_probability_le : amplitude_failure_probability ≤ alpha
  oracleCalls : ℝ
  oracleCalls_lt : oracleCalls < oracleBound method epsilon alpha

/-- Deterministic consequence of Theorem 1 or 2: if the true amplitude is inside
the returned interval, the midpoint estimate has error at most `epsilon`. -/
theorem midpoint_amplitude_error_of_runCertificate
    {method : ConfidenceMethod} {epsilon alpha a : ℝ}
    (run : RunCertificate method epsilon alpha)
    (ha : run.amplitudeInterval.Contains a) :
    |run.amplitudeInterval.midpoint - a| ≤ epsilon := by
  exact ClosedInterval.midpoint_error_of_contains_of_width ha run.amplitude_width

/-- Theorem 1 packaged for the Chernoff-Hoeffding method. -/
theorem theorem1_chernoffHoeffding_midpoint_accuracy
    {epsilon alpha a : ℝ}
    (run : RunCertificate .chernoffHoeffding epsilon alpha)
    (ha : run.amplitudeInterval.Contains a) :
    |run.amplitudeInterval.midpoint - a| ≤ epsilon ∧
      run.amplitude_failure_probability ≤ alpha ∧
      run.oracleCalls < chernoffHoeffdingOracleBound epsilon alpha := by
  constructor
  · exact midpoint_amplitude_error_of_runCertificate run ha
  constructor
  · exact run.amplitude_failure_probability_le
  · simpa [oracleBound] using run.oracleCalls_lt

/-- Theorem 2 packaged for the Clopper-Pearson method and its stated numerical
regime. -/
theorem theorem2_clopperPearson_midpoint_accuracy
    {epsilon alpha a : ℝ}
    (hregime : ClopperPearsonRegime epsilon alpha)
    (run : RunCertificate .clopperPearson epsilon alpha)
    (ha : run.amplitudeInterval.Contains a) :
    |run.amplitudeInterval.midpoint - a| ≤ epsilon ∧
      run.amplitude_failure_probability ≤ alpha ∧
      run.oracleCalls < clopperPearsonOracleBound epsilon alpha := by
  rcases hregime with ⟨_, _⟩
  constructor
  · exact midpoint_amplitude_error_of_runCertificate run ha
  constructor
  · exact run.amplitude_failure_probability_le
  · simpa [oracleBound] using run.oracleCalls_lt

end IQAE
end QAE
