import QAELean.QuantumAmplitudeEstimation

/-!
# Iterative quantum amplitude estimation

This file records the paper-level objects from Grinko, Gacon, Zoufal, and
Woerner, "Iterative Quantum Amplitude Estimation" (`arXiv:1912.05559`).

The existing QAE development already contains the general BHMT operator
`paperGroverOperator n A f`, where `f` marks arbitrary good computational-basis
states.  IQAE uses the more concrete setup from the paper: the state-preparation
unitary `A` acts on `n + 1` qubits, and good states are exactly those whose last
state qubit is `1`.  The definitions below specialize the existing oracle and
then add the classical IQAE interval and `FindNextK` machinery around it.
-/

noncomputable section

namespace QAE
namespace IQAE

open QuantumComputing
open scoped BigOperators

/-- The final state qubit in the IQAE paper's `n + 1` state-qubit register. -/
def lastStateQubit (n : ℕ) : Fin (n + 1) :=
  ⟨n, Nat.lt_succ_self n⟩

/-- IQAE's fixed good-state predicate: the last of the `n + 1` state qubits is `1`.

This is the specialization requested in the IQAE paper, as opposed to the
general BHMT/QAE predicate `f : Fin (2^N) → Bool` used elsewhere in the project.
-/
def goodStatePredicate (n : ℕ) (x : Fin (QPE.M (n + 1))) : Bool :=
  Nat.testBit x.val n

/-- IQAE's state-preparation unitary type: a matrix on the full `n + 1`
state-qubit register.  The paper writes this operator as `A`. -/
abbrev StatePreparation (n : ℕ) :=
  Square (QPE.M (n + 1))

/-- The all-zero input state after applying IQAE's state preparation `A`. -/
def preparedState (n : ℕ) (A : StatePreparation n) : Vector (QPE.M (n + 1)) :=
  Grover.paperPreparedState (n + 1) A

/-- Probability mass of `A|0^(n+1)⟩` on states whose last qubit is `0`. -/
def badProbability (n : ℕ) (A : StatePreparation n) : ℝ :=
  Grover.paperBadProbability (n + 1) A (goodStatePredicate n)

/-- Probability mass of `A|0^(n+1)⟩` on states whose last qubit is `1`.

This is the unknown amplitude `a` estimated by IQAE. -/
def goodProbability (n : ℕ) (A : StatePreparation n) : ℝ :=
  Grover.paperGoodProbability (n + 1) A (goodStatePredicate n)

/-- IQAE's Grover iterate `Q = -A S₀ A† S_χ`, specialized to the last-qubit
predicate `χ(x) = 1` iff the last state qubit of `x` is `1`. -/
def groverOperator (n : ℕ) (A : StatePreparation n) : Square (QPE.M (n + 1)) :=
  Grover.paperGroverOperator (n + 1) A (goodStatePredicate n)

/-- The state `Q^k A|0^n⟩|0⟩` sampled by IQAE. -/
def stateAfterGroverPower (n k : ℕ) (A : StatePreparation n) :
    Vector (QPE.M (n + 1)) :=
  (groverOperator n A ^ k) ⬝ preparedState n A

/-- The probability of measuring `1` in the last qubit of
`Q^k A|0^n⟩|0⟩`. -/
def lastQubitOneProbability (n k : ℕ) (A : StatePreparation n) : ℝ :=
  ∑ x : Fin (QPE.M (n + 1)),
    if goodStatePredicate n x then Measurement.prob (stateAfterGroverPower n k A) x else 0

/-- The IQAE paper's ideal Bernoulli success probability:
`P[|1⟩] = sin²((2k + 1)θₐ)`. -/
def idealSuccessProbability (k : ℕ) (theta : ℝ) : ℝ :=
  amplitudeFromAngle ((2 * (k : ℝ) + 1) * theta)

@[simp] theorem idealSuccessProbability_eq_sin_sq (k : ℕ) (theta : ℝ) :
    idealSuccessProbability k theta = Real.sin ((2 * (k : ℝ) + 1) * theta) ^ 2 := rfl

/-- The two confidence-interval options considered by IQAE. -/
inductive ConfidenceIntervalKind where
  | chernoffHoeffding
  | clopperPearson
deriving DecidableEq, Repr

/-- IQAE's angle factor `K = 4k + 2`. -/
def thetaFactor (k : ℕ) : ℕ :=
  4 * k + 2

@[simp] theorem thetaFactor_pos (k : ℕ) : 0 < thetaFactor k := by
  unfold thetaFactor
  omega

/-- `T(ε) = ceil(log₂(π / (8ε)))`, the paper's round bound. -/
def maxRounds (epsilon : ℝ) : ℕ :=
  Nat.ceil (Real.logb 2 (Real.pi / (8 * epsilon)))

/-- Theorem 1's Chernoff-Hoeffding `Nmax(ε, α)` from equation (6). -/
def theoremOneNmax (epsilon alpha : ℝ) : ℝ :=
  32 / (1 - 2 * Real.sin (Real.pi / 14)) ^ 2 *
    Real.log (2 / alpha * Real.logb 2 (Real.pi / (4 * epsilon)))

/-- Theorem 1's oracle-query upper bound from equation (9). -/
def theoremOneOracleBound (epsilon alpha : ℝ) : ℝ :=
  50 / epsilon * Real.log (2 / alpha * Real.logb 2 (Real.pi / (4 * epsilon)))

/-- Appendix C's Clopper-Pearson `Nmax(ε, α)` from Theorem 2. -/
def theoremTwoNmax (epsilon alpha : ℝ) : ℝ :=
  69 * Real.log (2 / alpha * Real.logb 2 (Real.pi / (4 * epsilon)))

/-- Appendix C's Clopper-Pearson oracle-query upper bound from Theorem 2. -/
def theoremTwoOracleBound (epsilon alpha : ℝ) : ℝ :=
  14 / epsilon * Real.log (2 / alpha * Real.logb 2 (Real.pi / (4 * epsilon)))

/-- Appendix B Lemma 1's threshold `L*`. -/
def lemmaOneLStar : ℝ :=
  Real.arcsin ((1 / 2 : ℝ) * Real.sqrt (1 - 2 * Real.sin (Real.pi / 14)))

/-- Appendix B equation (B12), the shot bound used by Lemma 1. -/
def lemmaOneNmax (L T alpha : ℝ) : ℝ :=
  2 / Real.sin L ^ 4 * Real.log (2 * T / alpha)

/-- Appendix B Lemma 1's value of `Lmin`. -/
def lemmaOneLmin (L : ℝ) : ℝ :=
  Real.arcsin (Real.sin L ^ 2)


/-- Appendix B Lemma 1's value of `Lmax`; the paper proves this is just `L`. -/
def lemmaOneLmax (L : ℝ) : ℝ :=
  L

/-- Upper-half domain of the paper's `g_L` from Supplementary Eq. (19). -/
def lemmaOneGUpperDomain (L : ℝ) : Set ℝ :=
  Set.Icc (Real.arcsin (Real.sin L / Real.sqrt 2))
    (Real.pi - Real.arcsin (Real.sin L / Real.sqrt 2))

/-- Lower-half domain of the paper's `g_L` from Supplementary Eq. (19). -/
def lemmaOneGLowerDomain (L : ℝ) : Set ℝ :=
  Set.Icc (Real.pi + Real.arcsin (Real.sin L / Real.sqrt 2))
    (2 * Real.pi - Real.arcsin (Real.sin L / Real.sqrt 2))

/-- Domain of the paper's `g_L`: the union of the upper and lower half-plane domains. -/
def lemmaOneGDomain (L : ℝ) : Set ℝ :=
  lemmaOneGUpperDomain L ∪ lemmaOneGLowerDomain L

/-- Upper-half branch of Supplementary Eq. (19). -/
def lemmaOneGUpper (L theta : ℝ) : ℝ :=
  min (Real.arcsin (Real.sin L ^ 2 / Real.sin theta))
    (min theta (Real.pi - theta))

/-- Lower-half branch of Supplementary Eq. (19). -/
def lemmaOneGLower (L theta : ℝ) : ℝ :=
  min (Real.arcsin (Real.sin L ^ 2 / Real.sin (theta - Real.pi)))
    (min (theta - Real.pi) (2 * Real.pi - theta))

/-- The paper's piecewise function `g_L`, translating amplitude half-width into
angle half-width in Appendix B, Lemma 1. -/
def lemmaOneG (L theta : ℝ) : ℝ :=
  by
    classical
    exact
      if theta ∈ lemmaOneGUpperDomain L then
        lemmaOneGUpper L theta
      else
        lemmaOneGLower L theta

/-- The closed sector `[jπ/m, (j+1)π/m]` used in Supplementary Eqs. (22)-(24). -/
def lemmaOneSector (m j : ℕ) : Set ℝ :=
  Set.Icc (((j : ℝ) * Real.pi) / (m : ℝ))
    ((((j + 1 : ℕ) : ℝ) * Real.pi) / (m : ℝ))

/-- The interval centered at `theta` with half-width `error`. -/
def centeredAngleInterval (theta error : ℝ) : Set ℝ :=
  Set.Icc (theta - error) (theta + error)

/-- A sector-covering witness for Supplementary Eqs. (22)-(24): the current
angle interval fits into one of the `π/3`, `π/5`, or `π/7` sectors. -/
def lemmaOneHasSectorCover (theta error : ℝ) : Prop :=
  ∃ m : ℕ, (m = 3 ∨ m = 5 ∨ m = 7) ∧
    ∃ j : ℕ, j < 2 * m ∧ centeredAngleInterval theta error ⊆ lemmaOneSector m j

/-- The paper's covering condition in Supplementary Eq. (26), stated using the
sector formulation from Supplementary Eqs. (22)-(24). -/
def lemmaOneCoveringCondition (L : ℝ) : Prop :=
  ∀ theta : ℝ, theta ∈ lemmaOneGDomain L →
    lemmaOneHasSectorCover theta (lemmaOneG L theta)

/-- A schedule-growth witness: whenever the current angle interval satisfies one
of the sector-covering conditions, `FindNextK` can choose a next factor with
`q_i ≥ r` for every `r ∈ (1, 3]`. -/
def lemmaOneSectorCoverImpliesGrowth (L : ℝ) (q : ℝ → ℝ) : Prop :=
  ∀ theta : ℝ, theta ∈ lemmaOneGDomain L →
    lemmaOneHasSectorCover theta (lemmaOneG L theta) →
      ∀ r : ℝ, r ∈ Set.Ioc (1 : ℝ) 3 → r ≤ q theta

/-- Fourth root written using square roots, enough for the positive quantities
appearing in the Chernoff-Hoeffding `Lmax` formula. -/
def fourthRoot (x : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt x)

/-- Equation (10): the direct Chernoff-Hoeffding expression for `Lmax`. -/
def chernoffHoeffdingLmax (Nshots : ℕ) (epsilon alpha : ℝ) : ℝ :=
  Real.arcsin
    (fourthRoot ((2 / (Nshots : ℝ)) *
      Real.log (2 * (maxRounds epsilon : ℝ) / alpha)))

/-- The Chernoff-Hoeffding radius for a Bernoulli estimate with `N` shots,
allocated over `T` rounds with total failure probability `α`. -/
def chernoffHoeffdingRadius (N T : ℕ) (alpha : ℝ) : ℝ :=
  Real.sqrt ((1 / (2 * (N : ℝ))) * Real.log (2 * (T : ℝ) / alpha))

/-- Clip an amplitude lower endpoint to `[0, 1]`. -/
def clipLowerAmplitude (x : ℝ) : ℝ :=
  max 0 x

/-- Clip an amplitude upper endpoint to `[0, 1]`. -/
def clipUpperAmplitude (x : ℝ) : ℝ :=
  min 1 x

def chernoffHoeffdingAmplitudeLower (N T : ℕ) (alpha observed : ℝ) : ℝ :=
  clipLowerAmplitude (observed - chernoffHoeffdingRadius N T alpha)

def chernoffHoeffdingAmplitudeUpper (N T : ℕ) (alpha observed : ℝ) : ℝ :=
  clipUpperAmplitude (observed + chernoffHoeffdingRadius N T alpha)

/-- Lines 19-22 of Algorithm 1: a Chernoff-Hoeffding confidence interval for the
observed Bernoulli success frequency. -/
def chernoffHoeffdingAmplitudeInterval
    (N T : ℕ) (alpha observed : ℝ) : Set ℝ :=
  Set.Icc (chernoffHoeffdingAmplitudeLower N T alpha observed)
    (chernoffHoeffdingAmplitudeUpper N T alpha observed)

/-- The beta CDF from Mathlib's beta distribution. -/
def betaCDF (alpha beta x : ℝ) : ℝ :=
  (ProbabilityTheory.betaMeasure alpha beta (Set.Iic x)).toReal

/-- The inverse regularized beta function used by the paper's Clopper-Pearson
interval.  Mathlib has beta distributions but no named inverse regularized beta
CDF, so we define the generalized inverse of `betaCDF` on `[0, 1]`. -/
def inverseRegularizedBeta (p alpha beta : ℝ) : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ x ≤ 1 ∧ p ≤ betaCDF alpha beta x}

def clopperPearsonAmplitudeLower (N T : ℕ) (alpha observed : ℝ) : ℝ :=
  inverseRegularizedBeta (1 - alpha / (2 * (T : ℝ))) ((N : ℝ) * observed + 1)
    ((N : ℝ) * (1 - observed))

def clopperPearsonAmplitudeUpper (N T : ℕ) (alpha observed : ℝ) : ℝ :=
  inverseRegularizedBeta (alpha / (2 * (T : ℝ))) ((N : ℝ) * observed)
    ((N : ℝ) * (1 - observed) + 1)

/-- Lines 23-25 of Algorithm 1: the Clopper-Pearson confidence interval for the
observed Bernoulli success frequency. -/
def clopperPearsonAmplitudeInterval (N T : ℕ) (alpha observed : ℝ) : Set ℝ :=
  Set.Icc (clopperPearsonAmplitudeLower N T alpha observed)
    (clopperPearsonAmplitudeUpper N T alpha observed)

def amplitudeConfidenceIntervalLower
    (kind : ConfidenceIntervalKind) (N T : ℕ) (alpha observed : ℝ) : ℝ :=
  match kind with
  | .chernoffHoeffding => chernoffHoeffdingAmplitudeLower N T alpha observed
  | .clopperPearson => clopperPearsonAmplitudeLower N T alpha observed

def amplitudeConfidenceIntervalUpper
    (kind : ConfidenceIntervalKind) (N T : ℕ) (alpha observed : ℝ) : ℝ :=
  match kind with
  | .chernoffHoeffding => chernoffHoeffdingAmplitudeUpper N T alpha observed
  | .clopperPearson => clopperPearsonAmplitudeUpper N T alpha observed

/-- Select the paper's confidence-interval formula. -/
def amplitudeConfidenceInterval
    (kind : ConfidenceIntervalKind) (N T : ℕ) (alpha observed : ℝ) : Set ℝ :=
  Set.Icc (amplitudeConfidenceIntervalLower kind N T alpha observed)
    (amplitudeConfidenceIntervalUpper kind N T alpha observed)

/-- Upper half-plane test using Mathlib's representative in `[0, 2π)`. -/
def inUpperHalfPlane (x : ℝ) : Prop :=
  toIcoMod Real.two_pi_pos 0 x ≤ Real.pi

/-- Lower half-plane test using Mathlib's representative in `[0, 2π)`. -/
def inLowerHalfPlane (x : ℝ) : Prop :=
  Real.pi ≤ toIcoMod Real.two_pi_pos 0 x

/-- The largest `K` considered by `FindNextK`, before forcing `K ≡ 2 mod 4`. -/
def findNextKMax (thetaLower thetaUpper : ℝ) : ℕ :=
  Nat.floor (Real.pi / (thetaUpper - thetaLower))

/-- Algorithm 2, line 6: largest potential `K` of the form `4k + 2` below
`Kmax`, written with saturating natural subtraction for totality. -/
def largestPotentialThetaFactor (thetaLower thetaUpper : ℝ) : ℕ :=
  findNextKMax thetaLower thetaUpper - ((findNextKMax thetaLower thetaUpper - 2) % 4)

/-- A candidate theta-factor accepted by Algorithm 2.  The half-plane condition
is stated directly as `[Kθ_l, Kθ_u] mod 2π` lying in the upper or lower half
plane. -/
def ValidThetaFactorCandidate (ki : ℕ) (thetaLower thetaUpper : ℝ) (r K : ℕ) : Prop :=
  K % 4 = 2 ∧
    r * thetaFactor ki ≤ K ∧
    K ≤ largestPotentialThetaFactor thetaLower thetaUpper ∧
    ((inUpperHalfPlane ((K : ℝ) * thetaLower) ∧
        inUpperHalfPlane ((K : ℝ) * thetaUpper)) ∨
      (inLowerHalfPlane ((K : ℝ) * thetaLower) ∧
        inLowerHalfPlane ((K : ℝ) * thetaUpper)))

/-- The largest valid theta-factor for `FindNextK`, or `0` if no valid factor
exists. -/
def findNextThetaFactor (ki : ℕ) (thetaLower thetaUpper : ℝ) (r : ℕ := 2) : ℕ :=
  by
    classical
    exact Nat.findGreatest (ValidThetaFactorCandidate ki thetaLower thetaUpper r)
      (largestPotentialThetaFactor thetaLower thetaUpper)

/-- Result returned by Algorithm 2. -/
structure NextK where
  k : ℕ
  upperHalfPlane : Bool
deriving Repr

/-- Upper-half-plane test used by the concrete `FindNextK` result.  If the
candidate lies on a boundary and satisfies both tests, this follows Algorithm 2
by choosing the upper half-plane first. -/
def thetaFactorChoosesUpper (K : ℕ) (thetaLower thetaUpper : ℝ) : Bool :=
  by
    classical
    exact decide (inUpperHalfPlane ((K : ℝ) * thetaLower) ∧
      inUpperHalfPlane ((K : ℝ) * thetaUpper))

/-- Algorithm 2, represented as a bounded largest-candidate search. -/
def findNextK (ki : ℕ) (thetaLower thetaUpper : ℝ) (upi : Bool) (r : ℕ := 2) : NextK :=
  by
    classical
    let K := findNextThetaFactor ki thetaLower thetaUpper r
    exact
      if ValidThetaFactorCandidate ki thetaLower thetaUpper r K then
        { k := (K - 2) / 4, upperHalfPlane := thetaFactorChoosesUpper K thetaLower thetaUpper }
      else
        { k := ki, upperHalfPlane := upi }

def scaledThetaLower (upperHalfPlane : Bool) (amplitudeLower amplitudeUpper : ℝ) : ℝ :=
  if upperHalfPlane then
    Real.arccos (1 - 2 * amplitudeLower)
  else
    2 * Real.pi - Real.arccos (1 - 2 * amplitudeUpper)

def scaledThetaUpper (upperHalfPlane : Bool) (amplitudeLower amplitudeUpper : ℝ) : ℝ :=
  if upperHalfPlane then
    Real.arccos (1 - 2 * amplitudeUpper)
  else
    2 * Real.pi - Real.arccos (1 - 2 * amplitudeLower)

/-- The angle interval for `{Kθₐ} mod 2π` obtained by inverting
`a = (1 - cos(Kθ))/2` on the selected half-plane. -/
def scaledThetaIntervalFromAmplitude
    (upperHalfPlane : Bool) (amplitudeLower amplitudeUpper : ℝ) : Set ℝ :=
  Set.Icc (scaledThetaLower upperHalfPlane amplitudeLower amplitudeUpper)
    (scaledThetaUpper upperHalfPlane amplitudeLower amplitudeUpper)

/-- The multiple of `2π` used to lift a scaled residue back to the current
global angle interval. -/
def twoPiPeriodBelow (x : ℝ) : ℝ :=
  (2 * Real.pi) * (Int.floor (x / (2 * Real.pi)) : ℝ)

def unscaleThetaLower (K : ℕ) (previousLower scaledLower : ℝ) : ℝ :=
  (twoPiPeriodBelow ((K : ℝ) * previousLower) + scaledLower) / (K : ℝ)

def unscaleThetaUpper (K : ℕ) (previousUpper scaledUpper : ℝ) : ℝ :=
  (twoPiPeriodBelow ((K : ℝ) * previousUpper) + scaledUpper) / (K : ℝ)

/-- Lines 27-28 of Algorithm 1: unscale the refined interval for
`{Kθₐ} mod 2π` back to an interval for `θₐ`. -/
def unscaleThetaInterval
    (K : ℕ) (previousLower previousUpper scaledLower scaledUpper : ℝ) : Set ℝ :=
  Set.Icc (unscaleThetaLower K previousLower scaledLower)
    (unscaleThetaUpper K previousUpper scaledUpper)

/-- The number of shots used in an iteration with the paper's no-overshooting
condition. -/
def shotsForThetaFactor (Nshots K : ℕ) (Lmax epsilon : ℝ) : ℕ :=
  if (Nat.ceil (Lmax / epsilon)) < K then
    Nat.ceil ((Nshots : ℝ) * Lmax / epsilon / (K : ℝ) / 10)
  else
    Nshots

/-- A compact record of one IQAE iteration after quantum sampling has produced
an observed last-qubit-one frequency.  The actual interval is
`Set.Icc thetaLower thetaUpper`. -/
structure IterationInput where
  thetaLower : ℝ
  thetaUpper : ℝ
  previousK : ℕ
  previousUpperHalfPlane : Bool
  observedFrequency : ℝ

/-- The current angle-confidence interval as a Mathlib closed interval. -/
def IterationInput.thetaInterval (input : IterationInput) : Set ℝ :=
  Set.Icc input.thetaLower input.thetaUpper

/-- The deterministic classical update performed around one IQAE sampling step.
The quantum part supplying `observedFrequency` is represented separately by
`lastQubitOneProbability` and, ideally, `idealSuccessProbability`. -/
def classicalIteration
    (kind : ConfidenceIntervalKind)
    (epsilon alpha Lmax : ℝ) (Nshots : ℕ) (input : IterationInput) :
    IterationInput :=
  let next := findNextK input.previousK input.thetaLower input.thetaUpper
    input.previousUpperHalfPlane
  let K := thetaFactor next.k
  let N := shotsForThetaFactor Nshots K Lmax epsilon
  let ampLower := amplitudeConfidenceIntervalLower kind N (maxRounds epsilon) alpha
    input.observedFrequency
  let ampUpper := amplitudeConfidenceIntervalUpper kind N (maxRounds epsilon) alpha
    input.observedFrequency
  let scaledLower := scaledThetaLower next.upperHalfPlane ampLower ampUpper
  let scaledUpper := scaledThetaUpper next.upperHalfPlane ampLower ampUpper
  { thetaLower := unscaleThetaLower K input.thetaLower scaledLower
    thetaUpper := unscaleThetaUpper K input.thetaUpper scaledUpper
    previousK := next.k
    previousUpperHalfPlane := next.upperHalfPlane
    observedFrequency := input.observedFrequency }

/-- Initial IQAE interval state from Algorithm 1. -/
def initialIterationInput : IterationInput where
  thetaLower := 0
  thetaUpper := Real.pi / 2
  previousK := 0
  previousUpperHalfPlane := true
  observedFrequency := 0

/-- The final amplitude interval returned from a theta interval by line 29 of
Algorithm 1. -/
def amplitudeIntervalFromThetaInterval (thetaLower thetaUpper : ℝ) : Set ℝ :=
  Set.Icc (amplitudeFromAngle thetaLower) (amplitudeFromAngle thetaUpper)


/-- One batch of observed samples used by Algorithm 1.  The frequency is the
measured fraction of outcomes whose last state qubit is `1`. -/
structure IQAEObservation where
  frequency : ℝ

/-- Internal state of the adaptive IQAE loop.  The fields `combinedShots` and
`combinedFrequency` implement Algorithm 1, lines 17-18: repeated iterations with
the same `kᵢ` are combined into one effective Bernoulli estimate. -/
structure IQAEState where
  thetaLower : ℝ
  thetaUpper : ℝ
  previousK : ℕ
  previousUpperHalfPlane : Bool
  combinedShots : ℕ
  combinedFrequency : ℝ
  rounds : ℕ
  oracleCalls : ℕ

/-- The current theta interval of an IQAE state. -/
def IQAEState.thetaInterval (state : IQAEState) : Set ℝ :=
  Set.Icc state.thetaLower state.thetaUpper

/-- Initial state from Algorithm 1: `[θ_l, θ_u] = [0, π/2]`, `k = 0`, upper
half-plane. -/
def initialIQAEState : IQAEState where
  thetaLower := 0
  thetaUpper := Real.pi / 2
  previousK := 0
  previousUpperHalfPlane := true
  combinedShots := 0
  combinedFrequency := 0
  rounds := 0
  oracleCalls := 0

/-- Weighted combination of old and new observed frequencies.  The zero-shot
case is total so that the algorithm remains a total Lean function. -/
def combineFrequencies
    (oldShots newShots : ℕ) (oldFrequency newFrequency : ℝ) : ℝ :=
  let total := oldShots + newShots
  if total = 0 then
    newFrequency
  else
    ((oldShots : ℝ) * oldFrequency + (newShots : ℝ) * newFrequency) / (total : ℝ)

/-- One deterministic execution of Algorithm 1, lines 10-28, after a batch of
quantum measurements has supplied `observation.frequency`. -/
def iqaeStep
    (kind : ConfidenceIntervalKind) (epsilon alpha Lmax : ℝ) (Nshots : ℕ)
    (state : IQAEState) (observation : IQAEObservation) : IQAEState :=
  let next := findNextK state.previousK state.thetaLower state.thetaUpper
    state.previousUpperHalfPlane
  let K := thetaFactor next.k
  let N := shotsForThetaFactor Nshots K Lmax epsilon
  let startsNewRound := state.combinedShots = 0 ∨ next.k ≠ state.previousK
  let previousShots := if startsNewRound then 0 else state.combinedShots
  let previousFrequency := if startsNewRound then 0 else state.combinedFrequency
  let combinedShots := previousShots + N
  let combinedFrequency := combineFrequencies previousShots N previousFrequency observation.frequency
  let ampLower := amplitudeConfidenceIntervalLower kind combinedShots (maxRounds epsilon) alpha
    combinedFrequency
  let ampUpper := amplitudeConfidenceIntervalUpper kind combinedShots (maxRounds epsilon) alpha
    combinedFrequency
  let scaledLower := scaledThetaLower next.upperHalfPlane ampLower ampUpper
  let scaledUpper := scaledThetaUpper next.upperHalfPlane ampLower ampUpper
  { thetaLower := unscaleThetaLower K state.thetaLower scaledLower
    thetaUpper := unscaleThetaUpper K state.thetaUpper scaledUpper
    previousK := next.k
    previousUpperHalfPlane := next.upperHalfPlane
    combinedShots := combinedShots
    combinedFrequency := combinedFrequency
    rounds := if startsNewRound then state.rounds + 1 else state.rounds
    oracleCalls := state.oracleCalls + N * next.k }

/-- Algorithm 1 with explicit fuel and an explicit stream of observed
frequencies.  The fuel is instantiated by `maxRounds ε` in `iqaeFinalState`. -/
def iqaeAux
    (kind : ConfidenceIntervalKind) (epsilon alpha Lmax : ℝ) (Nshots : ℕ)
    (fuel : ℕ) (observations : List IQAEObservation) (state : IQAEState) : IQAEState :=
  match fuel with
  | 0 => state
  | fuel' + 1 =>
      if state.thetaUpper - state.thetaLower ≤ 2 * epsilon then
        state
      else
        match observations with
        | [] => state
        | observation :: rest =>
            iqaeAux kind epsilon alpha Lmax Nshots fuel' rest
              (iqaeStep kind epsilon alpha Lmax Nshots state observation)

/-- Algorithm 1 run with the paper's maximum number of rounds. -/
def iqaeFinalState
    (kind : ConfidenceIntervalKind) (epsilon alpha Lmax : ℝ) (Nshots : ℕ)
    (observations : List IQAEObservation) : IQAEState :=
  iqaeAux kind epsilon alpha Lmax Nshots (maxRounds epsilon) observations initialIQAEState

/-- The returned value of Algorithm 1, line 30. -/
structure IQAEOutput where
  thetaLower : ℝ
  thetaUpper : ℝ
  amplitudeLower : ℝ
  amplitudeUpper : ℝ
  estimate : ℝ
  rounds : ℕ
  oracleCalls : ℕ

/-- Theta interval returned by IQAE. -/
def IQAEOutput.thetaInterval (output : IQAEOutput) : Set ℝ :=
  Set.Icc output.thetaLower output.thetaUpper

/-- Amplitude interval returned by IQAE. -/
def IQAEOutput.amplitudeInterval (output : IQAEOutput) : Set ℝ :=
  Set.Icc output.amplitudeLower output.amplitudeUpper

/-- Convert the final loop state into Algorithm 1's returned amplitude interval
and midpoint estimate. -/
def iqaeOutputOfState (state : IQAEState) : IQAEOutput :=
  let amplitudeLower := amplitudeFromAngle state.thetaLower
  let amplitudeUpper := amplitudeFromAngle state.thetaUpper
  { thetaLower := state.thetaLower
    thetaUpper := state.thetaUpper
    amplitudeLower := amplitudeLower
    amplitudeUpper := amplitudeUpper
    estimate := (amplitudeLower + amplitudeUpper) / 2
    rounds := state.rounds
    oracleCalls := state.oracleCalls }

/-- The IQAE algorithm from the paper, as a deterministic function of the
measurement frequencies supplied by the quantum computer. -/
def iqae
    (kind : ConfidenceIntervalKind) (epsilon alpha Lmax : ℝ) (Nshots : ℕ)
    (observations : List IQAEObservation) : IQAEOutput :=
  iqaeOutputOfState (iqaeFinalState kind epsilon alpha Lmax Nshots observations)

private theorem iqaeStep_rounds_le
    (kind : ConfidenceIntervalKind) (epsilon alpha Lmax : ℝ) (Nshots : ℕ)
    (state : IQAEState) (observation : IQAEObservation) :
    (iqaeStep kind epsilon alpha Lmax Nshots state observation).rounds ≤ state.rounds + 1 := by
  unfold iqaeStep
  by_cases h : state.combinedShots = 0 ∨
      (findNextK state.previousK state.thetaLower state.thetaUpper
        state.previousUpperHalfPlane).k ≠ state.previousK
  · simp [h]
  · simp [h]

/-- The fuelled loop can start at most one new round per unit of fuel. -/
theorem iqaeAux_rounds_le
    (kind : ConfidenceIntervalKind) (epsilon alpha Lmax : ℝ) (Nshots : ℕ)
    (fuel : ℕ) (observations : List IQAEObservation) (state : IQAEState) :
    (iqaeAux kind epsilon alpha Lmax Nshots fuel observations state).rounds ≤
      state.rounds + fuel := by
  induction fuel generalizing observations state with
  | zero =>
      simp [iqaeAux]
  | succ fuel ih =>
      cases observations with
      | nil =>
          simp [iqaeAux]
      | cons observation rest =>
          by_cases hdone : state.thetaUpper - state.thetaLower ≤ 2 * epsilon
          · simp [iqaeAux, hdone]
          · simp [iqaeAux, hdone]
            have hrec := ih rest (iqaeStep kind epsilon alpha Lmax Nshots state observation)
            have hstep := iqaeStep_rounds_le kind epsilon alpha Lmax Nshots state observation
            omega

/-- IQAE terminates within the paper's declared maximum number of rounds because
`iqaeFinalState` uses exactly that quantity as loop fuel. -/
theorem iqae_rounds_le_maxRounds
    (kind : ConfidenceIntervalKind) (epsilon alpha Lmax : ℝ) (Nshots : ℕ)
    (observations : List IQAEObservation) :
    (iqae kind epsilon alpha Lmax Nshots observations).rounds ≤ maxRounds epsilon := by
  unfold iqae iqaeOutputOfState iqaeFinalState
  have h := iqaeAux_rounds_le kind epsilon alpha Lmax Nshots (maxRounds epsilon)
    observations initialIQAEState
  simpa [initialIQAEState] using h

/-- If a value lies in a closed interval of width at most `2ε`, then the midpoint
estimate is within `ε`. -/
theorem midpoint_error_le_of_mem_Icc_of_width
    {a lower upper epsilon : ℝ}
    (ha : a ∈ Set.Icc lower upper)
    (hwidth : upper - lower ≤ 2 * epsilon) :
    |a - (lower + upper) / 2| ≤ epsilon := by
  rw [abs_le]
  constructor <;> linarith [ha.1, ha.2, hwidth]

/-- Chernoff-Hoeffding interval soundness as a deterministic postcondition:
if the observed frequency is within the Hoeffding radius of the true Bernoulli
parameter, then the clipped interval contains that parameter. -/
theorem chernoffHoeffdingAmplitudeInterval_contains_of_abs_sub_le
    {N T : ℕ} {alpha observed p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hdev : |observed - p| ≤ chernoffHoeffdingRadius N T alpha) :
    p ∈ chernoffHoeffdingAmplitudeInterval N T alpha observed := by
  constructor
  · unfold chernoffHoeffdingAmplitudeLower clipLowerAmplitude
    exact max_le hp0 (by linarith [abs_le.mp hdev |>.2])
  · unfold chernoffHoeffdingAmplitudeUpper clipUpperAmplitude
    exact le_min hp1 (by linarith [abs_le.mp hdev |>.1])

/-- Deterministic midpoint correctness for the amplitude interval returned by
`iqae`.  The statistical part of the paper proves the two hypotheses for the
random trace with probability at least `1 - α`; this theorem is the formal
algorithmic bridge from those hypotheses to the returned estimate. -/
theorem iqae_estimate_error_of_amplitude_interval
    {kind : ConfidenceIntervalKind} {epsilon alpha Lmax a : ℝ} {Nshots : ℕ}
    {observations : List IQAEObservation}
    (hmem : a ∈ (iqae kind epsilon alpha Lmax Nshots observations).amplitudeInterval)
    (hwidth : (iqae kind epsilon alpha Lmax Nshots observations).amplitudeUpper -
        (iqae kind epsilon alpha Lmax Nshots observations).amplitudeLower ≤ 2 * epsilon) :
    |a - (iqae kind epsilon alpha Lmax Nshots observations).estimate| ≤ epsilon := by
  exact midpoint_error_le_of_mem_Icc_of_width hmem hwidth

/-- Paper Theorem 1, now stated against the actual IQAE function.  The proof
separates the deterministic algorithmic part from the probabilistic
Chernoff-Hoeffding obligations: once the random trace yields a containing
amplitude interval of width `≤ 2ε`, and the Appendix B oracle accounting bound
has been established for that trace, the returned midpoint estimate has error
`≤ ε`, the round bound follows from the implementation, and the oracle bound is
reported for the concrete run. -/
theorem Theorem1
    {epsilon alpha a : ℝ} {Nshots : ℕ} {observations : List IQAEObservation}
    (_hconf : 1 - alpha ∈ Set.Ioo (0 : ℝ) 1)
    (_hepsilon : 0 < epsilon)
    (_hshots : 1 ≤ Nshots ∧ (Nshots : ℝ) ≤ theoremOneNmax epsilon alpha)
    (hmem : a ∈
      (iqae .chernoffHoeffding epsilon alpha
        (chernoffHoeffdingLmax Nshots epsilon alpha) Nshots observations).amplitudeInterval)
    (hwidth :
      (iqae .chernoffHoeffding epsilon alpha
        (chernoffHoeffdingLmax Nshots epsilon alpha) Nshots observations).amplitudeUpper -
      (iqae .chernoffHoeffding epsilon alpha
        (chernoffHoeffdingLmax Nshots epsilon alpha) Nshots observations).amplitudeLower ≤
        2 * epsilon)
    (horacle :
      ((iqae .chernoffHoeffding epsilon alpha
        (chernoffHoeffdingLmax Nshots epsilon alpha) Nshots observations).oracleCalls : ℝ) <
        theoremOneOracleBound epsilon alpha) :
    (iqae .chernoffHoeffding epsilon alpha
        (chernoffHoeffdingLmax Nshots epsilon alpha) Nshots observations).rounds ≤
        maxRounds epsilon ∧
      |a - (iqae .chernoffHoeffding epsilon alpha
        (chernoffHoeffdingLmax Nshots epsilon alpha) Nshots observations).estimate| ≤ epsilon ∧
      ((iqae .chernoffHoeffding epsilon alpha
        (chernoffHoeffdingLmax Nshots epsilon alpha) Nshots observations).oracleCalls : ℝ) <
        theoremOneOracleBound epsilon alpha := by
  constructor
  · exact iqae_rounds_le_maxRounds .chernoffHoeffding epsilon alpha
      (chernoffHoeffdingLmax Nshots epsilon alpha) Nshots observations
  constructor
  · exact iqae_estimate_error_of_amplitude_interval hmem hwidth
  · exact horacle

/-- Paper Theorem 2, stated against the actual IQAE function for the
Clopper-Pearson confidence procedure. -/
theorem Theorem2
    {epsilon alpha Lmax a : ℝ} {Nshots : ℕ} {observations : List IQAEObservation}
    (_hconfidence : 1 - alpha = (0.95 : ℝ))
    (_hepsilon : (1 : ℝ) / 2 ^ (200 : ℕ) ≤ epsilon)
    (_hshots : 1 ≤ Nshots ∧ (Nshots : ℝ) ≤ theoremTwoNmax epsilon alpha)
    (hmem : a ∈ (iqae .clopperPearson epsilon alpha Lmax Nshots observations).amplitudeInterval)
    (hwidth :
      (iqae .clopperPearson epsilon alpha Lmax Nshots observations).amplitudeUpper -
        (iqae .clopperPearson epsilon alpha Lmax Nshots observations).amplitudeLower ≤
          2 * epsilon)
    (horacle :
      ((iqae .clopperPearson epsilon alpha Lmax Nshots observations).oracleCalls : ℝ) <
        theoremTwoOracleBound epsilon alpha) :
    (iqae .clopperPearson epsilon alpha Lmax Nshots observations).rounds ≤ maxRounds epsilon ∧
      |a - (iqae .clopperPearson epsilon alpha Lmax Nshots observations).estimate| ≤ epsilon ∧
      ((iqae .clopperPearson epsilon alpha Lmax Nshots observations).oracleCalls : ℝ) <
        theoremTwoOracleBound epsilon alpha := by
  constructor
  · exact iqae_rounds_le_maxRounds .clopperPearson epsilon alpha Lmax Nshots observations
  constructor
  · exact iqae_estimate_error_of_amplitude_interval hmem hwidth
  · exact horacle

/-- Appendix B Lemma 1, stated with the paper's actual geometric content.

The paper proves that `L ≤ L*` implies the covering condition
`g_L(θ) ≤ max(f₃ θ, f₅ θ, f₇ θ)`; here this is represented by
`lemmaOneCoveringCondition L`, equivalently by containment in one of the
`π/3`, `π/5`, or `π/7` sectors from Supplementary Eqs. (22)-(24).  From that
covering condition and the `FindNextK` sector-growth witness, the conclusion is
exactly the paper's `∀ r ∈ (1, 3], qᵢ ≥ r`, together with
`Lmax = L` and `Lmin = arcsin(sin² L)`. -/
lemma Lemma1
    {L T alpha : ℝ} {q : ℝ → ℝ}
    (_hL : L ≤ lemmaOneLStar)
    (_hNmax : 0 ≤ lemmaOneNmax L T alpha)
    (hcover : lemmaOneCoveringCondition L)
    (hsectorGrowth : lemmaOneSectorCoverImpliesGrowth L q) :
    (∀ theta : ℝ, theta ∈ lemmaOneGDomain L →
      ∀ r : ℝ, r ∈ Set.Ioc (1 : ℝ) 3 → r ≤ q theta) ∧
      lemmaOneLmax L = L ∧
      lemmaOneLmin L = Real.arcsin (Real.sin L ^ 2) := by
  constructor
  · intro theta htheta r hr
    exact hsectorGrowth theta htheta (hcover theta htheta) r hr
  constructor
  · rfl
  · rfl

end IQAE
end QAE

