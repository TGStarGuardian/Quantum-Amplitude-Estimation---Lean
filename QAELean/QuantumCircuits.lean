import QAELean.QuantumLibraryBridge
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

/-!
# Quantum circuits

Basic structures for describing quantum computers and, later, circuits over
their native gate sets.
-/

namespace QAE

open QuantumComputing
open scoped BigOperators

/-- The arity class of a symbolic quantum gate. -/
inductive QuantumGateArity where
  /-- A gate acting on one qubit. -/
  | oneQubit
  /-- A gate acting on two qubits. -/
  | twoQubit
deriving DecidableEq, Repr

/-- Symbolic quantum gates.

These constructors intentionally carry no data; they only identify gate symbols.
The constructor list can be extended as the circuit language grows. -/
inductive QuantumGate where
  /-- Pauli-X gate. -/
  | X
  /-- Pauli-Y gate. -/
  | Y
  /-- Pauli-Z gate. -/
  | Z
  /-- Rotation around the X axis. -/
  | Rx
  /-- Rotation around the Y axis. -/
  | Ry
  /-- Rotation around the Z axis. -/
  | Rz
  /-- Identity gate, conventionally denoted `I`. -/
  | identity
  /-- Phase gate. -/
  | S
  /-- T gate. -/
  | T
  /-- Controlled-NOT gate. -/
  | CNOT
  /-- Controlled-Z gate. -/
  | CZ
  /-- Two-qubit ZZ interaction gate. -/
  | ZZ
  /-- SWAP gate. -/
  | SWAP
deriving DecidableEq, Repr

namespace QuantumGate

/-- The arity class of a symbolic quantum gate. -/
def arity : QuantumGate → QuantumGateArity
  | X => .oneQubit
  | Y => .oneQubit
  | Z => .oneQubit
  | Rx => .oneQubit
  | Ry => .oneQubit
  | Rz => .oneQubit
  | identity => .oneQubit
  | S => .oneQubit
  | T => .oneQubit
  | CNOT => .twoQubit
  | CZ => .twoQubit
  | ZZ => .twoQubit
  | SWAP => .twoQubit

/-- The number of qubits acted on by a symbolic quantum gate. -/
def numQubits (gate : QuantumGate) : ℕ :=
  match gate.arity with
  | .oneQubit => 1
  | .twoQubit => 2

/-- Predicate for one-qubit gates. -/
def IsOneQubit (gate : QuantumGate) : Prop :=
  gate.arity = .oneQubit

/-- Predicate for two-qubit gates. -/
def IsTwoQubit (gate : QuantumGate) : Prop :=
  gate.arity = .twoQubit

/-- The currently known one-qubit gate symbols. -/
def oneQubitGates : Finset QuantumGate :=
  [X, Y, Z, Rx, Ry, Rz, identity, S, T].toFinset

/-- The currently known two-qubit gate symbols. -/
def twoQubitGates : Finset QuantumGate :=
  [CNOT, CZ, ZZ, SWAP].toFinset

end QuantumGate

/-- A one-qubit gate application inside a quantum operation. -/
structure OneQubitOperation (N : ℕ) where
  gate : QuantumGate
  target : Fin N
deriving DecidableEq

namespace OneQubitOperation

/-- Whether a one-qubit operation touches a given qubit. -/
def Touches {N : ℕ} (op : OneQubitOperation N) (q : Fin N) : Prop :=
  op.target = q

end OneQubitOperation

/-- A two-qubit gate application inside a quantum operation.

The two targets are ordered, so a gate applied to `(q0, q1)` is distinct from
the same gate applied to `(q1, q0)`. -/
structure TwoQubitOperation (N : ℕ) where
  gate : QuantumGate
  target0 : Fin N
  target1 : Fin N
deriving DecidableEq

namespace TwoQubitOperation

/-- The ordered pair of targets for a two-qubit operation. -/
def targets {N : ℕ} (op : TwoQubitOperation N) : Fin N × Fin N :=
  (op.target0, op.target1)

/-- Whether a two-qubit operation touches a given qubit. -/
def Touches {N : ℕ} (op : TwoQubitOperation N) (q : Fin N) : Prop :=
  op.target0 = q ∨ op.target1 = q

/-- The closed line interval of physical qubits touched while routing this two-qubit operation. -/
def lineInterval {N : ℕ} (op : TwoQubitOperation N) : Finset (Fin N) :=
  Finset.univ.filter fun q : Fin N =>
    Nat.min op.target0.val op.target1.val ≤ q.val ∧
      q.val ≤ Nat.max op.target0.val op.target1.val

/-- Two routed two-qubit operations have disjoint line intervals. -/
def IntervalDisjoint {N : ℕ} (a b : TwoQubitOperation N) : Prop :=
  Disjoint a.lineInterval b.lineInterval

/-- A set of two-qubit operations whose routed line intervals are pairwise disjoint. -/
def PairwiseIntervalDisjoint {N : ℕ} (ops : Finset (TwoQubitOperation N)) : Prop :=
  ∀ a ∈ ops, ∀ b ∈ ops, a ≠ b → a.IntervalDisjoint b

/-- If an operation touches a qubit, that qubit lies in its routed line interval. -/
theorem touches_mem_lineInterval {N : ℕ} {op : TwoQubitOperation N} {q : Fin N}
    (h : op.Touches q) : q ∈ op.lineInterval := by
  rcases h with rfl | rfl
  · simp [lineInterval]
  · simp [lineInterval]

/-- Every routed line interval contains at least one endpoint. -/
theorem lineInterval_nonempty {N : ℕ} (op : TwoQubitOperation N) : op.lineInterval.Nonempty := by
  exact ⟨op.target0, touches_mem_lineInterval (Or.inl rfl)⟩

/-- `selected` is a largest-cardinality subset of `ops` with pairwise disjoint routing intervals. -/
def IsGreatestIntervalDisjointSubset {N : ℕ}
    (ops selected : Finset (TwoQubitOperation N)) : Prop :=
  selected ⊆ ops ∧
  PairwiseIntervalDisjoint selected ∧
  ∀ candidate, candidate ⊆ ops →
    PairwiseIntervalDisjoint candidate → candidate.card ≤ selected.card

/-- Choose a largest-cardinality subset with pairwise disjoint routing intervals. -/
noncomputable def greatestIntervalDisjointSubset {N : ℕ}
    (ops : Finset (TwoQubitOperation N)) :
    { selected : Finset (TwoQubitOperation N) //
      IsGreatestIntervalDisjointSubset ops selected } := by
  classical
  let candidates := ops.powerset.filter fun candidate => PairwiseIntervalDisjoint candidate
  have hnonempty : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, PairwiseIntervalDisjoint]
  let existsSelected :=
    Finset.exists_max_image candidates (fun candidate => candidate.card) hnonempty
  let selected := Classical.choose existsSelected
  have hselected : selected ∈ candidates := (Classical.choose_spec existsSelected).1
  have hmax : ∀ candidate ∈ candidates, candidate.card ≤ selected.card :=
    (Classical.choose_spec existsSelected).2
  refine ⟨selected, ?_⟩
  have hselectedSpec : selected ⊆ ops ∧ PairwiseIntervalDisjoint selected := by
    simpa [candidates] using hselected
  refine ⟨hselectedSpec.1, hselectedSpec.2, ?_⟩
  intro candidate hcandidateSubset hcandidateDisjoint
  apply hmax
  simp [candidates, hcandidateSubset, hcandidateDisjoint]

end TwoQubitOperation

/-- A one-qubit measurement inside a quantum operation. -/
structure QuantumMeasurement (N : ℕ) where
  target : Fin N
deriving DecidableEq

namespace QuantumMeasurement

/-- Whether a measurement touches a given qubit. -/
def Touches {N : ℕ} (measurement : QuantumMeasurement N) (q : Fin N) : Prop :=
  measurement.target = q

end QuantumMeasurement

/-- A quantum operation on an `N`-qubit register.

The field `qubits` records exactly the non-idle qubits touched by the operation.
One-qubit gate applications, two-qubit gate applications, and measurements are
stored separately. -/
structure QuantumOperation (N : ℕ) where
  qubits : Finset (Fin N)
  oneQubitOps : Finset (OneQubitOperation N)
  twoQubitOps : Finset (TwoQubitOperation N)
  measurements : Finset (QuantumMeasurement N)
  oneQubitOps_are_one :
    ∀ op ∈ oneQubitOps, op.gate.IsOneQubit
  twoQubitOps_are_two :
    ∀ op ∈ twoQubitOps, op.gate.IsTwoQubit
  twoQubit_targets_ne :
    ∀ op ∈ twoQubitOps, op.target0 ≠ op.target1
  qubits_eq_touched :
    ∀ q : Fin N, q ∈ qubits ↔
      (∃ op, op ∈ oneQubitOps ∧ op.Touches q) ∨
      (∃ op, op ∈ twoQubitOps ∧ op.Touches q) ∨
      (∃ measurement, measurement ∈ measurements ∧ measurement.Touches q)
  oneQubitOps_disjoint :
    ∀ a ∈ oneQubitOps, ∀ b ∈ oneQubitOps, a ≠ b → a.target ≠ b.target
  twoQubitOps_disjoint :
    ∀ a ∈ twoQubitOps, ∀ b ∈ twoQubitOps, a ≠ b →
      ∀ q : Fin N, ¬ (a.Touches q ∧ b.Touches q)
  measurements_disjoint :
    ∀ a ∈ measurements, ∀ b ∈ measurements, a ≠ b → a.target ≠ b.target
  oneQubit_twoQubit_disjoint :
    ∀ a ∈ oneQubitOps, ∀ b ∈ twoQubitOps,
      ∀ q : Fin N, ¬ (a.Touches q ∧ b.Touches q)
  oneQubit_measurement_disjoint :
    ∀ a ∈ oneQubitOps, ∀ measurement ∈ measurements,
      ∀ q : Fin N, ¬ (a.Touches q ∧ measurement.Touches q)
  twoQubit_measurement_disjoint :
    ∀ a ∈ twoQubitOps, ∀ measurement ∈ measurements,
      ∀ q : Fin N, ¬ (a.Touches q ∧ measurement.Touches q)

namespace QuantumOperation

/-- Predicate saying that an operation is a terminal full-register measurement.

Such an operation touches every qubit, contains no gate applications, and has a
measurement targeting each qubit. -/
def IsMeasurementOperation {N : ℕ} (op : QuantumOperation N) : Prop :=
  op.qubits = Finset.univ ∧
  op.oneQubitOps = ∅ ∧
  op.twoQubitOps = ∅ ∧
  ∀ q : Fin N, ∃ measurement ∈ op.measurements, measurement.target = q

/-- Predicate saying that every gate application in an operation uses a gate
from the given native gate set. Measurements are not gate applications. -/
def UsesOnlyNativeGates {N : ℕ} (nativeGates : Finset QuantumGate)
    (op : QuantumOperation N) : Prop :=
  (∀ gateOp ∈ op.oneQubitOps, gateOp.gate ∈ nativeGates) ∧
  (∀ gateOp ∈ op.twoQubitOps, gateOp.gate ∈ nativeGates)

/-- Predicate saying that an operation is unitary at this circuit-description
level, i.e. it contains no measurement operations. -/
def IsUnitary {N : ℕ} (op : QuantumOperation N) : Prop :=
  op.measurements = ∅

/-- Build a `QuantumOperation` from already-disjoint component sets.

The touched-qubit set is derived from the supplied components, so callers only
provide the gate-arity and disjointness witnesses for the components themselves. -/
noncomputable def fromComponents {N : ℕ}
    (oneQubitOps : Finset (OneQubitOperation N))
    (twoQubitOps : Finset (TwoQubitOperation N))
    (measurements : Finset (QuantumMeasurement N))
    (hOne : ∀ op ∈ oneQubitOps, op.gate.IsOneQubit)
    (hTwo : ∀ op ∈ twoQubitOps, op.gate.IsTwoQubit)
    (hTwoNe : ∀ op ∈ twoQubitOps, op.target0 ≠ op.target1)
    (hOneDisjoint :
      ∀ a ∈ oneQubitOps, ∀ b ∈ oneQubitOps, a ≠ b → a.target ≠ b.target)
    (hTwoDisjoint :
      ∀ a ∈ twoQubitOps, ∀ b ∈ twoQubitOps, a ≠ b →
        ∀ q : Fin N, ¬ (a.Touches q ∧ b.Touches q))
    (hMeasurementsDisjoint :
      ∀ a ∈ measurements, ∀ b ∈ measurements, a ≠ b → a.target ≠ b.target)
    (hOneTwoDisjoint :
      ∀ a ∈ oneQubitOps, ∀ b ∈ twoQubitOps,
        ∀ q : Fin N, ¬ (a.Touches q ∧ b.Touches q))
    (hOneMeasurementDisjoint :
      ∀ a ∈ oneQubitOps, ∀ measurement ∈ measurements,
        ∀ q : Fin N, ¬ (a.Touches q ∧ measurement.Touches q))
    (hTwoMeasurementDisjoint :
      ∀ a ∈ twoQubitOps, ∀ measurement ∈ measurements,
        ∀ q : Fin N, ¬ (a.Touches q ∧ measurement.Touches q)) :
    QuantumOperation N := by
  classical
  exact {
    qubits := Finset.univ.filter fun q : Fin N =>
      (∃ op, op ∈ oneQubitOps ∧ op.Touches q) ∨
      (∃ op, op ∈ twoQubitOps ∧ op.Touches q) ∨
      (∃ measurement, measurement ∈ measurements ∧ measurement.Touches q)
    oneQubitOps := oneQubitOps
    twoQubitOps := twoQubitOps
    measurements := measurements
    oneQubitOps_are_one := hOne
    twoQubitOps_are_two := hTwo
    twoQubit_targets_ne := hTwoNe
    qubits_eq_touched := by
      intro q
      simp
    oneQubitOps_disjoint := hOneDisjoint
    twoQubitOps_disjoint := hTwoDisjoint
    measurements_disjoint := hMeasurementsDisjoint
    oneQubit_twoQubit_disjoint := hOneTwoDisjoint
    oneQubit_measurement_disjoint := hOneMeasurementDisjoint
    twoQubit_measurement_disjoint := hTwoMeasurementDisjoint
  }

/-- A layer containing exactly one two-qubit gate application. -/
noncomputable def singletonTwoQubit {N : ℕ} (op : TwoQubitOperation N)
    (hgate : op.gate.IsTwoQubit) (hne : op.target0 ≠ op.target1) : QuantumOperation N :=
  fromComponents ∅ {op} ∅
    (by simp)
    (by
      intro a ha
      have haeq : a = op := by simpa using ha
      rw [haeq]
      exact hgate)
    (by
      intro a ha
      have haeq : a = op := by simpa using ha
      rw [haeq]
      exact hne)
    (by simp)
    (by
      intro a ha b hb hab q htouched
      have haeq : a = op := by simpa using ha
      have hbeq : b = op := by simpa using hb
      exact hab (haeq.trans hbeq.symm))
    (by simp)
    (by simp)
    (by simp)
    (by simp)

/-- The layer containing all one-qubit operations from an operation. -/
noncomputable def oneQubitLayer {N : ℕ} (op : QuantumOperation N) : QuantumOperation N :=
  fromComponents op.oneQubitOps ∅ ∅
    op.oneQubitOps_are_one
    (by simp)
    (by simp)
    op.oneQubitOps_disjoint
    (by simp)
    (by simp)
    (by simp)
    (by simp)
    (by simp)

/-- The layer containing all measurements from an operation. -/
noncomputable def measurementLayer {N : ℕ} (op : QuantumOperation N) : QuantumOperation N :=
  fromComponents ∅ ∅ op.measurements
    (by simp)
    (by simp)
    (by simp)
    (by simp)
    (by simp)
    op.measurements_disjoint
    (by simp)
    (by simp)
    (by simp)

/-- Translating a terminal full-register measurement to its measurement layer
preserves the terminal-measurement predicate. -/
theorem measurementLayer_isMeasurementOperation {N : ℕ} {op : QuantumOperation N}
    (hop : op.IsMeasurementOperation) : (measurementLayer op).IsMeasurementOperation := by
  rcases hop with ⟨_hqubits, _hone, _htwo, hmeasurements⟩
  unfold IsMeasurementOperation measurementLayer fromComponents
  constructor
  · ext q
    simp [QuantumMeasurement.Touches]
    exact hmeasurements q
  constructor
  · rfl
  constructor
  · rfl
  · intro q
    exact hmeasurements q

end QuantumOperation

/-- A terminal full-register measurement operation on an `N`-qubit register. -/
abbrev MeasurementOperation (N : ℕ) :=
  { op : QuantumOperation N // op.IsMeasurementOperation }

/-- A quantum algorithm family whose concrete circuit depends on external
parameters.

The parameter value can determine both the number of qubits and the finite list
of operations. Each concrete algorithm instance must end in a full-register
measurement operation. -/
structure QuantumAlgorithm (Parameters : Type) (numQubits : Parameters → ℕ) where
  operations : (parameters : Parameters) → List (QuantumOperation (numQubits parameters))
  endsWithMeasurement :
    ∀ parameters : Parameters,
      ∃ (initOps : List (QuantumOperation (numQubits parameters)))
        (measurement : MeasurementOperation (numQubits parameters)),
        operations parameters = initOps ++ [measurement.val]

/-- A fixed-size quantum algorithm, recovered as a parameterized algorithm with
one trivial parameter. -/
abbrev FixedQuantumAlgorithm (N : ℕ) :=
  QuantumAlgorithm PUnit (fun _ => N)

namespace QuantumAlgorithm

/-- Predicate saying that every gate application in every operation of every
parameter instance uses a gate from the given native gate set. -/
def UsesOnlyNativeGates {Parameters : Type} {numQubits : Parameters → ℕ}
    (nativeGates : Finset QuantumGate)
    (algorithm : QuantumAlgorithm Parameters numQubits) : Prop :=
  ∀ parameters operation,
    operation ∈ algorithm.operations parameters →
      operation.UsesOnlyNativeGates nativeGates

/-- Complexity of a concrete algorithm instance, counted as the number of
operations before its terminal measurement operation. -/
def complexity {Parameters : Type} {numQubits : Parameters → ℕ}
    (algorithm : QuantumAlgorithm Parameters numQubits) (parameters : Parameters) : ℕ :=
  (algorithm.operations parameters).length - 1

/-- Predicate saying that every operation except the terminal measurement is
unitary for every parameter instance. -/
def IsProper {Parameters : Type} {numQubits : Parameters → ℕ}
    (algorithm : QuantumAlgorithm Parameters numQubits) : Prop :=
  ∀ parameters : Parameters,
    ∃ (initOps : List (QuantumOperation (numQubits parameters)))
      (measurement : MeasurementOperation (numQubits parameters)),
      algorithm.operations parameters = initOps ++ [measurement.val] ∧
      ∀ operation ∈ initOps, operation.IsUnitary

end QuantumAlgorithm

/-- Complexity of a concrete quantum algorithm instance, counted as the number
of operations before its terminal measurement operation. -/
def QuantumAlgorithmComplexity {Parameters : Type} {numQubits : Parameters → ℕ}
    (algorithm : QuantumAlgorithm Parameters numQubits) (parameters : Parameters) : ℕ :=
  algorithm.complexity parameters

/-- A computational-basis measurement outcome for an `N`-qubit register. -/
abbrev QuantumMeasurementOutcome (N : ℕ) :=
  Fin (2 ^ N)

/-- A pure quantum state of an `N`-qubit register.

The underlying state is the `quantum-computing-lean` column-vector type, namely
a complex matrix with `2 ^ N` rows and one column.  The normalization field
records the unit-vector condition expected of physical pure states. -/
structure QuantumState (N : ℕ) where
  vector : Vector (2 ^ N)
  isNormalized : Vector.IsNormalized vector

namespace QuantumState

instance {N : ℕ} : Coe (QuantumState N) (Vector (2 ^ N)) where
  coe state := state.vector

/-- The amplitude of a computational-basis outcome in a quantum state. -/
def amplitude {N : ℕ} (state : QuantumState N) (outcome : QuantumMeasurementOutcome N) : ℂ :=
  state.vector outcome 0

/-- The computational-basis probability of an outcome in a quantum state. -/
def outcomeProbability {N : ℕ} (state : QuantumState N)
    (outcome : QuantumMeasurementOutcome N) : ℝ :=
  Measurement.prob state.vector outcome

/-- Computational-basis outcome probabilities of a quantum state sum to one. -/
theorem sum_outcomeProbability {N : ℕ} (state : QuantumState N) :
    (∑ outcome : QuantumMeasurementOutcome N, state.outcomeProbability outcome) = 1 :=
  Measurement.sum_prob_of_isNormalized state.isNormalized

end QuantumState



/-- The probabilistic result of running one concrete parameter instance of a
quantum algorithm.

Mathlib's `PMF` stores the discrete probability mass function on the finite
outcome space for the number of qubits determined by `parameters`. -/
structure QuantumAlgorithmResult {Parameters : Type} {numQubits : Parameters → ℕ}
    (algorithm : QuantumAlgorithm Parameters numQubits) (parameters : Parameters) where
  distribution : PMF (QuantumMeasurementOutcome (numQubits parameters))

namespace QuantumAlgorithmResult

/-- Real-valued probability assigned to a single measurement outcome. -/
noncomputable def outcomeProbability {Parameters : Type} {numQubits : Parameters → ℕ}
    {algorithm : QuantumAlgorithm Parameters numQubits} {parameters : Parameters}
    (result : QuantumAlgorithmResult algorithm parameters) :
    QuantumMeasurementOutcome (numQubits parameters) → ℝ :=
  fun outcome => (result.distribution outcome).toReal

/-- Real-valued probability assigned to a finite event of measurement outcomes. -/
noncomputable def eventProbability {Parameters : Type} {numQubits : Parameters → ℕ}
    {algorithm : QuantumAlgorithm Parameters numQubits} {parameters : Parameters}
    (result : QuantumAlgorithmResult algorithm parameters) :
    Finset (QuantumMeasurementOutcome (numQubits parameters)) → ℝ :=
  fun outcomes => (outcomes.sum fun outcome => result.distribution outcome).toReal

end QuantumAlgorithmResult

/-- A quantum computer with a positive number of qubits, a finite set of
native gates, and an undirected graph describing qubit connectivity.

The graph vertices are `Fin numQubits`, so the graph has exactly one node for
each qubit. Mathlib`s `SimpleGraph` is undirected and loopless. -/
structure QuantumComputer where
  numQubits : ℕ
  numQubits_pos : 0 < numQubits
  nativeGates : Finset QuantumGate
  architecture : SimpleGraph (Fin numQubits)


namespace QuantumComputer

/-- Predicate for a line architecture graph on `N` qubits.

The only edges are between consecutive qubit indices: `0--1--2--...--(N - 1)`. -/
def IsLineArchitectureGraph {N : ℕ} (graph : SimpleGraph (Fin N)) : Prop :=
  ∀ q r : Fin N, graph.Adj q r ↔ q.val + 1 = r.val ∨ r.val + 1 = q.val

/-- Predicate for an all-to-all architecture graph on `N` qubits.

Every pair of distinct qubits is connected. -/
def IsAllToAllGraph {N : ℕ} (graph : SimpleGraph (Fin N)) : Prop :=
  ∀ q r : Fin N, graph.Adj q r ↔ q ≠ r

/-- Predicate saying that a quantum computer has line architecture. -/
def IsLineArchitecture (computer : QuantumComputer) : Prop :=
  IsLineArchitectureGraph computer.architecture

/-- Predicate saying that a quantum computer has all-to-all connectivity. -/
def IsAllToAllConnected (computer : QuantumComputer) : Prop :=
  IsAllToAllGraph computer.architecture

end QuantumComputer

/-- Quantum computers whose qubit connectivity graph is a line. -/
abbrev LineArchitectureQuantumComputer :=
  { computer : QuantumComputer // computer.IsLineArchitecture }

/-- Quantum computers whose qubit connectivity graph is all-to-all connected. -/
abbrev AllToAllQuantumComputer :=
  { computer : QuantumComputer // computer.IsAllToAllConnected }

namespace LineArchitectureTranslation

/-- A routed two-qubit step together with the proofs needed to emit it as part
of a line-architecture `QuantumOperation`.  The `source` field is the original
logical two-qubit operation whose routing interval contains this adjacent step. -/
structure RoutedTwoQubitStep (N : ℕ) where
  source : TwoQubitOperation N
  op : TwoQubitOperation N
  isTwoQubit : op.gate.IsTwoQubit
  targets_ne : op.target0 ≠ op.target1
  interval_subset : op.lineInterval ⊆ source.lineInterval

namespace RoutedTwoQubitStep

/-- Emit a routed two-qubit step as a singleton operation layer. -/
noncomputable def toOperation {N : ℕ} (step : RoutedTwoQubitStep N) : QuantumOperation N :=
  QuantumOperation.singletonTwoQubit step.op step.isTwoQubit step.targets_ne

end RoutedTwoQubitStep

/-- The successor qubit index, when it exists. -/
def finSucc {N : ℕ} (q : Fin N) (h : q.val + 1 < N) : Fin N :=
  ⟨q.val + 1, h⟩

/-- An adjacent SWAP routed across line edge `i--(i+1)`, known to stay inside
`source`'s line interval. -/
def adjacentSwapStep {N : ℕ} (source : TwoQubitOperation N)
    (i : ℕ) (hi : i + 1 < N)
    (hlo : Nat.min source.target0.val source.target1.val ≤ i)
    (hhi : i + 1 ≤ Nat.max source.target0.val source.target1.val) :
    RoutedTwoQubitStep N where
  source := source
  op := {
    gate := .SWAP
    target0 := ⟨i, by omega⟩
    target1 := ⟨i + 1, hi⟩
  }
  isTwoQubit := rfl
  targets_ne := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
  interval_subset := by
    intro q hq
    have hstep : i ≤ q.val ∧ q.val ≤ i + 1 := by
      simpa [TwoQubitOperation.lineInterval, Nat.min_eq_left (Nat.le_succ i),
        Nat.max_eq_right (Nat.le_succ i)] using hq
    rw [TwoQubitOperation.lineInterval]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨le_trans hlo hstep.1, le_trans hstep.2 hhi⟩

/-- SWAP chain moving the state at `right` leftward to physical position
`left + 1`.  The `left`/`right` endpoints are the min/max endpoints of `source`. -/
def moveRightEndpointToSuccChain {N : ℕ} (source : TwoQubitOperation N)
    (left right : Fin N)
    (hmin : Nat.min source.target0.val source.target1.val = left.val)
    (hmax : Nat.max source.target0.val source.target1.val = right.val) :
    List (RoutedTwoQubitStep N) :=
  (((List.range right.val).filter fun i => left.val < i ∧ i < right.val).reverse).attach.map
    fun i =>
      let k := i.val
      have hmem : k ∈ ((List.range right.val).filter fun i => left.val < i ∧ i < right.val).reverse :=
        i.property
      have hbetween : left.val < k ∧ k < right.val := by
        have hmemFilter : k ∈ (List.range right.val).filter fun i => left.val < i ∧ i < right.val := by
          simpa using List.mem_reverse.mp hmem
        exact of_decide_eq_true (List.mem_filter.mp hmemFilter).2
      have hk : k + 1 < N := by
        have hright : right.val < N := right.isLt
        omega
      adjacentSwapStep source k hk
        (by rw [hmin]; exact Nat.le_of_lt hbetween.1)
        (by rw [hmax]; omega)

/-- The original ordered two-qubit gate after routing the right endpoint next to the left endpoint. -/
def routedGateLeftRight {N : ℕ} (source : TwoQubitOperation N)
    (hgate : source.gate.IsTwoQubit) (hleft : source.target0.val < source.target1.val) :
    RoutedTwoQubitStep N where
  source := source
  op := {
    gate := source.gate
    target0 := source.target0
    target1 := finSucc source.target0 (by
      have htarget : source.target1.val < N := source.target1.isLt
      omega)
  }
  isTwoQubit := hgate
  targets_ne := by
    intro h
    have hval := congrArg Fin.val h
    simp [finSucc] at hval
  interval_subset := by
    intro q hq
    have hstep : source.target0.val ≤ q.val ∧ q.val ≤ source.target0.val + 1 := by
      simpa [TwoQubitOperation.lineInterval, finSucc,
        Nat.min_eq_left (Nat.le_succ source.target0.val),
        Nat.max_eq_right (Nat.le_succ source.target0.val)] using hq
    simp [TwoQubitOperation.lineInterval, Nat.min_eq_left (Nat.le_of_lt hleft),
      Nat.max_eq_right (Nat.le_of_lt hleft)]
    omega

/-- The original ordered two-qubit gate after routing the left endpoint next to the right endpoint. -/
def routedGateRightLeft {N : ℕ} (source : TwoQubitOperation N)
    (hgate : source.gate.IsTwoQubit) (hright : source.target1.val < source.target0.val) :
    RoutedTwoQubitStep N where
  source := source
  op := {
    gate := source.gate
    target0 := finSucc source.target1 (by
      have htarget : source.target0.val < N := source.target0.isLt
      omega)
    target1 := source.target1
  }
  isTwoQubit := hgate
  targets_ne := by
    intro h
    have hval := congrArg Fin.val h
    simp [finSucc] at hval
  interval_subset := by
    intro q hq
    have hstep : source.target1.val ≤ q.val ∧ q.val ≤ source.target1.val + 1 := by
      simpa [TwoQubitOperation.lineInterval, finSucc,
        Nat.min_eq_right (Nat.le_succ source.target1.val),
        Nat.max_eq_left (Nat.le_succ source.target1.val)] using hq
    simp [TwoQubitOperation.lineInterval, Nat.min_eq_right (Nat.le_of_lt hright),
      Nat.max_eq_left (Nat.le_of_lt hright)]
    omega

/-- Translate a two-qubit operation into adjacent line steps using a SWAP chain.

If `target0 < target1`, the chain moves `target1` to `target0 + 1`.  If
`target1 < target0`, it moves `target0` to `target1 + 1`, preserving the
ordered arguments of the original two-qubit gate.  In both cases the inverse
SWAP chain is appended by reversing the original chain. -/
def translateTwoQubitOperationSteps {N : ℕ} (source : TwoQubitOperation N)
    (hgate : source.gate.IsTwoQubit) (hne : source.target0 ≠ source.target1) :
    List (RoutedTwoQubitStep N) :=
  if hleft : source.target0.val < source.target1.val then
    let chain := moveRightEndpointToSuccChain source source.target0 source.target1
      (Nat.min_eq_left (Nat.le_of_lt hleft))
      (Nat.max_eq_right (Nat.le_of_lt hleft))
    chain ++ [routedGateLeftRight source hgate hleft] ++ chain.reverse
  else if hright : source.target1.val < source.target0.val then
    let chain := moveRightEndpointToSuccChain source source.target1 source.target0
      (Nat.min_eq_right (Nat.le_of_lt hright))
      (Nat.max_eq_left (Nat.le_of_lt hright))
    chain ++ [routedGateRightLeft source hgate hright] ++ chain.reverse
  else
    [{
      source := source
      op := source
      isTwoQubit := hgate
      targets_ne := hne
      interval_subset := by intro q hq; exact hq
    }]

/-- Translate a single two-qubit operation to singleton `QuantumOperation` layers. -/
noncomputable def translateTwoQubitOperation {N : ℕ} (source : TwoQubitOperation N)
    (hgate : source.gate.IsTwoQubit) (hne : source.target0 ≠ source.target1) :
    List (QuantumOperation N) :=
  (translateTwoQubitOperationSteps source hgate hne).map RoutedTwoQubitStep.toOperation

/-- Keep a step only if its proof-carrying source matches the requested source. -/
def routedStepAt {N : ℕ} (source : TwoQubitOperation N)
    (hgate : source.gate.IsTwoQubit) (hne : source.target0 ≠ source.target1)
    (idx : ℕ) : Option { step : RoutedTwoQubitStep N // step.source = source } :=
  match (translateTwoQubitOperationSteps source hgate hne)[idx]? with
  | none => none
  | some step => if h : step.source = source then some ⟨step, h⟩ else none

/-- Proof-carrying routed steps at one time index, built from a source list
with no duplicate two-qubit operations. -/
structure StepsAtIndexResult {N : ℕ} (sources : List (TwoQubitOperation N)) where
  steps : List (RoutedTwoQubitStep N)
  source_mem : ∀ step ∈ steps, step.source ∈ sources
  unique_source : ∀ a ∈ steps, ∀ b ∈ steps, a.source = b.source → a = b

/-- Build all routed steps present at time index `idx` from a nodup source list. -/
def stepsAtIndexFromSources {N : ℕ} (op : QuantumOperation N) (idx : ℕ) :
    (sources : List (TwoQubitOperation N)) → sources.Nodup →
      (∀ source, source ∈ sources → source ∈ op.twoQubitOps) →
      StepsAtIndexResult sources
  | [], _hnodup, _hmem => {
      steps := []
      source_mem := by simp
      unique_source := by simp
    }
  | source :: rest, hnodup, hmem =>
      let restResult := stepsAtIndexFromSources op idx rest hnodup.of_cons
        (by
          intro restSource hrestSource
          exact hmem restSource (List.mem_cons_of_mem source hrestSource))
      let step? := routedStepAt source
        (op.twoQubitOps_are_two source (hmem source (by simp)))
        (op.twoQubit_targets_ne source (hmem source (by simp)))
        idx
      match hstep? : step? with
      | none => {
          steps := restResult.steps
          source_mem := by
            intro step hstep
            exact List.mem_cons_of_mem source (restResult.source_mem step hstep)
          unique_source := restResult.unique_source
        }
      | some packedStep => {
          steps := packedStep.val :: restResult.steps
          source_mem := by
            intro step hstep
            simp at hstep
            rcases hstep with rfl | hstepRest
            · rw [packedStep.property]
              simp
            · exact List.mem_cons_of_mem source (restResult.source_mem step hstepRest)
          unique_source := by
            intro a ha b hb hsrc
            simp at ha hb
            rcases ha with rfl | haRest
            · rcases hb with rfl | hbRest
              · rfl
              · have hbSourceMem := restResult.source_mem b hbRest
                have hbSourceEq : b.source = source := hsrc.symm.trans packedStep.property
                rw [hbSourceEq] at hbSourceMem
                exact False.elim (hnodup.notMem hbSourceMem)
            · rcases hb with rfl | hbRest
              · have haSourceMem := restResult.source_mem a haRest
                have haSourceEq : a.source = source := hsrc.trans packedStep.property
                rw [haSourceEq] at haSourceMem
                exact False.elim (hnodup.notMem haSourceMem)
              · exact restResult.unique_source a haRest b hbRest hsrc
        }

/-- The routed steps present at time index `idx` for a selected maximum-disjoint batch. -/
noncomputable def stepsAtIndexResult {N : ℕ} (op : QuantumOperation N)
    (selected : Finset (TwoQubitOperation N)) (hselected : selected ⊆ op.twoQubitOps)
    (idx : ℕ) : StepsAtIndexResult selected.toList :=
  stepsAtIndexFromSources op idx selected.toList selected.nodup_toList
    (by
      intro source hsource
      exact hselected (by simpa using hsource))

/-- A layer containing the time-indexed routed steps from one maximum-disjoint batch. -/
noncomputable def routedStepLayer {N : ℕ}
    (selected : Finset (TwoQubitOperation N))
    (hselectedDisjoint : TwoQubitOperation.PairwiseIntervalDisjoint selected)
    (steps : List (RoutedTwoQubitStep N))
    (hsource : ∀ step ∈ steps, step.source ∈ selected)
    (huniqueSource : ∀ a ∈ steps, ∀ b ∈ steps, a.source = b.source → a = b) :
    QuantumOperation N :=
  QuantumOperation.fromComponents ∅ (steps.map (fun step => step.op)).toFinset ∅
    (by simp)
    (by
      intro routedOp hroutedOp
      simp at hroutedOp
      rcases hroutedOp with ⟨step, hstep, rfl⟩
      exact step.isTwoQubit)
    (by
      intro routedOp hroutedOp
      simp at hroutedOp
      rcases hroutedOp with ⟨step, hstep, rfl⟩
      exact step.targets_ne)
    (by simp)
    (by
      intro a ha b hb hab q htouched
      simp at ha hb
      rcases ha with ⟨stepA, hstepA, rfl⟩
      rcases hb with ⟨stepB, hstepB, rfl⟩
      by_cases hsrc : stepA.source = stepB.source
      · have hstepEq := huniqueSource stepA hstepA stepB hstepB hsrc
        subst hstepEq
        exact hab rfl
      · have hintervalDisjoint :=
          hselectedDisjoint stepA.source (hsource stepA hstepA)
            stepB.source (hsource stepB hstepB) hsrc
        have hqa : q ∈ stepA.source.lineInterval :=
          stepA.interval_subset (TwoQubitOperation.touches_mem_lineInterval htouched.1)
        have hqb : q ∈ stepB.source.lineInterval :=
          stepB.interval_subset (TwoQubitOperation.touches_mem_lineInterval htouched.2)
        exact (Finset.disjoint_left.mp hintervalDisjoint hqa hqb))
    (by simp)
    (by simp)
    (by simp)
    (by simp)

/-- Merge the separately routed lists of one selected maximum-disjoint batch by
time index: all first steps form the first `QuantumOperation`, all second steps
form the next, and so on until the line-routing depth bound is exhausted. -/
noncomputable def routeSelectedBatch {N : ℕ} (op : QuantumOperation N)
    (selected : Finset (TwoQubitOperation N)) (hselected : selected ⊆ op.twoQubitOps)
    (hselectedDisjoint : TwoQubitOperation.PairwiseIntervalDisjoint selected) :
    List (QuantumOperation N) :=
  (List.range (2 * N + 1)).filterMap fun idx =>
    let result := stepsAtIndexResult op selected hselected idx
    if hsteps : result.steps = [] then
      none
    else
      some (routedStepLayer selected hselectedDisjoint result.steps
        (by
          intro step hstep
          have hsourceList := result.source_mem step hstep
          simpa using hsourceList)
        result.unique_source)

/-- Auxiliary maximum-disjoint-interval scheduler for all remaining two-qubit operations. -/
noncomputable def translateTwoQubitOperationsAux {N : ℕ} (op : QuantumOperation N) :
    ℕ → (remaining : Finset (TwoQubitOperation N)) → remaining ⊆ op.twoQubitOps →
      List (QuantumOperation N)
  | 0, _remaining, _hremaining => []
  | fuel + 1, remaining, hremaining =>
      if hremainingEmpty : remaining = ∅ then
        []
      else
        let selectedWithProof := TwoQubitOperation.greatestIntervalDisjointSubset remaining
        let selected := selectedWithProof.val
        have hselectedSubsetRemaining : selected ⊆ remaining := selectedWithProof.property.1
        have hselectedSubsetOriginal : selected ⊆ op.twoQubitOps := by
          intro routedOp hroutedOp
          exact hremaining (hselectedSubsetRemaining hroutedOp)
        have hselectedDisjoint : TwoQubitOperation.PairwiseIntervalDisjoint selected :=
          selectedWithProof.property.2.1
        have hnextRemaining : remaining \ selected ⊆ op.twoQubitOps := by
          intro routedOp hroutedOp
          exact hremaining (Finset.mem_sdiff.mp hroutedOp).1
        routeSelectedBatch op selected hselectedSubsetOriginal hselectedDisjoint ++
          translateTwoQubitOperationsAux op fuel (remaining \ selected) hnextRemaining

/-- Translate all two-qubit operations by repeatedly selecting a largest-cardinality
set of disjoint routing intervals, routing each selected operation separately,
and merging the selected routed lists by time index. -/
noncomputable def translateTwoQubitOperations {N : ℕ} (op : QuantumOperation N) :
    List (QuantumOperation N) :=
  translateTwoQubitOperationsAux op op.twoQubitOps.card op.twoQubitOps (by intro routedOp hroutedOp; exact hroutedOp)

/-- Translate one symbolic operation to operations compatible with a line architecture.

Two-qubit operations are routed in maximum-disjoint-interval batches first.  The
original one-qubit operations are then emitted as one layer, followed by the
original measurements as one layer. -/
noncomputable def translateOperation {N : ℕ} (op : QuantumOperation N) :
    List (QuantumOperation N) :=
  translateTwoQubitOperations op ++
    [QuantumOperation.oneQubitLayer op, QuantumOperation.measurementLayer op]

/-- Total number of two-qubit gate applications in a list of operations. -/
def totalTwoQubitOps {N : ℕ} : List (QuantumOperation N) → ℕ
  | [] => 0
  | operation :: operations => operation.twoQubitOps.card + totalTwoQubitOps operations

/-- Translate a list of operations by translating each operation and concatenating
the resulting lists. -/
noncomputable def translateOperations {N : ℕ} :
    List (QuantumOperation N) → List (QuantumOperation N)
  | [] => []
  | operation :: operations => translateOperation operation ++ translateOperations operations

@[simp]
theorem translateOperations_append {N : ℕ}
    (left right : List (QuantumOperation N)) :
    translateOperations (left ++ right) = translateOperations left ++ translateOperations right := by
  induction left with
  | nil => rfl
  | cons operation operations ih =>
      simp [translateOperations, ih, List.append_assoc]

/-- A routed maximum-disjoint batch emits at most the fixed per-batch depth. -/
theorem routeSelectedBatch_length_le {N : ℕ} (op : QuantumOperation N)
    (selected : Finset (TwoQubitOperation N)) (hselected : selected ⊆ op.twoQubitOps)
    (hselectedDisjoint : TwoQubitOperation.PairwiseIntervalDisjoint selected) :
    (routeSelectedBatch op selected hselected hselectedDisjoint).length ≤ (2 * N + 1) := by
  unfold routeSelectedBatch
  grind

/-- The auxiliary two-qubit scheduler emits at most one batch-depth worth of
layers per unit of scheduler fuel. -/
theorem translateTwoQubitOperationsAux_length_le {N : ℕ} (op : QuantumOperation N)
    (fuel : ℕ) (remaining : Finset (TwoQubitOperation N))
    (hremaining : remaining ⊆ op.twoQubitOps) :
    (translateTwoQubitOperationsAux op fuel remaining hremaining).length ≤
      fuel * (2 * N + 1) := by
  induction fuel generalizing remaining with
  | zero =>
      simp [translateTwoQubitOperationsAux]
  | succ fuel ih =>
      rw [translateTwoQubitOperationsAux]
      split
      · simp
      · simp only [List.length_append]
        apply le_trans
        · apply Nat.add_le_add
          · apply routeSelectedBatch_length_le
          · apply ih
        · rw [Nat.succ_mul]
          nlinarith

/-- The translated two-qubit part of one operation is bounded by the number of
its two-qubit gates times the line-routing batch depth. -/
theorem translateTwoQubitOperations_length_le {N : ℕ} (op : QuantumOperation N) :
    (translateTwoQubitOperations op).length ≤ op.twoQubitOps.card * (2 * N + 1) := by
  unfold translateTwoQubitOperations
  exact translateTwoQubitOperationsAux_length_le op op.twoQubitOps.card op.twoQubitOps
    (by intro routedOp hroutedOp; exact hroutedOp)

/-- Translating one operation adds at most two extra layers beyond its routed
two-qubit part: one one-qubit layer and one measurement layer. -/
theorem translateOperation_length_le {N : ℕ} (op : QuantumOperation N) :
    (translateOperation op).length ≤ op.twoQubitOps.card * (2 * N + 1) + 2 := by
  unfold translateOperation
  simp only [List.length_append, List.length_cons, List.length_nil]
  exact Nat.add_le_add_right (translateTwoQubitOperations_length_le op) 2

/-- Translating a list of operations is bounded by the total number of two-qubit
gates times the line-routing batch depth, plus two administrative layers per
original operation. -/
theorem translateOperations_length_le {N : ℕ} (operations : List (QuantumOperation N)) :
    (translateOperations operations).length ≤
      totalTwoQubitOps operations * (2 * N + 1) + 2 * operations.length := by
  induction operations with
  | nil =>
      simp [translateOperations, totalTwoQubitOps]
  | cons operation operations ih =>
      simp only [translateOperations, totalTwoQubitOps, List.length_append, List.length_cons]
      have hop := translateOperation_length_le operation
      have hsum := Nat.add_le_add hop ih
      apply le_trans hsum
      rw [Nat.add_mul]
      omega

/-- Translate every operation in a quantum algorithm to line-architecture layers,
concatenating the translated operation lists into one operation list. -/
noncomputable def translateAlgorithm {Parameters : Type} {numQubits : Parameters → ℕ}
    (algorithm : QuantumAlgorithm Parameters numQubits) :
    QuantumAlgorithm Parameters numQubits where
  operations parameters := translateOperations (algorithm.operations parameters)
  endsWithMeasurement := by
    intro parameters
    obtain ⟨initOps, measurement, hoperations⟩ := algorithm.endsWithMeasurement parameters
    let translatedMeasurement : MeasurementOperation (numQubits parameters) :=
      ⟨QuantumOperation.measurementLayer measurement.val,
        QuantumOperation.measurementLayer_isMeasurementOperation measurement.property⟩
    refine ⟨translateOperations initOps ++ [QuantumOperation.oneQubitLayer measurement.val],
      translatedMeasurement, ?_⟩
    have htwo : measurement.val.twoQubitOps = ∅ := measurement.property.2.2.1
    simp [hoperations, translateOperations, translateOperation, translateTwoQubitOperations,
      translateTwoQubitOperationsAux, htwo, translatedMeasurement, List.append_assoc]

/-- Length bound for a translated concrete algorithm instance. -/
theorem translateAlgorithm_operations_length_le {Parameters : Type} {numQubits : Parameters → ℕ}
    (algorithm : QuantumAlgorithm Parameters numQubits) (parameters : Parameters) :
    ((translateAlgorithm algorithm).operations parameters).length ≤
      totalTwoQubitOps (algorithm.operations parameters) * (2 * numQubits parameters + 1) +
        2 * (algorithm.operations parameters).length := by
  exact translateOperations_length_le (algorithm.operations parameters)

/-- Translation specialized to a concrete line-architecture quantum computer. -/
noncomputable def translateOperationOnComputer
    (computer : LineArchitectureQuantumComputer)
    (op : QuantumOperation computer.val.numQubits) :
    List (QuantumOperation computer.val.numQubits) :=
  translateOperation op

/-- Algorithm translation specialized to a concrete line-architecture quantum computer. -/
noncomputable def translateAlgorithmOnComputer
    (computer : LineArchitectureQuantumComputer) {Parameters : Type}
    (algorithm : QuantumAlgorithm Parameters (fun _ : Parameters => computer.val.numQubits)) :
    QuantumAlgorithm Parameters (fun _ : Parameters => computer.val.numQubits) :=
  translateAlgorithm algorithm

end LineArchitectureTranslation

/-- A semantic interpretation of symbolic gate names as concrete one- and
two-qubit matrices.  Rotation symbols in `QuantumGate` carry no angle, so the
angle choices belong in this interpretation rather than in the bare syntax. -/
structure QuantumGateInterpretation where
  oneQubitMatrix : (gate : QuantumGate) → gate.IsOneQubit → Square 2
  twoQubitMatrix : (gate : QuantumGate) → gate.IsTwoQubit → Square 4

namespace QuantumGateInterpretation

/-- Bit of a computational-basis index at qubit position `q`. -/
def basisBit {N : ℕ} (basis : Fin (2 ^ N)) (q : Fin N) : Bool :=
  basis.val.testBit q.val

/-- The one-qubit local basis index extracted from an `N`-qubit basis index. -/
def oneQubitLocalIndex {N : ℕ} (basis : Fin (2 ^ N)) (q : Fin N) : Fin 2 :=
  if basisBit basis q then 1 else 0

/-- The ordered two-qubit local basis index extracted from an `N`-qubit basis index.

The first qubit is the high bit and the second qubit is the low bit, so the
local basis order is `|00⟩, |01⟩, |10⟩, |11⟩`. -/
def twoQubitLocalIndex {N : ℕ} (basis : Fin (2 ^ N)) (q0 q1 : Fin N) : Fin 4 :=
  match basisBit basis q0, basisBit basis q1 with
  | false, false => 0
  | false, true => 1
  | true, false => 2
  | true, true => 3

/-- Two computational-basis indices agree away from target qubit `q`. -/
def SameExceptOne {N : ℕ} (row col : Fin (2 ^ N)) (q : Fin N) : Prop :=
  ∀ r : Fin N, r ≠ q → basisBit row r = basisBit col r

/-- Two computational-basis indices agree away from target qubits `q0` and `q1`. -/
def SameExceptTwo {N : ℕ} (row col : Fin (2 ^ N)) (q0 q1 : Fin N) : Prop :=
  ∀ r : Fin N, r ≠ q0 → r ≠ q1 → basisBit row r = basisBit col r

/-- Lift a one-qubit matrix to an `N`-qubit operator on target `q`. -/
noncomputable def liftOneQubit {N : ℕ} (A : Square 2) (q : Fin N) : Square (2 ^ N) := by
  classical
  exact fun row col =>
    if SameExceptOne row col q then
      A (oneQubitLocalIndex row q) (oneQubitLocalIndex col q)
    else 0

/-- Lift an ordered two-qubit matrix to an `N`-qubit operator on targets
`q0, q1`.  The order matters: swapping `q0` and `q1` changes the local basis
indexing for non-symmetric gates such as CNOT. -/
noncomputable def liftTwoQubit {N : ℕ} (A : Square 4) (q0 q1 : Fin N) : Square (2 ^ N) := by
  classical
  exact fun row col =>
    if SameExceptTwo row col q0 q1 then
      A (twoQubitLocalIndex row q0 q1) (twoQubitLocalIndex col q0 q1)
    else 0

/-- Apply one interpreted one-qubit gate to a state vector. -/
noncomputable def applyOneQubitOperationVector {N : ℕ} (interp : QuantumGateInterpretation)
    (op : OneQubitOperation N) (hgate : op.gate.IsOneQubit)
    (state : Vector (2 ^ N)) : Vector (2 ^ N) :=
  liftOneQubit (interp.oneQubitMatrix op.gate hgate) op.target ⬝ state

/-- Apply one interpreted two-qubit gate to a state vector.  This definition is
intended for adjacent targets in line-architecture layers; non-adjacent gates
are handled by translating the operation first. -/
noncomputable def applyTwoQubitOperationVector {N : ℕ} (interp : QuantumGateInterpretation)
    (op : TwoQubitOperation N) (hgate : op.gate.IsTwoQubit)
    (state : Vector (2 ^ N)) : Vector (2 ^ N) :=
  liftTwoQubit (interp.twoQubitMatrix op.gate hgate) op.target0 op.target1 ⬝ state

/-- Apply all one-qubit gates in a layer.  The operation invariant guarantees
that these targets are disjoint, so the fold order is only a deterministic
presentation choice. -/
noncomputable def applyOneQubitLayerVector {N : ℕ} (interp : QuantumGateInterpretation)
    (op : QuantumOperation N) (state : Vector (2 ^ N)) : Vector (2 ^ N) :=
  op.oneQubitOps.attach.toList.foldl
    (fun state gateOp =>
      applyOneQubitOperationVector interp gateOp.val
        (op.oneQubitOps_are_one gateOp.val gateOp.property) state)
    state

/-- Apply all two-qubit gates in a line-architecture layer.  The operation
invariant guarantees disjoint target qubits, so the fold order is only a
deterministic presentation choice. -/
noncomputable def applyTwoQubitLayerVector {N : ℕ} (interp : QuantumGateInterpretation)
    (op : QuantumOperation N) (state : Vector (2 ^ N)) : Vector (2 ^ N) :=
  op.twoQubitOps.attach.toList.foldl
    (fun state gateOp =>
      applyTwoQubitOperationVector interp gateOp.val
        (op.twoQubitOps_are_two gateOp.val gateOp.property) state)
    state

/-- Apply one line-architecture unitary layer to a state vector.  Measurements
are intentionally ignored here; callers should use this only for operations
satisfying `QuantumOperation.IsUnitary`. -/
noncomputable def applyLineOperationVector {N : ℕ} (interp : QuantumGateInterpretation)
    (op : QuantumOperation N) (state : Vector (2 ^ N)) : Vector (2 ^ N) :=
  applyTwoQubitLayerVector interp op (applyOneQubitLayerVector interp op state)

/-- A unitary quantum operation, i.e. one with no measurements. -/
abbrev UnitaryQuantumOperation (N : ℕ) :=
  { op : QuantumOperation N // op.IsUnitary }

/-- Apply a unitary operation to a vector by first routing its two-qubit gates to
line-architecture layers and then applying each routed line layer. -/
noncomputable def applyUnitaryOperationVector {N : ℕ} (interp : QuantumGateInterpretation)
    (op : UnitaryQuantumOperation N) (state : Vector (2 ^ N)) : Vector (2 ^ N) :=
  LineArchitectureTranslation.translateOperation op.val |>.foldl
    (fun state layer => applyLineOperationVector interp layer state)
    state

/-- Predicate saying the interpreted operation preserves normalization.  This is
separated from the vector semantics because proving lifted arbitrary-position
gate matrices unitary is a separate theorem layer. -/
def PreservesNormalization {N : ℕ} (interp : QuantumGateInterpretation)
    (op : UnitaryQuantumOperation N) : Prop :=
  ∀ state : QuantumState N,
    Vector.IsNormalized (applyUnitaryOperationVector interp op state.vector)

/-- Apply a unitary operation to a bundled quantum state, assuming the chosen
gate interpretation preserves normalization for this operation. -/
noncomputable def applyUnitaryOperation {N : ℕ} (interp : QuantumGateInterpretation)
    (op : UnitaryQuantumOperation N) (hpreserves : PreservesNormalization interp op)
    (state : QuantumState N) : QuantumState N where
  vector := applyUnitaryOperationVector interp op state.vector
  isNormalized := hpreserves state

/-- A convenient interpretation using the included `QuantumComputing` matrices
where the symbolic gate carries enough information.  The remaining matrices are
parameters because the corresponding symbols in `QuantumGate` carry no angle
(`Rx`, `Ry`, `Rz`) or are project-specific choices (`Y`, `S`, `T`, `ZZ`). -/
noncomputable def libraryBackedInterpretation
    (Y Rx Ry Rz S T : Square 2) (ZZ : Square 4) : QuantumGateInterpretation where
  oneQubitMatrix gate _ :=
    match gate with
    | .X => _root_.QuantumComputing.X
    | .Y => Y
    | .Z => _root_.QuantumComputing.Z
    | .Rx => Rx
    | .Ry => Ry
    | .Rz => Rz
    | .identity => I 2
    | .S => S
    | .T => T
    | .CNOT => I 2
    | .CZ => I 2
    | .ZZ => I 2
    | .SWAP => I 2
  twoQubitMatrix gate _ :=
    match gate with
    | .CNOT => _root_.QuantumComputing.CNOT
    | .CZ => _root_.QuantumComputing.CZ
    | .ZZ => ZZ
    | .SWAP => _root_.QuantumComputing.SWAP
    | .X => I 4
    | .Y => I 4
    | .Z => I 4
    | .Rx => I 4
    | .Ry => I 4
    | .Rz => I 4
    | .identity => I 4
    | .S => I 4
    | .T => I 4

end QuantumGateInterpretation

/-- A quantum algorithm implemented on a given quantum computer.

Every one-qubit and two-qubit gate application in the algorithm must use one of
the computer's native gates. -/
structure ImplementedQuantumAlgorithm (computer : QuantumComputer) (Parameters : Type) where
  algorithm : QuantumAlgorithm Parameters (fun _ : Parameters => computer.numQubits)
  usesOnlyNativeGates :
    algorithm.UsesOnlyNativeGates computer.nativeGates

end QAE
