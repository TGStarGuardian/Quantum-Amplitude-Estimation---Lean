import QAELean.QuantumLibraryBridge
import Mathlib.Data.Finset.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

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
  [CNOT, CZ, ZZ].toFinset

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

/-- A quantum algorithm implemented on a given quantum computer.

Every one-qubit and two-qubit gate application in the algorithm must use one of
the computer's native gates. -/
structure ImplementedQuantumAlgorithm (computer : QuantumComputer) (Parameters : Type) where
  algorithm : QuantumAlgorithm Parameters (fun _ : Parameters => computer.numQubits)
  usesOnlyNativeGates :
    algorithm.UsesOnlyNativeGates computer.nativeGates

end QAE
