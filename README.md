# QAE formalization in Lean

This project formalizes core correctness statements for quantum amplitude
estimation (QAE), centered on Brassard, Hoyer, Mosca, and Tapp,
*Quantum Amplitude Amplification and Estimation* (`quant-ph/0005055`).

The development uses Lean `v4.29.1` and is pinned to
`duckki/quantum-computing-lean` at commit
`22f7b16c03a3486da550244cee19b94b993d3de8`.

## Scope

The current formalization covers:

- BHMT QAE amplitude post-processing, including `a = sin^2 theta`,
  `sin^2 (pi * y / M)`, the Theorem 12 error bound, and the analytic transfer
  from phase error to amplitude error.
- Approximate quantum phase estimation (QPE) on a finite counting register,
  including exact-grid behavior, the sine-ratio probability formula, and the
  circular-window probability lower bounds used as BHMT Theorem 11.
- A concrete QFT matrix and inverse QFT matrix over the
  `quantum-computing-lean` matrix/vector API, with unitarity and exact
  phase-state behavior proved.
- The paper-level Grover operator, the bad/good decomposition of
  `A|0...0>`, the two Grover eigenphases, and the probability-level bridge from
  the QAE circuit to the two QPE eigenphase distributions.
- BHMT Paper Theorem 12 for the paper-level QAE circuit, including the endpoint
  cases `a = 0` and `a = 1`.
- A lightweight symbolic circuit and architecture layer for gate sets,
  operations, algorithm families, native-gate checks, and simple connectivity
  predicates.

The local Lean sources currently contain no `sorry`, `axiom`, or `admit`.

## Module Map

`QAELean/QuantumAmplitudeEstimation.lean`

- Defines `amplitudeFromAngle`, `estAmpEstimate`, `phaseErrorRadius`,
  `theorem12ErrorBound`, and `theorem12SuccessProbability`.
- Proves the analytic Lemma 7 style bound as `paperLemma7`.
- Proves `theorem12_from_phase_estimation_proved` and
  `estAmp_error_from_phase_estimation_proved`.
- Packages the QPE facts as `QPE.PaperTheorem11`.
- Defines the paper QAE circuit states, output probabilities, bad/good
  projections, paper Grover operator, and paper estimate.
- Proves `Grover.PaperTheorem12`, the paper-level QAE success-probability
  theorem with the expanded BHMT error threshold.

`QAELean/QuantumPhaseEstimation.lean`

- Defines the counting-register dimension `M m = 2^m`, uniform states,
  phase states, QFT and inverse-QFT matrices, and approximate-QPE amplitudes and
  probabilities.
- Defines circular phase windows and their probabilities.
- Proves exact-grid QPE behavior and the sine-ratio probability form.
- Proves QFT matrix unitarity and the core controlled-power phase-kickback
  lemmas used by QAE.
- Proves the BHMT circular-window lower bounds used by Theorem 11.

`QAELean/GroverQPEBridge.lean`

- Defines the two normalized Y-basis eigenstates of the Grover-plane rotation.
- Proves their eigenphase equations for `Ry (4 * theta)` under the QPE phase
  convention.

`QAELean/GroverQAESuperposition.lean`

- Decomposes the initial two-dimensional QAE state into the two Grover
  eigenstates.
- Proves that QPE on this initial state is the corresponding superposition of
  the two QPE eigenphase outputs.
- Derives the counting-register marginal as the average of the two eigenphase
  QPE distributions.

`QAELean/QuantumLibraryBridge.lean`

- Connects the development to `QuantumComputing.Vector`, matrices, and
  computational-basis measurement.
- Defines the canonical two-dimensional good/bad QAE vector used by the Grover
  bridge.

`QAELean/UtilGates.lean`

- Defines utility gate matrices used by the Grover-plane development,
  including `Rx`, `Ry`, `Rz`, and selected IonQ-native gate matrices.

`QAELean/QuantumCircuits.lean`

- Defines symbolic quantum gates, gate arities, one- and two-qubit operations,
  measurements, quantum operations, algorithm families, algorithm results, and
  quantum-computer architecture predicates.

`QAELean/BHMTK1Tangent.lean`

- Contains the real cotangent/tangent analytic support used in the BHMT
  `k = 1` QPE lower-bound proof.

## Dependency Graph

The project includes a generated dependency graph:

- `docs/qae_dependency_graph.html`
- `docs/qae_dependency_graph.json`

Regenerate or serve it with:

```bash
python3 scripts/qae_dependency_graph.py
python3 scripts/qae_dependency_graph.py --serve
```

## Verification

Build the project with:

```bash
lake build
```

The default target is the `QAELean` Lean library declared in `lakefile.lean`.
