# Quantum Amplitude Estimation in Lean

This repository contains a Lean formalization project focused on the Quantum Amplitude Estimation (QAE) algorithm from Brassard, Hoyer, Mosca, and Tapp, *Quantum Amplitude Amplification and Estimation* (`arXiv:quant-ph/0005055`).

The main goal of the project was to define the Quantum Amplitude Estimation algorithm and prove its correctness, following the structure of Theorem 11 and Theorem 12 in the original paper. In the paper, Theorem 11 gives the probability bounds for the phase-estimation distribution, while Theorem 12 uses those bounds to prove the correctness guarantee for amplitude estimation.

## AI assistance disclosure

OpenAI Codex was used to write Lean code according to my instructions.

One part of the proof of Theorem 12 relies on a proof contained in `BHMTK1Tangent.lean`. The key proof idea was suggested by ChatGPT in this chat:

https://chatgpt.com/share/6a1e3e92-6430-8387-8ed3-40c7a2764470

The proof was then written in Lean using Codex.

## Repository structure

The Lean development is contained in the `QAELean/` directory.

### `QuantumAmplitudeEstimation.lean`

Main QAE file. It defines the amplitude associated to an angle, the classical post-processing step of amplitude estimation, the phase-error radius, the Theorem 12 error bound, and the Theorem 12 success-probability expression.

It also contains the analytic Lemma 7-style result converting a phase error into an amplitude error, packages the Theorem 11-style QPE probability bounds, and connects these components to the amplitude-estimation correctness statement.

### `QuantumPhaseEstimation.lean`

Formalizes the QPE machinery needed by QAE. This includes the counting-register dimension `M = 2^m`, the uniform counting-register state, phase states, QFT and inverse-QFT matrices, approximate QPE amplitudes and probabilities, circular phase distance, phase-window predicates, adjacent outcomes, and probability bounds corresponding to the BHMT Theorem 11 analysis.

This file provides the phase-estimation layer on which the QAE correctness proof depends.

### `BHMTK1Tangent.lean`

Contains the real-analysis proof needed for the `k = 1` case in the Theorem 11/Theorem 12 probability bound. In particular, it proves the lower bound for the two-nearest-outcome estimate used to obtain the `8 / π^2` success probability.

The proof uses a tangent/partial-fraction argument and establishes the monotonicity/sign estimates required for the BHMT `k = 1` bound.

### `GroverQPEBridge.lean`

Connects the Grover-plane rotation used in QAE to the phase convention used by the QPE formalization.

It defines the Y-basis eigenstates `|-i⟩` and `|i⟩`, and proves that they are eigenstates of the relevant `Ry` rotation with eigenphases `θ / π` and `-θ / π`.

### `GroverQAESuperposition.lean`

Proves that the initial QAE state decomposes as a superposition of the two Grover-plane eigenstates. It also proves that the QPE pipeline acts linearly on this superposition and that the counting-register marginal distribution is the average of the two corresponding QPE eigenphase distributions.

This file bridges the abstract QPE analysis with the actual initial state used in amplitude estimation.

### `QuantumLibraryBridge.lean`

Provides a small bridge to the imported Lean quantum-computing library. It defines the canonical two-dimensional QAE good/bad state

```lean
cos θ |bad⟩ + sin θ |good⟩
```

using the library's finite-dimensional vector API.

### `RotationGates.lean`

Defines standard one-qubit rotation gates used in the Grover-plane development, including `Rx`, `Ry`, and `Rz`.
