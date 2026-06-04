# QAE formalization in Lean

This project formalizes theorem-level contracts for two amplitude-estimation
papers and now uses `duckki/quantum-computing-lean` for finite-dimensional
quantum mechanics semantics:

- Brassard, Hoyer, Mosca, and Tapp, *Quantum Amplitude Amplification and
  Estimation* (`quant-ph/0005055`)
- Grinko, Gacon, Zoufal, and Woerner, *Iterative Quantum Amplitude Estimation*
  (`arXiv:1912.05559`)

The project is pinned to Lean `v4.29.1`, matching the quantum library.

## Canonical QAE

`QAELean/AmplitudeEstimation.lean` includes:

- good/bad amplitude as `a = sin^2 theta`;
- the Grover iterate `Q = -A S0 Ainv Schi`;
- `Est Amp(A, chi, M)` post-processing as `sin^2 (pi * y / M)`;
- Theorem 12's error bound as `theorem12ErrorBound`;
- `theorem12_from_phase_estimation`, proving the QAE error transfer from the
  phase-estimation event and the paper's Lemma 7;
- `count_error_from_estAmp_error`, the approximate-counting reduction `a = t/N`.

## Iterative QAE

`QAELean/IterativeAmplitudeEstimation.lean` includes:

- IQAE's amplified measurement probability
  `sin^2((2k+1) theta)` and its cosine rewrite
  `(1 - cos((4k+2) theta))/2`;
- Algorithm 1's Chernoff-Hoeffding interval construction and a theorem showing
  interval containment from an absolute-error event;
- a finite union-bound theorem for per-round failure probabilities;
- Algorithm 2's `FindNextK` feasibility contract;
- Theorem 1 constants for Chernoff-Hoeffding IQAE;
- Theorem 2 constants for Clopper-Pearson IQAE in its stated numerical regime;
- deterministic midpoint-accuracy theorems for the returned amplitude interval.

## Quantum Library Bridge

`QAELean/QuantumLibraryBridge.lean` connects the QAE/IQAE development to
`duckki/quantum-computing-lean`:

- uses the library's `QuantumComputing.Vector`, `PureState`, `Matrix.isUnitary`,
  `PureState.evolve`, and `Measurement.prob` APIs;
- defines the canonical two-dimensional good/bad QAE vector and the IQAE
  amplified vector;
- proves both vectors are normalized in the library's `Vector.IsNormalized`
  sense;
- proves computational-basis measurement of the good state has probabilities
  `sin^2 theta` and `sin^2((2k+1) theta)`;
- exposes the library facts that unitary evolution preserves normalization and
  normalized computational-basis probabilities sum to one.

This removes the previous local replacement quantum-semantics modules.  The
remaining unproved end-to-end pieces are QPE correctness, executable IQAE loop
termination, `FindNextK` completeness, and deriving the final query-complexity
bounds from executable algorithms rather than theorem certificates.

## Quantum Phase Estimation

`QAELean/QuantumPhaseEstimation.lean` starts the QPE development on top of
`duckki/quantum-computing-lean`:

- defines the phase convention `exp(2*pi*i*x)` and counting-register dimension
  `M = 2^m`;
- defines Fourier-basis vectors and exact computational-basis vectors using the
  library `Vector` type;
- states reusable matrix-level contracts for inverse QFT and the controlled-power
  phase-kickback stage;
- proves exact QPE correctness from those contracts: after inverse QFT the
  counting register is `|y>` and the target eigenstate is unchanged;
- proves the resulting computational-basis measurement probabilities with the
  library measurement API.

The next missing pieces are implementing the QFT matrix and the controlled-power
operator itself, then proving those two contracts rather than assuming them.

## Verification

Run:

```bash
lake build
```

The project currently builds without `sorry`, `axiom`, or `admit` in the local
Lean source files.
