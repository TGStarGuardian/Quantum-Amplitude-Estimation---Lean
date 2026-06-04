import QAELean.IterativeAmplitudeEstimation
import QuantumComputing

/-!
# Bridge to `duckki/quantum-computing-lean`

This file connects the QAE/IQAE theorem-level development to the existing
`QuantumComputing` Lean library.  We use the library's finite-dimensional complex
state vectors, pure-state wrapper, unitarity API, and computational-basis
measurement probabilities.
-/

noncomputable section

namespace QAE
namespace QuantumLibrary

open QuantumComputing

/-- The canonical two-dimensional good/bad state
`cos theta |bad> + sin theta |good>` in the quantum-computing-lean vector API.
Basis index `0` is bad and basis index `1` is good. -/
def qaePlaneVector (theta : ℝ) : Vector 2 :=
  fun i _ => if i = (1 : Fin 2) then (Real.sin theta : ℂ) else (Real.cos theta : ℂ)

/-- The IQAE amplified two-dimensional state after `k` Grover powers. -/
def iqaeAmplifiedPlaneVector (theta : ℝ) (k : ℕ) : Vector 2 :=
  fun i _ =>
    if i = (1 : Fin 2) then
      (Real.sin (((2 * (k : ℝ)) + 1) * theta) : ℂ)
    else
      (Real.cos (((2 * (k : ℝ)) + 1) * theta) : ℂ)

/-- Measuring the good basis state in the canonical QAE plane state gives
`sin^2 theta`. -/
theorem qaePlaneVector_good_probability (theta : ℝ) :
    Measurement.prob (qaePlaneVector theta) (1 : Fin 2) = amplitudeFromAngle theta := by
  unfold Measurement.prob qaePlaneVector amplitudeFromAngle
  simp [-Complex.ofReal_sin, -Complex.ofReal_cos, Complex.normSq_ofReal, sq]

/-- Measuring the good basis state in the IQAE amplified plane state gives the
paper's probability `sin^2((2k+1)theta)`. -/
theorem iqaeAmplifiedPlaneVector_good_probability (theta : ℝ) (k : ℕ) :
    Measurement.prob (iqaeAmplifiedPlaneVector theta k) (1 : Fin 2) =
      IQAE.amplifiedSuccessProbability theta k := by
  unfold Measurement.prob iqaeAmplifiedPlaneVector IQAE.amplifiedSuccessProbability amplitudeFromAngle
  simp [-Complex.ofReal_sin, -Complex.ofReal_cos, Complex.normSq_ofReal, sq]

/-- The canonical QAE plane state is normalized in the quantum-computing-lean
sense. -/
theorem qaePlaneVector_isNormalized (theta : ℝ) :
    Vector.IsNormalized (qaePlaneVector theta) := by
  rw [Vector.IsNormalized]
  ext i j
  fin_cases i
  fin_cases j
  simp [qaePlaneVector, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply,
    -Complex.ofReal_sin, -Complex.ofReal_cos]
  simpa [sq, add_comm] using Complex.cos_sq_add_sin_sq (theta : ℂ)

/-- The IQAE amplified plane state is normalized in the quantum-computing-lean
sense. -/
theorem iqaeAmplifiedPlaneVector_isNormalized (theta : ℝ) (k : ℕ) :
    Vector.IsNormalized (iqaeAmplifiedPlaneVector theta k) := by
  rw [Vector.IsNormalized]
  ext i j
  fin_cases i
  fin_cases j
  simp [iqaeAmplifiedPlaneVector, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply,
    -Complex.ofReal_sin, -Complex.ofReal_cos]
  simpa [sq, add_comm, add_mul, mul_add, mul_comm, mul_left_comm, mul_assoc] using
    Complex.cos_sq_add_sin_sq (((2 * (k : ℂ)) + 1) * (theta : ℂ))

/-- Library theorem: unitary evolution preserves pure-state normalization. -/
theorem unitary_evolution_preserves_normalization {n : ℕ}
    (U : Square n) (hU : Matrix.isUnitary U) (ψ : PureState n) :
    Vector.IsNormalized (PureState.evolve U hU ψ).vector := by
  exact (PureState.evolve U hU ψ).isNormalized

/-- Library theorem specialized to computational-basis measurements: measuring a
normalized state gives a probability mass function summing to one. -/
theorem computational_measurement_total_probability {n : ℕ} {ψ : Vector n}
    (hψ : Vector.IsNormalized ψ) :
    (∑ i : Fin n, Measurement.prob ψ i) = 1 := by
  exact Measurement.sum_prob_of_isNormalized hψ

end QuantumLibrary
end QAE
