import QAELean.QuantumLibraryBridge

/-!
# Matrix semantics for the Grover iterate

This module contains matrix-level Grover facts used by the QAE development,
including generic unitarity helpers and the canonical two-dimensional Grover-plane
rotation.
-/

noncomputable section

namespace QAE
namespace Grover

open QuantumComputing
open scoped BigOperators

variable {n : ℕ}

/-- The adjoint of a unitary matrix is unitary. -/
theorem adjoint_isUnitary {A : Square n} (hA : Matrix.isUnitary A) :
    Matrix.isUnitary A† := by
  rw [Matrix.isUnitary_iff_adjoint_mul_self]
  rw [Matrix.adjoint_adjoint]
  exact (Matrix.isUnitary_iff_mul_adjoint_self A).mp hA

/-- Multiplication by the global phase `-1` preserves unitarity. -/
theorem neg_isUnitary {A : Square n} (hA : Matrix.isUnitary A) :
    Matrix.isUnitary (-A) := by
  rw [Matrix.isUnitary_iff_adjoint_mul_self]
  rw [Matrix.adjoint_neg]
  have h := (Matrix.isUnitary_iff_adjoint_mul_self A).mp hA
  change (-A†) * (-A) = 1
  rw [neg_mul_neg]
  exact h

/-- Rotation by `2θ` on the canonical two-dimensional bad/good QAE plane.  With
basis index `0` as bad and `1` as good, this sends
`cos φ |bad⟩ + sin φ |good⟩` to
`cos (φ + 2θ) |bad⟩ + sin (φ + 2θ) |good⟩`. -/
def groverPlaneRotation (theta : ℝ) : Square 2 :=
  fun i j =>
    if i = (0 : Fin 2) ∧ j = (0 : Fin 2) then (Real.cos (2 * theta) : ℂ)
    else if i = (0 : Fin 2) ∧ j = (1 : Fin 2) then (-(Real.sin (2 * theta)) : ℂ)
    else if i = (1 : Fin 2) ∧ j = (0 : Fin 2) then (Real.sin (2 * theta) : ℂ)
    else if i = (1 : Fin 2) ∧ j = (1 : Fin 2) then (Real.cos (2 * theta) : ℂ)
    else 0

/-- The canonical Grover-plane rotation is unitary. -/
theorem groverPlaneRotation_adjoint_mul_self (theta : ℝ) :
    (groverPlaneRotation theta)† ⬝ groverPlaneRotation theta = I 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [groverPlaneRotation, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply,
      -Complex.ofReal_sin, -Complex.ofReal_cos]
  · simpa [sq] using Complex.cos_sq_add_sin_sq (2 * (theta : ℂ))
  · ring
  · ring
  · simpa [sq, add_comm] using Complex.cos_sq_add_sin_sq (2 * (theta : ℂ))

/-- The canonical Grover-plane rotation is unitary. -/
theorem groverPlaneRotation_isUnitary (theta : ℝ) :
    Matrix.isUnitary (groverPlaneRotation theta) := by
  rw [Matrix.isUnitary_iff_adjoint_mul_self]
  exact groverPlaneRotation_adjoint_mul_self theta

/-- One Grover-plane rotation advances the amplified QAE state from angle
`(2k+1)θ` to `(2k+3)θ`. -/
theorem groverPlaneRotation_step (theta : ℝ) (k : ℕ) :
    groverPlaneRotation theta ⬝ QuantumLibrary.iqaeAmplifiedPlaneVector theta k =
      QuantumLibrary.iqaeAmplifiedPlaneVector theta (k + 1) := by
  ext i j
  fin_cases i
  · fin_cases j
    simp [groverPlaneRotation, QuantumLibrary.iqaeAmplifiedPlaneVector, Matrix.mul,
      _root_.Matrix.mul_apply]
    have harg : (2 * ((k : ℂ) + 1) + 1) * (theta : ℂ) =
        2 * (theta : ℂ) + ((2 * (k : ℂ) + 1) * (theta : ℂ)) := by ring
    rw [harg, Complex.cos_add]
    ring
  · fin_cases j
    simp [groverPlaneRotation, QuantumLibrary.iqaeAmplifiedPlaneVector, Matrix.mul,
      _root_.Matrix.mul_apply]
    have harg : (2 * ((k : ℂ) + 1) + 1) * (theta : ℂ) =
        2 * (theta : ℂ) + ((2 * (k : ℂ) + 1) * (theta : ℂ)) := by ring
    rw [harg, Complex.sin_add]

/-- After `k` canonical Grover-plane rotations, the initial QAE state has success
amplitude `sin((2k+1)θ)`. -/
theorem groverPlaneRotation_pow_mul_initial (theta : ℝ) :
    ∀ k : ℕ, (groverPlaneRotation theta) ^ k ⬝ QuantumLibrary.qaePlaneVector theta =
      QuantumLibrary.iqaeAmplifiedPlaneVector theta k
  | 0 => by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [QuantumLibrary.qaePlaneVector, QuantumLibrary.iqaeAmplifiedPlaneVector]
  | k + 1 => by
      calc
        (groverPlaneRotation theta) ^ (k + 1) ⬝ QuantumLibrary.qaePlaneVector theta
            = groverPlaneRotation theta ⬝
                ((groverPlaneRotation theta) ^ k ⬝ QuantumLibrary.qaePlaneVector theta) := by
              rw [pow_succ']
              change (groverPlaneRotation theta * groverPlaneRotation theta ^ k) *
                  QuantumLibrary.qaePlaneVector theta =
                groverPlaneRotation theta *
                  (groverPlaneRotation theta ^ k * QuantumLibrary.qaePlaneVector theta)
              rw [_root_.Matrix.mul_assoc]
        _ = groverPlaneRotation theta ⬝ QuantumLibrary.iqaeAmplifiedPlaneVector theta k := by
              rw [groverPlaneRotation_pow_mul_initial theta k]
        _ = QuantumLibrary.iqaeAmplifiedPlaneVector theta (k + 1) :=
              groverPlaneRotation_step theta k

end Grover
end QAE

