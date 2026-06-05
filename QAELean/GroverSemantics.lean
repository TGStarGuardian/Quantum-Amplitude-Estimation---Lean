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

/-- The standard one-qubit `Ry` gate.

With the common quantum-gate angle convention, this is
`[[cos(θ/2), -sin(θ/2)], [sin(θ/2), cos(θ/2)]]`.  The Grover-plane rotation by
`2θ` used in QAE is therefore `Ry (4 * θ)`. -/
def Ry (theta : ℝ) : Square 2 :=
  fun i j =>
    if i = (0 : Fin 2) ∧ j = (0 : Fin 2) then (Real.cos (theta / 2) : ℂ)
    else if i = (0 : Fin 2) ∧ j = (1 : Fin 2) then (-(Real.sin (theta / 2)) : ℂ)
    else if i = (1 : Fin 2) ∧ j = (0 : Fin 2) then (Real.sin (theta / 2) : ℂ)
    else if i = (1 : Fin 2) ∧ j = (1 : Fin 2) then (Real.cos (theta / 2) : ℂ)
    else 0

/-- The `Ry` gate is unitary. -/
theorem Ry_adjoint_mul_self (theta : ℝ) :
    (Ry theta)† ⬝ Ry theta = I 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ry, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply,
      -Complex.ofReal_sin, -Complex.ofReal_cos]
  · simpa [sq] using Complex.cos_sq_add_sin_sq ((theta : ℂ) / 2)
  · ring
  · ring
  · simpa [sq, add_comm] using Complex.cos_sq_add_sin_sq ((theta : ℂ) / 2)

/-- The `Ry` gate is unitary. -/
theorem Ry_isUnitary (theta : ℝ) : Matrix.isUnitary (Ry theta) := by
  rw [Matrix.isUnitary_iff_adjoint_mul_self]
  exact Ry_adjoint_mul_self theta

/-- One Grover-plane `Ry (4θ)` rotation advances the amplified QAE state from
angle `(2k+1)θ` to `(2k+3)θ`. -/
theorem Ry_step (theta : ℝ) (k : ℕ) :
    Ry (4 * theta) ⬝ QuantumLibrary.iqaeAmplifiedPlaneVector theta k =
      QuantumLibrary.iqaeAmplifiedPlaneVector theta (k + 1) := by
  have hhalf : (4 * theta) / 2 = 2 * theta := by ring
  ext i j
  fin_cases i
  · fin_cases j
    simp [Ry, hhalf, QuantumLibrary.iqaeAmplifiedPlaneVector, Matrix.mul,
      _root_.Matrix.mul_apply]
    have harg : (2 * ((k : ℂ) + 1) + 1) * (theta : ℂ) =
        2 * (theta : ℂ) + ((2 * (k : ℂ) + 1) * (theta : ℂ)) := by ring
    rw [harg, Complex.cos_add]
    ring
  · fin_cases j
    simp [Ry, hhalf, QuantumLibrary.iqaeAmplifiedPlaneVector, Matrix.mul,
      _root_.Matrix.mul_apply]
    have harg : (2 * ((k : ℂ) + 1) + 1) * (theta : ℂ) =
        2 * (theta : ℂ) + ((2 * (k : ℂ) + 1) * (theta : ℂ)) := by ring
    rw [harg, Complex.sin_add]

/-- After `k` Grover-plane `Ry (4θ)` rotations, the initial QAE state has success
amplitude `sin((2k+1)θ)`. -/
theorem Ry_pow_mul_initial (theta : ℝ) :
    ∀ k : ℕ, (Ry (4 * theta)) ^ k ⬝ QuantumLibrary.qaePlaneVector theta =
      QuantumLibrary.iqaeAmplifiedPlaneVector theta k
  | 0 => by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [QuantumLibrary.qaePlaneVector, QuantumLibrary.iqaeAmplifiedPlaneVector]
  | k + 1 => by
      calc
        (Ry (4 * theta)) ^ (k + 1) ⬝ QuantumLibrary.qaePlaneVector theta
            = Ry (4 * theta) ⬝
                ((Ry (4 * theta)) ^ k ⬝ QuantumLibrary.qaePlaneVector theta) := by
              rw [pow_succ']
              change (Ry (4 * theta) * Ry (4 * theta) ^ k) *
                  QuantumLibrary.qaePlaneVector theta =
                Ry (4 * theta) *
                  (Ry (4 * theta) ^ k * QuantumLibrary.qaePlaneVector theta)
              rw [_root_.Matrix.mul_assoc]
        _ = Ry (4 * theta) ⬝ QuantumLibrary.iqaeAmplifiedPlaneVector theta k := by
              rw [Ry_pow_mul_initial theta k]
        _ = QuantumLibrary.iqaeAmplifiedPlaneVector theta (k + 1) :=
              Ry_step theta k

end Grover
end QAE

