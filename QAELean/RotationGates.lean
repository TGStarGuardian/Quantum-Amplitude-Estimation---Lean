import QAELean.QuantumLibraryBridge
import Mathlib.Analysis.Complex.Exponential

/-!
# Rotation quantum gates

This module contains rotation gate matrices used by the QAE development,
including the canonical one-qubit rotations used by the Grover-plane development.
-/

noncomputable section

namespace QAE
namespace Grover

open QuantumComputing

/-- The standard one-qubit `Rx` gate.

With the common quantum-gate angle convention, this is
`[[cos(θ/2), -i sin(θ/2)], [-i sin(θ/2), cos(θ/2)]]`. -/
def Rx (theta : ℝ) : Square 2 :=
  fun i j =>
    if i = (0 : Fin 2) ∧ j = (0 : Fin 2) then (Real.cos (theta / 2) : ℂ)
    else if i = (0 : Fin 2) ∧ j = (1 : Fin 2) then -Complex.I * (Real.sin (theta / 2) : ℂ)
    else if i = (1 : Fin 2) ∧ j = (0 : Fin 2) then -Complex.I * (Real.sin (theta / 2) : ℂ)
    else if i = (1 : Fin 2) ∧ j = (1 : Fin 2) then (Real.cos (theta / 2) : ℂ)
    else 0

/-- The standard one-qubit `Rz` gate.

With angle `θ` in radians, this is `diag(exp(-iθ/2), exp(iθ/2))`. -/
def Rz (theta : ℝ) : Square 2 :=
  fun i j =>
    if i = (0 : Fin 2) ∧ j = (0 : Fin 2) then Complex.exp (-(Complex.I * (theta : ℂ) / 2))
    else if i = (1 : Fin 2) ∧ j = (1 : Fin 2) then Complex.exp (Complex.I * (theta : ℂ) / 2)
    else 0

/-- The standard one-qubit `Ry` gate.

With the common quantum-gate angle convention, this is
`[[cos(θ/2), -sin(θ/2)], [sin(θ/2), cos(θ/2)]]`. -/
def Ry (theta : ℝ) : Square 2 :=
  fun i j =>
    if i = (0 : Fin 2) ∧ j = (0 : Fin 2) then (Real.cos (theta / 2) : ℂ)
    else if i = (0 : Fin 2) ∧ j = (1 : Fin 2) then (-(Real.sin (theta / 2)) : ℂ)
    else if i = (1 : Fin 2) ∧ j = (0 : Fin 2) then (Real.sin (theta / 2) : ℂ)
    else if i = (1 : Fin 2) ∧ j = (1 : Fin 2) then (Real.cos (theta / 2) : ℂ)
    else 0

end Grover
end QAE
