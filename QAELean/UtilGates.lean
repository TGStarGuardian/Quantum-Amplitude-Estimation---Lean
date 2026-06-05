import QAELean.QuantumLibraryBridge
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Exponential

/-!
# Utility quantum gates

This module contains utility gate matrices used by the QAE development,
including the canonical two-dimensional Grover-plane rotation and a small set of
IonQ native gates not already provided by the imported quantum-computing library.
-/

noncomputable section

namespace QAE
namespace Grover

open QuantumComputing
open scoped BigOperators

variable {n : ℕ}


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

/-- IonQ native GPi gate.

IonQ documents `GPi(φ)` as `[[0, exp(2πiφ)], [exp(-2πiφ), 0]]`, where `φ`
is measured in turns. -/
def ionqGPi (phi : ℝ) : Square 2 :=
  fun i j =>
    if i = (0 : Fin 2) ∧ j = (1 : Fin 2) then (Real.fourierChar phi : ℂ)
    else if i = (1 : Fin 2) ∧ j = (0 : Fin 2) then (Real.fourierChar (-phi) : ℂ)
    else 0

/-- IonQ native GPi2 gate.

IonQ documents `GPi2(φ)` as `(1 / sqrt 2) * [[1, -i exp(2πiφ)],
[-i exp(-2πiφ), 1]]`, where `φ` is measured in turns. -/
def ionqGPi2 (phi : ℝ) : Square 2 :=
  fun i j =>
    if i = (0 : Fin 2) ∧ j = (0 : Fin 2) then invSqrt2
    else if i = (0 : Fin 2) ∧ j = (1 : Fin 2) then invSqrt2 * (-Complex.I * (Real.fourierChar phi : ℂ))
    else if i = (1 : Fin 2) ∧ j = (0 : Fin 2) then invSqrt2 * (-Complex.I * (Real.fourierChar (-phi) : ℂ))
    else if i = (1 : Fin 2) ∧ j = (1 : Fin 2) then invSqrt2
    else 0

/-- IonQ virtual Z gate.

IonQ documents `VirtualZ(θ)` as `diag(exp(-iπθ), exp(iπθ))`, with `θ`
measured in turns. This is the standard `Rz (2πθ)` matrix. -/
def ionqVirtualZ (theta : ℝ) : Square 2 :=
  Rz (2 * Real.pi * theta)

/-- IonQ native fully-entangling Mølmer-Sørensen gate for Aria systems.

The basis order is `|00⟩, |01⟩, |10⟩, |11⟩`. Parameters `φ₀` and `φ₁` are
measured in turns. -/
def ionqMS (phi0 phi1 : ℝ) : Square 4 :=
  fun i j =>
    if i = (0 : Fin 4) ∧ j = (0 : Fin 4) then invSqrt2
    else if i = (0 : Fin 4) ∧ j = (3 : Fin 4) then invSqrt2 * (-Complex.I * (Real.fourierChar (phi0 + phi1) : ℂ))
    else if i = (1 : Fin 4) ∧ j = (1 : Fin 4) then invSqrt2
    else if i = (1 : Fin 4) ∧ j = (2 : Fin 4) then invSqrt2 * (-Complex.I * (Real.fourierChar (phi0 - phi1) : ℂ))
    else if i = (2 : Fin 4) ∧ j = (1 : Fin 4) then invSqrt2 * (-Complex.I * (Real.fourierChar (-(phi0 - phi1)) : ℂ))
    else if i = (2 : Fin 4) ∧ j = (2 : Fin 4) then invSqrt2
    else if i = (3 : Fin 4) ∧ j = (0 : Fin 4) then invSqrt2 * (-Complex.I * (Real.fourierChar (-(phi0 + phi1)) : ℂ))
    else if i = (3 : Fin 4) ∧ j = (3 : Fin 4) then invSqrt2
    else 0

/-- IonQ native partially-entangling Mølmer-Sørensen gate.

IonQ's `θ` parameter is measured in turns; `θ = 0.25` gives the fully-entangling
MS gate. -/
def ionqPartialMS (phi0 phi1 theta : ℝ) : Square 4 :=
  fun i j =>
    if i = (0 : Fin 4) ∧ j = (0 : Fin 4) then (Real.cos (Real.pi * theta) : ℂ)
    else if i = (0 : Fin 4) ∧ j = (3 : Fin 4) then -Complex.I * (Real.fourierChar (phi0 + phi1) : ℂ) * (Real.sin (Real.pi * theta) : ℂ)
    else if i = (1 : Fin 4) ∧ j = (1 : Fin 4) then (Real.cos (Real.pi * theta) : ℂ)
    else if i = (1 : Fin 4) ∧ j = (2 : Fin 4) then -Complex.I * (Real.fourierChar (phi0 - phi1) : ℂ) * (Real.sin (Real.pi * theta) : ℂ)
    else if i = (2 : Fin 4) ∧ j = (1 : Fin 4) then -Complex.I * (Real.fourierChar (-(phi0 - phi1)) : ℂ) * (Real.sin (Real.pi * theta) : ℂ)
    else if i = (2 : Fin 4) ∧ j = (2 : Fin 4) then (Real.cos (Real.pi * theta) : ℂ)
    else if i = (3 : Fin 4) ∧ j = (0 : Fin 4) then -Complex.I * (Real.fourierChar (-(phi0 + phi1)) : ℂ) * (Real.sin (Real.pi * theta) : ℂ)
    else if i = (3 : Fin 4) ∧ j = (3 : Fin 4) then (Real.cos (Real.pi * theta) : ℂ)
    else 0

/-- IonQ native ZZ gate for Forte systems.

IonQ documents `ZZ(θ) = exp(-iπθ Z⊗Z)`, with `θ` measured in turns. -/
def ionqZZ (theta : ℝ) : Square 4 :=
  fun i j =>
    if i = j then
      if i = (0 : Fin 4) ∨ i = (3 : Fin 4) then Complex.exp (-(Complex.I * (Real.pi * theta : ℂ)))
      else Complex.exp (Complex.I * (Real.pi * theta : ℂ))
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
