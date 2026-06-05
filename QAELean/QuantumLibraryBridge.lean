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

end QuantumLibrary
end QAE
