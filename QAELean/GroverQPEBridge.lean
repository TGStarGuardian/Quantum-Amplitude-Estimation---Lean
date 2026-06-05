import QAELean.GroverSemantics
import QAELean.QuantumPhaseEstimation

/-!
# Y-basis eigenstates for QPE

This module connects the canonical `Ry` rotation used by QAE to the phase
convention used by the QPE formalization. It supplies the normalized Y-basis
states `|-i⟩` and `|i⟩`, with eigenphases `θ / π` and `-θ / π` under
`Ry (4 * θ)`.
-/

noncomputable section

namespace QAE
namespace Grover

open QuantumComputing

/-- The Y-basis state `|-i⟩ = (|0⟩ - i|1⟩) / sqrt 2`.
It has eigenphase `θ / π` for `Ry (4 * θ)`. -/
def ketMinusI : Vector 2 :=
  fun i _ => if i = (0 : Fin 2) then invSqrt2 else -Complex.I * invSqrt2

/-- The Y-basis state `|i⟩ = (|0⟩ + i|1⟩) / sqrt 2`.
It has eigenphase `-θ / π` for `Ry (4 * θ)`. -/
def ketPlusI : Vector 2 :=
  fun i _ => if i = (0 : Fin 2) then invSqrt2 else Complex.I * invSqrt2

/-- `ketMinusI` is normalized. -/
theorem ketMinusI_isNormalized : Vector.IsNormalized ketMinusI := by
  rw [Vector.IsNormalized]
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.mul, Matrix.adjoint, ketMinusI, _root_.Matrix.mul_apply,
    Fin.sum_univ_two]
  ring_nf
  rw [Complex.I_sq]
  rw [sq]
  rw [invSqrt2_mul_self]
  norm_num

/-- `ketPlusI` is normalized. -/
theorem ketPlusI_isNormalized : Vector.IsNormalized ketPlusI := by
  rw [Vector.IsNormalized]
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.mul, Matrix.adjoint, ketPlusI, _root_.Matrix.mul_apply,
    Fin.sum_univ_two]
  ring_nf
  rw [Complex.I_sq]
  rw [sq]
  rw [invSqrt2_mul_self]
  norm_num

/-- The Y-basis state `ketMinusI` has QPE eigenphase `θ / π` under `Ry (4 * θ)`. -/
theorem Ry_ketMinusI_eigen (theta : ℝ) :
    Ry (4 * theta) ⬝ ketMinusI =
      (Real.fourierChar (theta / Real.pi) : ℂ) • ketMinusI := by
  have hphase : (Real.fourierChar (theta / Real.pi) : ℂ) =
      Complex.cos (2 * (theta : ℂ)) + Complex.sin (2 * (theta : ℂ)) * Complex.I := by
    rw [Real.fourierChar_apply]
    have harg : ((2 * Real.pi * (theta / Real.pi) : ℝ) : ℂ) * Complex.I =
        (2 * (theta : ℂ)) * Complex.I := by
      field_simp [Real.pi_ne_zero]
      norm_num
    rw [harg]
    exact Complex.exp_mul_I (2 * (theta : ℂ))
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Ry, ketMinusI, Matrix.mul, _root_.Matrix.mul_apply, hphase]
    ring_nf
  · simp [Ry, ketMinusI, Matrix.mul, _root_.Matrix.mul_apply, hphase]
    ring_nf
    simp

/-- The Y-basis state `ketPlusI` has QPE eigenphase `-θ / π` under `Ry (4 * θ)`. -/
theorem Ry_ketPlusI_eigen (theta : ℝ) :
    Ry (4 * theta) ⬝ ketPlusI =
      (Real.fourierChar (-(theta / Real.pi)) : ℂ) • ketPlusI := by
  have hphase : (Real.fourierChar (-(theta / Real.pi)) : ℂ) =
      Complex.cos (2 * (theta : ℂ)) - Complex.sin (2 * (theta : ℂ)) * Complex.I := by
    rw [Real.fourierChar_apply]
    have harg : ((2 * Real.pi * (-(theta / Real.pi)) : ℝ) : ℂ) * Complex.I =
        (-(2 * (theta : ℂ))) * Complex.I := by
      field_simp [Real.pi_ne_zero]
      norm_num
    rw [harg]
    rw [Complex.exp_mul_I]
    simp [Complex.cos_neg, Complex.sin_neg, sub_eq_add_neg]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Ry, ketPlusI, Matrix.mul, _root_.Matrix.mul_apply, hphase]
    rw [sub_eq_add_neg]
    ring_nf
  · simp [Ry, ketPlusI, Matrix.mul, _root_.Matrix.mul_apply, hphase]
    ring_nf
    simp

end Grover
end QAE
