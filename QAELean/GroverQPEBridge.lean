import QAELean.GroverSemantics
import QAELean.QuantumPhaseEstimation

/-!
# Grover-plane eigenstates for QPE

This module connects the canonical two-dimensional Grover rotation to the phase convention used by the QPE formalization.  It supplies normalized eigenvectors
with eigenphases `θ / π` and `-θ / π`.
-/

noncomputable section

namespace QAE
namespace Grover

open QuantumComputing

/-- Normalized eigenvector of the canonical Grover-plane rotation with eigenphase
`θ / π`, i.e. eigenvalue `exp(2iθ)`. -/
def planeEigenPlus : Vector 2 :=
  fun i _ => if i = (0 : Fin 2) then invSqrt2 else -Complex.I * invSqrt2

/-- Normalized eigenvector of the canonical Grover-plane rotation with eigenphase
`-θ / π`, i.e. eigenvalue `exp(-2iθ)`. -/
def planeEigenMinus : Vector 2 :=
  fun i _ => if i = (0 : Fin 2) then invSqrt2 else Complex.I * invSqrt2

/-- The QPE phase convention at `θ / π` is `exp(2iθ)`. -/
theorem phase_theta_over_pi (theta : ℝ) :
    (Real.fourierChar (theta / Real.pi) : ℂ) =
      Complex.cos (2 * (theta : ℂ)) + Complex.sin (2 * (theta : ℂ)) * Complex.I := by
  rw [Real.fourierChar_apply]
  have harg : ((2 * Real.pi * (theta / Real.pi) : ℝ) : ℂ) * Complex.I =
      (2 * (theta : ℂ)) * Complex.I := by
    field_simp [Real.pi_ne_zero]
    norm_num
  rw [harg]
  exact Complex.exp_mul_I (2 * (theta : ℂ))

/-- The QPE phase convention at `-θ / π` is `exp(-2iθ)`. -/
theorem phase_neg_theta_over_pi (theta : ℝ) :
    (Real.fourierChar (-(theta / Real.pi)) : ℂ) =
      Complex.cos (2 * (theta : ℂ)) - Complex.sin (2 * (theta : ℂ)) * Complex.I := by
  rw [Real.fourierChar_apply]
  have harg : ((2 * Real.pi * (-(theta / Real.pi)) : ℝ) : ℂ) * Complex.I =
      (-(2 * (theta : ℂ))) * Complex.I := by
    field_simp [Real.pi_ne_zero]
    norm_num
  rw [harg]
  rw [Complex.exp_mul_I]
  simp [Complex.cos_neg, Complex.sin_neg, sub_eq_add_neg]

/-- `planeEigenPlus` is normalized. -/
theorem planeEigenPlus_isNormalized : Vector.IsNormalized planeEigenPlus := by
  rw [Vector.IsNormalized]
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.mul, Matrix.adjoint, planeEigenPlus, _root_.Matrix.mul_apply,
    Fin.sum_univ_two]
  ring_nf
  rw [Complex.I_sq]
  rw [sq]
  rw [invSqrt2_mul_self]
  norm_num

/-- `planeEigenMinus` is normalized. -/
theorem planeEigenMinus_isNormalized : Vector.IsNormalized planeEigenMinus := by
  rw [Vector.IsNormalized]
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.mul, Matrix.adjoint, planeEigenMinus, _root_.Matrix.mul_apply,
    Fin.sum_univ_two]
  ring_nf
  rw [Complex.I_sq]
  rw [sq]
  rw [invSqrt2_mul_self]
  norm_num

/-- The positive Grover-plane eigenstate has QPE eigenphase `θ / π`. -/
theorem groverPlaneRotation_eigen_plus (theta : ℝ) :
    groverPlaneRotation theta ⬝ planeEigenPlus =
      (Real.fourierChar (theta / Real.pi) : ℂ) • planeEigenPlus := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [groverPlaneRotation, planeEigenPlus, Matrix.mul, _root_.Matrix.mul_apply,
      phase_theta_over_pi]
    ring
  · simp [groverPlaneRotation, planeEigenPlus, Matrix.mul, _root_.Matrix.mul_apply,
      phase_theta_over_pi]
    ring_nf
    simp

/-- The negative Grover-plane eigenstate has QPE eigenphase `-θ / π`. -/
theorem groverPlaneRotation_eigen_minus (theta : ℝ) :
    groverPlaneRotation theta ⬝ planeEigenMinus =
      (Real.fourierChar (-(theta / Real.pi)) : ℂ) • planeEigenMinus := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [groverPlaneRotation, planeEigenMinus, Matrix.mul, _root_.Matrix.mul_apply,
      phase_neg_theta_over_pi]
    rw [sub_eq_add_neg]
    ring
  · simp [groverPlaneRotation, planeEigenMinus, Matrix.mul, _root_.Matrix.mul_apply,
      phase_neg_theta_over_pi]
    ring_nf
    simp

end Grover
end QAE
