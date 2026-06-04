import QAELean.GroverQPEBridge

/-!
# QPE on the QAE initial Grover-plane state

This module proves the next bridge needed for QAE correctness: the initial
amplitude-estimation state is a linear combination of the two Grover eigenstates,
and the concrete QPE pipeline acts linearly on that superposition.
-/

noncomputable section

namespace QAE
namespace Grover

open QuantumComputing

/-- Coefficient of the positive Grover-plane eigenstate in the initial QAE state. -/
def qaeCoeffPlus (theta : ℝ) : ℂ :=
  invSqrt2 * ((Real.cos theta : ℂ) + (Real.sin theta : ℂ) * Complex.I)

/-- Coefficient of the negative Grover-plane eigenstate in the initial QAE state. -/
def qaeCoeffMinus (theta : ℝ) : ℂ :=
  invSqrt2 * ((Real.cos theta : ℂ) - (Real.sin theta : ℂ) * Complex.I)

/-- The positive eigenstate coefficient has squared norm `1 / 2`. -/
theorem qaeCoeffPlus_normSq (theta : ℝ) :
    Complex.normSq (qaeCoeffPlus theta) = (1 / 2 : ℝ) := by
  unfold qaeCoeffPlus
  rw [Complex.normSq_mul]
  rw [normSq_invSqrt2]
  have hunit :
      Complex.normSq ((Real.cos theta : ℂ) + (Real.sin theta : ℂ) * Complex.I) = 1 := by
    have h := congrArg (fun r : ℝ => r ^ 2) (Complex.norm_cos_add_sin_mul_I theta)
    set_option linter.unnecessarySimpa false in
      simpa [Complex.normSq_eq_norm_sq] using h
  rw [hunit]
  norm_num

/-- The negative eigenstate coefficient has squared norm `1 / 2`. -/
theorem qaeCoeffMinus_normSq (theta : ℝ) :
    Complex.normSq (qaeCoeffMinus theta) = (1 / 2 : ℝ) := by
  unfold qaeCoeffMinus
  rw [Complex.normSq_mul]
  rw [normSq_invSqrt2]
  have hunit :
      Complex.normSq ((Real.cos theta : ℂ) - (Real.sin theta : ℂ) * Complex.I) = 1 := by
    rw [sub_eq_add_neg]
    have h := congrArg (fun r : ℝ => r ^ 2) (Complex.norm_cos_add_sin_mul_I (-theta))
    simpa [Complex.normSq_eq_norm_sq, Complex.cos_neg, Complex.sin_neg] using h
  rw [hunit]
  norm_num

/-- The initial QAE state decomposes as a superposition of the two Grover-plane
eigenstates. -/
theorem qaePlaneVector_eq_eigen_superposition (theta : ℝ) :
    QuantumLibrary.qaePlaneVector theta =
      qaeCoeffPlus theta • planeEigenPlus + qaeCoeffMinus theta • planeEigenMinus := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [QuantumLibrary.qaePlaneVector, qaeCoeffPlus, qaeCoeffMinus, planeEigenPlus,
      planeEigenMinus]
    ring_nf
    rw [sq]
    rw [invSqrt2_mul_self]
    ring
  · simp [QuantumLibrary.qaePlaneVector, qaeCoeffPlus, qaeCoeffMinus, planeEigenPlus,
      planeEigenMinus]
    ring_nf
    rw [Complex.I_sq]
    rw [sq]
    rw [invSqrt2_mul_self]
    ring

/-- QPE is linear on a two-term target-state superposition.  The phase argument
of `approxQPEStateConcrete` is ignored by the matrix pipeline, so each branch can
be assigned the eigenphase used to rewrite it. -/
theorem qpeOutputStateConcrete_linear_combination {n m : ℕ} {U : Square n}
    {ψ φ : Vector n} (a b : ℂ) (theta thetaψ thetaφ : ℝ) :
    QPE.approxQPEStateConcrete (m := m) (U := U) (ψ := a • ψ + b • φ) theta =
      a • QPE.approxQPEStateConcrete (m := m) (U := U) (ψ := ψ) thetaψ +
        b • QPE.approxQPEStateConcrete (m := m) (U := U) (ψ := φ) thetaφ := by
  unfold QPE.approxQPEStateConcrete
  simp [Matrix.kron_add_right, Matrix.kron_smul_right]

/-- QPE applied to the initial QAE plane state is the corresponding linear
superposition of the two QPE eigenphase output states. -/
theorem qpeOutput_groverPlane_initial_eq_eigenphase_superposition
    (m : ℕ) (theta : ℝ) :
    QPE.approxQPEStateConcrete (m := m) (U := groverPlaneRotation theta)
        (ψ := QuantumLibrary.qaePlaneVector theta) (0 : ℝ) =
      qaeCoeffPlus theta •
          ((QPE.inverseQFTMatrix m ⬝ QPE.phaseState m (theta / Real.pi)) ⊗ planeEigenPlus) +
        qaeCoeffMinus theta •
          ((QPE.inverseQFTMatrix m ⬝ QPE.phaseState m (-(theta / Real.pi))) ⊗ planeEigenMinus) := by
  rw [qaePlaneVector_eq_eigen_superposition]
  rw [qpeOutputStateConcrete_linear_combination
    (theta := 0) (thetaψ := theta / Real.pi) (thetaφ := -(theta / Real.pi))]
  rw [QPE.approxQPEStateConcrete_eq_distribution_tensor_eigenstate
    (groverPlaneRotation_eigen_plus theta)]
  rw [QPE.approxQPEStateConcrete_eq_distribution_tensor_eigenstate
    (groverPlaneRotation_eigen_minus theta)]

/-- Counting-register marginal probability for a joint QPE state. -/
def qpeCountingMarginal {n m : ℕ} (state : Vector (QPE.M m * n)) (y : Fin (QPE.M m)) : ℝ :=
  ∑ j : Fin n, Measurement.prob state (finProdFinEquiv (y, j))

theorem groverPlane_two_branch_normSq_sum (a b : ℂ) :
    Complex.normSq (invSqrt2 * (a + b)) +
      Complex.normSq (invSqrt2 * (-Complex.I * a + Complex.I * b)) =
        Complex.normSq a + Complex.normSq b := by
  rw [Complex.normSq_mul, normSq_invSqrt2]
  rw [Complex.normSq_mul, normSq_invSqrt2]
  rw [Complex.normSq_add, Complex.normSq_add]
  simp [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_I]
  ring_nf

theorem groverPlane_two_branch_normSq_sum_coeff
    (cp cm dp dm : ℂ)
    (hcp : Complex.normSq cp = (1 / 2 : ℝ))
    (hcm : Complex.normSq cm = (1 / 2 : ℝ)) :
    Complex.normSq (cp * (dp * invSqrt2) + cm * (dm * invSqrt2)) +
      Complex.normSq (-(cp * (dp * (Complex.I * invSqrt2))) +
        cm * (dm * (Complex.I * invSqrt2))) =
        (1 / 2 : ℝ) * Complex.normSq dp + (1 / 2 : ℝ) * Complex.normSq dm := by
  have h := groverPlane_two_branch_normSq_sum (cp * dp) (cm * dm)
  have hleft :
      Complex.normSq (cp * (dp * invSqrt2) + cm * (dm * invSqrt2)) +
        Complex.normSq (-(cp * (dp * (Complex.I * invSqrt2))) +
          cm * (dm * (Complex.I * invSqrt2))) =
      Complex.normSq (cp * dp) + Complex.normSq (cm * dm) := by
    convert h using 1
    ring_nf
  rw [hleft]
  rw [Complex.normSq_mul, Complex.normSq_mul, hcp, hcm]


/-- The counting-register marginal of QPE on the initial Grover-plane state is
the average of the two QPE eigenphase distributions. -/
theorem qpeCountingMarginal_groverPlane_initial
    (m : ℕ) (theta : ℝ) (y : Fin (QPE.M m)) :
    qpeCountingMarginal
        (QPE.approxQPEStateConcrete (m := m) (U := groverPlaneRotation theta)
          (ψ := QuantumLibrary.qaePlaneVector theta) (0 : ℝ)) y =
      (1 / 2 : ℝ) * QPE.qpeApproxOutcomeProbability m (theta / Real.pi) y +
        (1 / 2 : ℝ) * QPE.qpeApproxOutcomeProbability m (-(theta / Real.pi)) y := by
  unfold qpeCountingMarginal
  rw [qpeOutput_groverPlane_initial_eq_eigenphase_superposition]
  have hcol : (finProdFinEquiv.symm (0 : Fin (1 * 1))).1 = (0 : Fin 1) := Subsingleton.elim _ _
  simp [Measurement.prob, Matrix.kron, planeEigenPlus, planeEigenMinus,
    QPE.qpeApproxOutcomeProbability, QPE.qpeApproxAmplitude, Fin.sum_univ_two, hcol]
  rw [groverPlane_two_branch_normSq_sum_coeff]
  · ring_nf
  · exact qaeCoeffPlus_normSq theta
  · exact qaeCoeffMinus_normSq theta


end Grover
end QAE
