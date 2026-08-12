import QAELean.QuantumAmplitudeEstimation

noncomputable section

set_option maxRecDepth 10000

namespace QAE

open QuantumComputing
open scoped BigOperators

namespace QPE

private theorem isUnitary_pow {n : ℕ} {U : Square n}
    (hU : Matrix.isUnitary U) (k : ℕ) : Matrix.isUnitary (U ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      simpa [pow_succ] using Matrix.isUnitary_mul ih hU

theorem controlledPowerMatrix_isUnitary {n m : ℕ} {U : Square n}
    (hU : Matrix.isUnitary U) :
    Matrix.isUnitary (controlledPowerMatrix m U) := by
  rw [Matrix.isUnitary_iff_adjoint_mul_self]
  ext row col
  rw [← finProdFinEquiv.apply_symm_apply row,
    ← finProdFinEquiv.apply_symm_apply col]
  rcases finProdFinEquiv.symm row with ⟨r, i⟩
  rcases finProdFinEquiv.symm col with ⟨c, j⟩
  change (∑ x : Fin (M m * n),
      star (controlledPowerMatrix m U x (finProdFinEquiv (r, i))) *
        controlledPowerMatrix m U x (finProdFinEquiv (c, j))) =
    (1 : Square (M m * n)) (finProdFinEquiv (r, i)) (finProdFinEquiv (c, j))
  rw [← finProdFinEquiv.sum_comp]
  simp [controlledPowerMatrix]
  rw [Fintype.sum_prod_type]
  by_cases hrc : r = c
  · subst c
    simp [Finset.sum_ite_eq', Finset.mem_univ]
    simp only [Matrix.one_apply]
    simp only [finProdFinEquiv.apply_eq_iff_eq]
    have hp := (Matrix.isUnitary_iff_adjoint_mul_self (U ^ (r : ℕ))).mp
      (isUnitary_pow hU (r : ℕ))
    simpa only [Matrix.mul, _root_.Matrix.mul_apply, Matrix.conjTranspose_apply, starRingEnd_apply, Matrix.one_apply, Prod.mk.injEq, true_and, if_pos] using congrFun (congrFun hp i) j
  · simp [hrc, Ne.symm hrc]

end QPE

namespace Grover

private theorem diagonalSign_isUnitary {N : ℕ} (s : Fin N → Bool) :
    Matrix.isUnitary (fun r c : Fin N =>
      if r = c then if s c then (-1 : ℂ) else 1 else 0) := by
  rw [Matrix.isUnitary_iff_adjoint_mul_self]
  ext r c
  by_cases hrc : r = c
  · subst c
    cases hs : s r <;> simp [hs, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply]
  · simp [Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply, hrc, Ne.symm hrc]

theorem phaseOracle_isUnitary (n : ℕ) (f : Fin (QPE.M n) → Bool) :
    Matrix.isUnitary (phaseOracle n f) := by
  exact diagonalSign_isUnitary f

theorem zeroReflection_isUnitary (n : ℕ) :
    Matrix.isUnitary (zeroReflection n) := by
  rw [Matrix.isUnitary_iff_adjoint_mul_self]
  ext r c
  by_cases hrc : r = c
  · subst c
    by_cases hz : r = QPE.zeroIndex n <;>
      simp [zeroReflection, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply, hz]
  · simp [zeroReflection, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply, hrc, Ne.symm hrc]

theorem paperGroverOperator_isUnitary {n : ℕ}
    (A : Square (QPE.M n)) (f : Fin (QPE.M n) → Bool)
    (hA : Matrix.isUnitary A) :
    Matrix.isUnitary (paperGroverOperator n A f) := by
  unfold paperGroverOperator
  have hAadj : Matrix.isUnitary A† := by
    rw [Matrix.isUnitary_iff_adjoint_mul_self]
    simpa [Matrix.adjoint_adjoint] using (Matrix.isUnitary_iff_mul_adjoint_self A).mp hA
  have hprod : Matrix.isUnitary
      (A ⬝ zeroReflection n ⬝ A† ⬝ phaseOracle n f) := by
    exact Matrix.isUnitary_mul
      (Matrix.isUnitary_mul
        (Matrix.isUnitary_mul hA (zeroReflection_isUnitary n)) hAadj)
      (phaseOracle_isUnitary n f)
  rw [Matrix.isUnitary_iff_adjoint_mul_self] at hprod ⊢
  rw [Matrix.adjoint_neg]
  change (-((A ⬝ zeroReflection n ⬝ A† ⬝ phaseOracle n f)†)) *
    (-(A ⬝ zeroReflection n ⬝ A† ⬝ phaseOracle n f)) = 1
  simpa only [neg_mul_neg] using hprod

end Grover
end QAE
