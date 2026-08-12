import QAELean.Unitarity

noncomputable section

namespace QAE
namespace Grover

open QuantumComputing

theorem paperQAEInitialState_isNormalized {m n : ℕ}
    (A : Square (QPE.M n)) (hA : Matrix.isUnitary A) :
    Vector.IsNormalized (paperQAEInitialState m n A) := by
  unfold paperQAEInitialState
  apply Vector.isNormalized_kron
  · exact Vector.basis_isNormalized (QPE.zeroIndex m)
  · exact Matrix.isUnitary_mul_isNormalized hA
      (Vector.basis_isNormalized (QPE.zeroIndex n))

theorem paperQAEAfterQFT_isNormalized {m n : ℕ}
    (A : Square (QPE.M n)) (hA : Matrix.isUnitary A) :
    Vector.IsNormalized (paperQAEAfterQFT m n A) := by
  unfold paperQAEAfterQFT
  apply Matrix.isUnitary_mul_isNormalized
  exact Matrix.isUnitary_kron (QPE.qftMatrix_isUnitary m) (by simp)
  exact paperQAEInitialState_isNormalized A hA

theorem paperQAEAfterControlledPowers_isNormalized {m n : ℕ}
    (A : Square (QPE.M n)) (f : Fin (QPE.M n) → Bool)
    (hA : Matrix.isUnitary A) :
    Vector.IsNormalized (paperQAEAfterControlledPowers m n A f) := by
  unfold paperQAEAfterControlledPowers
  apply Matrix.isUnitary_mul_isNormalized
  · exact QPE.controlledPowerMatrix_isUnitary
      (Grover.paperGroverOperator_isUnitary A f hA)
  · exact paperQAEAfterQFT_isNormalized A hA

theorem paperQAEFinalState_isNormalized {m n : ℕ}
    (A : Square (QPE.M n)) (f : Fin (QPE.M n) → Bool)
    (hA : Matrix.isUnitary A) :
    Vector.IsNormalized (paperQAEFinalState m n A f) := by
  unfold paperQAEFinalState
  apply Matrix.isUnitary_mul_isNormalized
  · exact Matrix.isUnitary_kron (QPE.inverseQFTMatrix_isUnitary m) (by simp)
  · exact paperQAEAfterControlledPowers_isNormalized A f hA

end Grover
end QAE
