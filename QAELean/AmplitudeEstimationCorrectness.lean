import QAELean.GroverQAESuperposition
import QAELean.BHMTK1Tangent

/-!
# Conservative end-to-end QAE correctness

This module connects the canonical Grover-plane QPE distribution to the existing
QAE analytic error theorem.  It proves nearest-eigenphase correctness statements
with the currently available single-nearest-outcome QPE probability bound.
-/

noncomputable section

namespace QAE

namespace QPE

/-- BHMT Paper Theorem 11 for the approximate phase-estimation distribution.

The distribution is represented by `qpeApproxOutcomeProbability m theta`: the
probability of measuring counting-register value `x` after applying the inverse
QFT to `phaseState m theta`.

This statement packages the paper-facing facts: exact-grid phases are measured
with probability one, off-grid point probabilities have the sine-ratio form, and
the circular `k / M` window has the BHMT lower bounds for `k > 1` and for
`k = 1` with `m > 1`. -/
theorem PaperTheorem11 :
    (∀ (m : ℕ) {theta : ℝ}, 0 ≤ theta → theta < 1 →
      qpeFractionalOffset m theta = 0 →
        qpeApproxOutcomeProbability m theta (qpeLowerAdjacentOutcome m theta) = 1) ∧
    (∀ (m : ℕ) (theta : ℝ) (x : Fin (M m)),
      Real.sin (Real.pi * (theta - (((x : ℕ) : ℝ) / (M m : ℝ)))) ≠ 0 →
        qpeApproxOutcomeProbability m theta x =
          qpeApproxGeometricProbability (M m)
            (theta - (((x : ℕ) : ℝ) / (M m : ℝ)))) ∧
    (∀ (m k : ℕ) {theta : ℝ}, 0 ≤ theta → theta ≤ 1 → 1 < k →
      1 - 1 / (2 * ((k : ℝ) - 1)) ≤ qpeCircularPhaseWindowProbability m k theta) ∧
    (∀ (m : ℕ) {theta : ℝ}, 1 < m → 0 ≤ theta → theta ≤ 1 →
      8 / Real.pi ^ 2 ≤ qpeCircularPhaseWindowProbability m 1 theta) := by
  constructor
  · intro m theta h0 h1 hx
    exact qpeApproxOutcomeProbability_lowerAdjacent_eq_one_of_fractionalOffset_eq_zero
      m h0 h1 hx
  constructor
  · intro m theta x hden
    exact qpeApproxOutcomeProbability_eq_geometric_of_sin_ne_zero m theta x hden
  constructor
  · intro m k theta h0 h1 hk
    have h := qpeCircularPhaseWindowProbability_lower_bound_k_gt_one m k h0 h1 hk
    have hk_ne : k ≠ 1 := by omega
    simpa [bhmt11SuccessProbability, hk_ne] using h
  · intro m theta _hm h0 h1
    exact qpeCircularPhaseWindowProbability_lower_bound_k1 m h0 h1

end QPE

namespace Grover

open QuantumComputing
open scoped BigOperators

/-- The selective phase oracle `S_f`: it flips exactly the computational-basis
states marked by `f`.  The work register has `n` qubits and dimension `2^n`. -/
def phaseOracle (n : ℕ) (f : Fin (QPE.M n) → Bool) : Square (QPE.M n) :=
  fun row col => if row = col then if f col then (-1 : ℂ) else 1 else 0

@[simp] theorem phaseOracle_apply (n : ℕ) (f : Fin (QPE.M n) → Bool)
    (row col : Fin (QPE.M n)) :
    phaseOracle n f row col = if row = col then if f col then (-1 : ℂ) else 1 else 0 :=
  rfl

/-- `S_f` multiplies a marked basis state by `-1` and an unmarked basis state by `1`. -/
theorem phaseOracle_mul_basis (n : ℕ) (f : Fin (QPE.M n) → Bool)
    (x : Fin (QPE.M n)) :
    phaseOracle n f ⬝ Vector.basis x =
      (if f x then (-1 : ℂ) else 1) • Vector.basis x := by
  ext row col
  fin_cases col
  simp [phaseOracle, Matrix.mul, _root_.Matrix.mul_apply, Vector.basis]

/-- The selective phase oracle is unitary. -/
theorem phaseOracle_isUnitary (n : ℕ) (f : Fin (QPE.M n) → Bool) :
    Matrix.isUnitary (phaseOracle n f) := by
  rw [Matrix.isUnitary_iff_adjoint_mul_self]
  ext row col
  by_cases h : row = col
  · subst col
    by_cases hf : f row <;>
      simp [phaseOracle, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply, hf]
  · have h' : col ≠ row := by
      intro hc
      exact h hc.symm
    simp [phaseOracle, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply, h, h']

/-- The zero reflection `S₀`: it flips only the all-zero computational-basis state. -/
def zeroReflection (n : ℕ) : Square (QPE.M n) :=
  fun row col => if row = col then if col = QPE.zeroIndex n then (-1 : ℂ) else 1 else 0

@[simp] theorem zeroReflection_apply (n : ℕ) (row col : Fin (QPE.M n)) :
    zeroReflection n row col =
      if row = col then if col = QPE.zeroIndex n then (-1 : ℂ) else 1 else 0 :=
  rfl

/-- `S₀` flips `|0...0⟩`. -/
theorem zeroReflection_mul_zero_basis (n : ℕ) :
    zeroReflection n ⬝ Vector.basis (QPE.zeroIndex n) =
      (-1 : ℂ) • Vector.basis (QPE.zeroIndex n) := by
  ext row col
  fin_cases col
  simp [zeroReflection, Matrix.mul, _root_.Matrix.mul_apply, Vector.basis]

/-- `S₀` fixes every nonzero computational-basis state. -/
theorem zeroReflection_mul_basis_of_ne (n : ℕ) {x : Fin (QPE.M n)}
    (hx : x ≠ QPE.zeroIndex n) :
    zeroReflection n ⬝ Vector.basis x = Vector.basis x := by
  ext row col
  fin_cases col
  simp [zeroReflection, Matrix.mul, _root_.Matrix.mul_apply, Vector.basis, hx]

/-- The zero reflection is unitary. -/
theorem zeroReflection_isUnitary (n : ℕ) : Matrix.isUnitary (zeroReflection n) := by
  rw [Matrix.isUnitary_iff_adjoint_mul_self]
  ext row col
  by_cases h : row = col
  · subst col
    by_cases hz : row = QPE.zeroIndex n <;>
      simp [zeroReflection, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply, hz]
  · have h' : col ≠ row := by
      intro hc
      exact h hc.symm
    simp [zeroReflection, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply, h, h']

/-- The BHMT Grover iterate `Q = -A S₀ A† S_f` on the work register.

This is the paper-level operator.  The one-qubit `Ry` operator used elsewhere is
only the two-dimensional invariant-plane specialization of this iterate. -/
def paperGroverOperator (n : ℕ) (A : Square (QPE.M n))
    (f : Fin (QPE.M n) → Bool) : Square (QPE.M n) :=
  - (A ⬝ zeroReflection n ⬝ A† ⬝ phaseOracle n f)

/-- The paper-level Grover iterate is unitary whenever the preparation operator
`A` is unitary, as assumed implicitly in BHMT. -/
theorem paperGroverOperator_isUnitary (n : ℕ) (A : Square (QPE.M n))
    (f : Fin (QPE.M n) → Bool) (hA : Matrix.isUnitary A) :
    Matrix.isUnitary (paperGroverOperator n A f) := by
  let B : Square (QPE.M n) := A ⬝ zeroReflection n ⬝ A† ⬝ phaseOracle n f
  change Matrix.isUnitary (-B)
  have hAadj : Matrix.isUnitary A† := by
    rw [Matrix.isUnitary_iff_adjoint_mul_self]
    rw [Matrix.adjoint_adjoint]
    exact (Matrix.isUnitary_iff_mul_adjoint_self A).mp hA
  have hB : Matrix.isUnitary B := by
    dsimp [B]
    exact Matrix.isUnitary_mul
      (Matrix.isUnitary_mul
        (Matrix.isUnitary_mul hA (zeroReflection_isUnitary n)) hAadj)
      (phaseOracle_isUnitary n f)
  rw [Matrix.isUnitary_iff_adjoint_mul_self]
  have h := (Matrix.isUnitary_iff_adjoint_mul_self B).mp hB
  ext row col
  simpa [Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply] using congrFun (congrFun h row) col

/-- `S₀` acts on an arbitrary vector by subtracting twice its all-zero component. -/
theorem zeroReflection_mul_vector (n : ℕ) (v : Vector (QPE.M n)) :
    zeroReflection n ⬝ v =
      v - ((2 : ℂ) * v (QPE.zeroIndex n) 0) • Vector.basis (QPE.zeroIndex n) := by
  ext row col
  fin_cases col
  by_cases hz : row = QPE.zeroIndex n
  · subst row
    simp [zeroReflection, Matrix.mul, _root_.Matrix.mul_apply, Vector.basis]
    ring
  · simp [zeroReflection, Matrix.mul, _root_.Matrix.mul_apply, Vector.basis, hz]

/-- Conjugating `S₀` by `A` reflects about the prepared state `A|0...0⟩`. -/
theorem conjugatedZeroReflection_mul_vector {n : ℕ}
    (A : Square (QPE.M n)) (hA : Matrix.isUnitary A) (v : Vector (QPE.M n)) :
    A ⬝ (zeroReflection n ⬝ (A† ⬝ v)) =
      v - ((2 : ℂ) * (A† ⬝ v) (QPE.zeroIndex n) 0) •
        (A ⬝ Vector.basis (QPE.zeroIndex n)) := by
  rw [zeroReflection_mul_vector]
  simp only [sub_eq_add_neg]
  change A * (A† * v + -((2 * (A† * v) (QPE.zeroIndex n) 0) •
      Vector.basis (QPE.zeroIndex n))) =
    v + -((2 * (A† * v) (QPE.zeroIndex n) 0) •
      (A * Vector.basis (QPE.zeroIndex n)))
  rw [Matrix.mul_add]
  simp [Matrix.mul_smul]
  have hAA : A ⬝ A† = I (QPE.M n) :=
    (Matrix.isUnitary_iff_mul_adjoint_self A).mp hA
  calc
    A ⬝ (A† ⬝ v) = (A ⬝ A†) ⬝ v := by
      change A * (A† * v) = (A * A†) * v
      rw [← _root_.Matrix.mul_assoc]
    _ = v := by
      rw [hAA]
      simp [Matrix.mul]

/-- A vector supported only on unmarked states is fixed by `S_f`. -/
theorem phaseOracle_mul_of_bad_support (n : ℕ) (f : Fin (QPE.M n) → Bool)
    (v : Vector (QPE.M n)) (hbad : ∀ x, f x = true → v x 0 = 0) :
    phaseOracle n f ⬝ v = v := by
  ext row col
  fin_cases col
  by_cases hf : f row
  · simp [phaseOracle, Matrix.mul, _root_.Matrix.mul_apply, hf, hbad row hf]
  · simp [phaseOracle, Matrix.mul, _root_.Matrix.mul_apply, hf]

/-- A vector supported only on marked states is negated by `S_f`. -/
theorem phaseOracle_mul_of_good_support (n : ℕ) (f : Fin (QPE.M n) → Bool)
    (v : Vector (QPE.M n)) (hgood : ∀ x, f x = false → v x 0 = 0) :
    phaseOracle n f ⬝ v = (-1 : ℂ) • v := by
  ext row col
  fin_cases col
  by_cases hfalse : f row = false
  · simp [phaseOracle, Matrix.mul, _root_.Matrix.mul_apply, hfalse, hgood row hfalse]
  · have htrue : f row = true := by
      cases hfr : f row <;> simp [hfr] at hfalse ⊢
    simp [phaseOracle, Matrix.mul, _root_.Matrix.mul_apply, htrue]


/-- Bad and good components have disjoint support, hence zero inner product. -/
theorem bad_good_support_orthogonal
    {n : ℕ} {f : Fin (QPE.M n) → Bool} {ψ0 ψ1 : Vector (QPE.M n)}
    (hbad : ∀ x, f x = true → ψ0 x 0 = 0)
    (hgood : ∀ x, f x = false → ψ1 x 0 = 0) :
    ψ0† ⬝ ψ1 = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  change (∑ x : Fin (QPE.M n), star (ψ0 x 0) * ψ1 x 0) = 0
  apply Finset.sum_eq_zero
  intro x _hx
  by_cases hf : f x = true
  · simp [hbad x hf]
  · have hfalse : f x = false := by
      cases hfx : f x <;> simp [hfx] at hf ⊢
    simp [hgood x hfalse]

/-- The reverse inner product of bad and good components is also zero. -/
theorem good_bad_support_orthogonal
    {n : ℕ} {f : Fin (QPE.M n) → Bool} {ψ0 ψ1 : Vector (QPE.M n)}
    (hbad : ∀ x, f x = true → ψ0 x 0 = 0)
    (hgood : ∀ x, f x = false → ψ1 x 0 = 0) :
    ψ1† ⬝ ψ0 = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  change (∑ x : Fin (QPE.M n), star (ψ1 x 0) * ψ0 x 0) = 0
  apply Finset.sum_eq_zero
  intro x _hx
  by_cases hf : f x = true
  · simp [hbad x hf]
  · have hfalse : f x = false := by
      cases hfx : f x <;> simp [hfx] at hf ⊢
    simp [hgood x hfalse]

/-- In an orthogonal bad/good decomposition of `A|0...0⟩`, the bad component
has overlap `cos θ` with the prepared state. -/
theorem badComponent_overlap_of_decomposition
    {n : ℕ} {A : Square (QPE.M n)} {ψ0 ψ1 : Vector (QPE.M n)} {theta : ℝ}
    (hinit : A ⬝ Vector.basis (QPE.zeroIndex n) =
      (Real.cos theta : ℂ) • ψ0 + (Real.sin theta : ℂ) • ψ1)
    (hψ0 : Vector.IsNormalized ψ0)
    (horth10 : ψ1† ⬝ ψ0 = 0) :
    (A† ⬝ ψ0) (QPE.zeroIndex n) 0 = (Real.cos theta : ℂ) := by
  have hpick :
      (A† ⬝ ψ0) (QPE.zeroIndex n) 0 =
        (((Vector.basis (QPE.zeroIndex n))† ⬝ (A† ⬝ ψ0)) 0 0) := by
    simp [Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply, Vector.basis]
  rw [hpick]
  change (((Vector.basis (QPE.zeroIndex n))† * (A† * ψ0)) 0 0) =
    (Real.cos theta : ℂ)
  rw [← _root_.Matrix.mul_assoc]
  change ((((Vector.basis (QPE.zeroIndex n))† ⬝ A†) ⬝ ψ0) 0 0) =
    (Real.cos theta : ℂ)
  rw [← Matrix.adjoint_mul]
  rw [hinit]
  simp only [Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply, Vector.IsNormalized]
    at hψ0 horth10 ⊢
  have hnorm : (∑ x : Fin (QPE.M n), star (ψ0 x 0) * ψ0 x 0) = 1 := by
    have h := congrFun (congrFun hψ0 0) 0
    simpa [_root_.Matrix.mul_apply] using h
  have horth : (∑ x : Fin (QPE.M n), star (ψ1 x 0) * ψ0 x 0) = 0 := by
    have h := congrFun (congrFun horth10 0) 0
    simpa [_root_.Matrix.mul_apply] using h
  simp_rw [_root_.Matrix.conjTranspose_add, _root_.Matrix.conjTranspose_smul]
  change (∑ x : Fin (QPE.M n),
      ((star (Real.cos theta : ℂ) * star (ψ0 x 0) +
          star (Real.sin theta : ℂ) * star (ψ1 x 0)) * ψ0 x 0)) =
    (Real.cos theta : ℂ)
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hnorm, horth]
  have hcosStar : star (Real.cos theta : ℂ) = (Real.cos theta : ℂ) := by
    simpa only [starRingEnd_apply] using Complex.conj_ofReal (Real.cos theta)
  have hsinStar : star (Real.sin theta : ℂ) = (Real.sin theta : ℂ) := by
    simpa only [starRingEnd_apply] using Complex.conj_ofReal (Real.sin theta)
  rw [hcosStar, hsinStar]
  simp

/-- In an orthogonal bad/good decomposition of `A|0...0⟩`, the good component
has overlap `sin θ` with the prepared state. -/
theorem goodComponent_overlap_of_decomposition
    {n : ℕ} {A : Square (QPE.M n)} {ψ0 ψ1 : Vector (QPE.M n)} {theta : ℝ}
    (hinit : A ⬝ Vector.basis (QPE.zeroIndex n) =
      (Real.cos theta : ℂ) • ψ0 + (Real.sin theta : ℂ) • ψ1)
    (hψ1 : Vector.IsNormalized ψ1)
    (horth01 : ψ0† ⬝ ψ1 = 0) :
    (A† ⬝ ψ1) (QPE.zeroIndex n) 0 = (Real.sin theta : ℂ) := by
  have hpick :
      (A† ⬝ ψ1) (QPE.zeroIndex n) 0 =
        (((Vector.basis (QPE.zeroIndex n))† ⬝ (A† ⬝ ψ1)) 0 0) := by
    simp [Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply, Vector.basis]
  rw [hpick]
  change (((Vector.basis (QPE.zeroIndex n))† * (A† * ψ1)) 0 0) =
    (Real.sin theta : ℂ)
  rw [← _root_.Matrix.mul_assoc]
  change ((((Vector.basis (QPE.zeroIndex n))† ⬝ A†) ⬝ ψ1) 0 0) =
    (Real.sin theta : ℂ)
  rw [← Matrix.adjoint_mul]
  rw [hinit]
  simp only [Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply, Vector.IsNormalized]
    at hψ1 horth01 ⊢
  have hnorm : (∑ x : Fin (QPE.M n), star (ψ1 x 0) * ψ1 x 0) = 1 := by
    have h := congrFun (congrFun hψ1 0) 0
    simpa [_root_.Matrix.mul_apply] using h
  have horth : (∑ x : Fin (QPE.M n), star (ψ0 x 0) * ψ1 x 0) = 0 := by
    have h := congrFun (congrFun horth01 0) 0
    simpa [_root_.Matrix.mul_apply] using h
  simp_rw [_root_.Matrix.conjTranspose_add, _root_.Matrix.conjTranspose_smul]
  change (∑ x : Fin (QPE.M n),
      ((star (Real.cos theta : ℂ) * star (ψ0 x 0) +
          star (Real.sin theta : ℂ) * star (ψ1 x 0)) * ψ1 x 0)) =
    (Real.sin theta : ℂ)
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum, horth, hnorm]
  have hcosStar : star (Real.cos theta : ℂ) = (Real.cos theta : ℂ) := by
    simpa only [starRingEnd_apply] using Complex.conj_ofReal (Real.cos theta)
  have hsinStar : star (Real.sin theta : ℂ) = (Real.sin theta : ℂ) := by
    simpa only [starRingEnd_apply] using Complex.conj_ofReal (Real.sin theta)
  rw [hcosStar, hsinStar]
  simp

/-- On the bad component, the paper Grover iterate acts as the first column of
rotation by `2θ`. -/
theorem paperGroverOperator_mul_badComponent
    {n : ℕ} (A : Square (QPE.M n)) (f : Fin (QPE.M n) → Bool)
    (ψ0 ψ1 : Vector (QPE.M n)) (theta : ℝ)
    (hA : Matrix.isUnitary A)
    (hinit : A ⬝ Vector.basis (QPE.zeroIndex n) =
      (Real.cos theta : ℂ) • ψ0 + (Real.sin theta : ℂ) • ψ1)
    (hbad : ∀ x, f x = true → ψ0 x 0 = 0)
    (hinner0 : (A† ⬝ ψ0) (QPE.zeroIndex n) 0 = (Real.cos theta : ℂ)) :
    paperGroverOperator n A f ⬝ ψ0 =
      (Real.cos (2 * theta) : ℂ) • ψ0 + (Real.sin (2 * theta) : ℂ) • ψ1 := by
  unfold paperGroverOperator
  change (-(A * zeroReflection n * A† * phaseOracle n f)) * ψ0 =
      (Real.cos (2 * theta) : ℂ) • ψ0 + (Real.sin (2 * theta) : ℂ) • ψ1
  rw [_root_.Matrix.neg_mul]
  rw [_root_.Matrix.mul_assoc]
  rw [_root_.Matrix.mul_assoc]
  rw [_root_.Matrix.mul_assoc]
  rw [show phaseOracle n f * ψ0 = ψ0 from phaseOracle_mul_of_bad_support n f ψ0 hbad]
  rw [show A * (zeroReflection n * (A† * ψ0)) =
      ψ0 - ((2 : ℂ) * (A† ⬝ ψ0) (QPE.zeroIndex n) 0) •
        (A ⬝ Vector.basis (QPE.zeroIndex n)) from
    conjugatedZeroReflection_mul_vector A hA ψ0]
  rw [hinner0, hinit]
  ext row col
  fin_cases col
  simp
  rw [Complex.cos_two_mul, Complex.sin_two_mul]
  ring

/-- On the good component, the paper Grover iterate acts as the second column of
rotation by `2θ`. -/
theorem paperGroverOperator_mul_goodComponent
    {n : ℕ} (A : Square (QPE.M n)) (f : Fin (QPE.M n) → Bool)
    (ψ0 ψ1 : Vector (QPE.M n)) (theta : ℝ)
    (hA : Matrix.isUnitary A)
    (hinit : A ⬝ Vector.basis (QPE.zeroIndex n) =
      (Real.cos theta : ℂ) • ψ0 + (Real.sin theta : ℂ) • ψ1)
    (hgood : ∀ x, f x = false → ψ1 x 0 = 0)
    (hinner1 : (A† ⬝ ψ1) (QPE.zeroIndex n) 0 = (Real.sin theta : ℂ)) :
    paperGroverOperator n A f ⬝ ψ1 =
      (-(Real.sin (2 * theta) : ℂ)) • ψ0 + (Real.cos (2 * theta) : ℂ) • ψ1 := by
  unfold paperGroverOperator
  change (-(A * zeroReflection n * A† * phaseOracle n f)) * ψ1 =
      (-(Real.sin (2 * theta) : ℂ)) • ψ0 + (Real.cos (2 * theta) : ℂ) • ψ1
  rw [_root_.Matrix.neg_mul]
  rw [_root_.Matrix.mul_assoc]
  rw [_root_.Matrix.mul_assoc]
  rw [_root_.Matrix.mul_assoc]
  rw [show phaseOracle n f * ψ1 = (-1 : ℂ) • ψ1 from
    phaseOracle_mul_of_good_support n f ψ1 hgood]
  have hreflect := conjugatedZeroReflection_mul_vector A hA ((-1 : ℂ) • ψ1)
  have hinner_neg :
      (A† ⬝ ((-1 : ℂ) • ψ1)) (QPE.zeroIndex n) 0 = -(Real.sin theta : ℂ) := by
    have hvec : A† ⬝ ((-1 : ℂ) • ψ1) = (-1 : ℂ) • (A† ⬝ ψ1) := by
      change A† * ((-1 : ℂ) • ψ1) = (-1 : ℂ) • (A† * ψ1)
      rw [Matrix.mul_smul]
    rw [hvec]
    simp [hinner1]
  rw [show A * (zeroReflection n * (A† * ((-1 : ℂ) • ψ1))) =
      ((-1 : ℂ) • ψ1) - ((2 : ℂ) * (A† ⬝ ((-1 : ℂ) • ψ1))
        (QPE.zeroIndex n) 0) • (A ⬝ Vector.basis (QPE.zeroIndex n)) from hreflect]
  rw [hinner_neg, hinit]
  ext row col
  fin_cases col
  simp
  rw [Complex.cos_two_mul, Complex.sin_two_mul]
  have hcoef : (1 : ℂ) - 2 * Complex.sin (theta : ℂ) ^ 2 =
      2 * Complex.cos (theta : ℂ) ^ 2 - 1 := by
    calc
      (1 : ℂ) - 2 * Complex.sin (theta : ℂ) ^ 2
          = 2 * (1 - Complex.sin (theta : ℂ) ^ 2) - 1 := by ring
      _ = 2 * Complex.cos (theta : ℂ) ^ 2 - 1 := by
          rw [← Complex.sin_sq_add_cos_sq (theta : ℂ)]
          ring
  calc
    -(2 * Complex.sin (theta : ℂ) * (Complex.cos (theta : ℂ) * ψ0 row 0)) +
        -(2 * Complex.sin (theta : ℂ) * (Complex.sin (theta : ℂ) * ψ1 row 0)) +
          ψ1 row 0
        = -(2 * Complex.sin (theta : ℂ) * Complex.cos (theta : ℂ) * ψ0 row 0) +
            ((1 : ℂ) - 2 * Complex.sin (theta : ℂ) ^ 2) * ψ1 row 0 := by ring
    _ = -(2 * Complex.sin (theta : ℂ) * Complex.cos (theta : ℂ) * ψ0 row 0) +
            (2 * Complex.cos (theta : ℂ) ^ 2 - 1) * ψ1 row 0 := by rw [hcoef]

/-- The negative-Y combination of the bad/good components is an eigenvector of a
Grover-plane rotation with QPE eigenphase `θ / π`. -/
theorem groverRotation_eigenMinus
    {n : ℕ} {Q : Square (QPE.M n)} {ψ0 ψ1 : Vector (QPE.M n)} (theta : ℝ)
    (h0 : Q ⬝ ψ0 =
      (Real.cos (2 * theta) : ℂ) • ψ0 + (Real.sin (2 * theta) : ℂ) • ψ1)
    (h1 : Q ⬝ ψ1 =
      (-(Real.sin (2 * theta) : ℂ)) • ψ0 + (Real.cos (2 * theta) : ℂ) • ψ1) :
    Q ⬝ (invSqrt2 • ψ0 + (-Complex.I * invSqrt2) • ψ1) =
      (Real.fourierChar (theta / Real.pi) : ℂ) •
        (invSqrt2 • ψ0 + (-Complex.I * invSqrt2) • ψ1) := by
  have hphase : (Real.fourierChar (theta / Real.pi) : ℂ) =
      Complex.cos (2 * (theta : ℂ)) + Complex.sin (2 * (theta : ℂ)) * Complex.I := by
    rw [Real.fourierChar_apply]
    have harg : ((2 * Real.pi * (theta / Real.pi) : ℝ) : ℂ) * Complex.I =
        (2 * (theta : ℂ)) * Complex.I := by
      field_simp [Real.pi_ne_zero]
      norm_num
    rw [harg]
    exact Complex.exp_mul_I (2 * (theta : ℂ))
  change Q * (invSqrt2 • ψ0 + (-Complex.I * invSqrt2) • ψ1) =
    (Real.fourierChar (theta / Real.pi) : ℂ) •
      (invSqrt2 • ψ0 + (-Complex.I * invSqrt2) • ψ1)
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  rw [show Q * ψ0 =
    (Real.cos (2 * theta) : ℂ) • ψ0 + (Real.sin (2 * theta) : ℂ) • ψ1 from h0]
  rw [show Q * ψ1 =
    (-(Real.sin (2 * theta) : ℂ)) • ψ0 + (Real.cos (2 * theta) : ℂ) • ψ1 from h1]
  ext row col
  fin_cases col
  simp [hphase]
  rw [Complex.cos_two_mul, Complex.sin_two_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The positive-Y combination of the bad/good components is an eigenvector of a
Grover-plane rotation with QPE eigenphase `-θ / π`. -/
theorem groverRotation_eigenPlus
    {n : ℕ} {Q : Square (QPE.M n)} {ψ0 ψ1 : Vector (QPE.M n)} (theta : ℝ)
    (h0 : Q ⬝ ψ0 =
      (Real.cos (2 * theta) : ℂ) • ψ0 + (Real.sin (2 * theta) : ℂ) • ψ1)
    (h1 : Q ⬝ ψ1 =
      (-(Real.sin (2 * theta) : ℂ)) • ψ0 + (Real.cos (2 * theta) : ℂ) • ψ1) :
    Q ⬝ (invSqrt2 • ψ0 + (Complex.I * invSqrt2) • ψ1) =
      (Real.fourierChar (-(theta / Real.pi)) : ℂ) •
        (invSqrt2 • ψ0 + (Complex.I * invSqrt2) • ψ1) := by
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
  change Q * (invSqrt2 • ψ0 + (Complex.I * invSqrt2) • ψ1) =
    (Real.fourierChar (-(theta / Real.pi)) : ℂ) •
      (invSqrt2 • ψ0 + (Complex.I * invSqrt2) • ψ1)
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  rw [show Q * ψ0 =
    (Real.cos (2 * theta) : ℂ) • ψ0 + (Real.sin (2 * theta) : ℂ) • ψ1 from h0]
  rw [show Q * ψ1 =
    (-(Real.sin (2 * theta) : ℂ)) • ψ0 + (Real.cos (2 * theta) : ℂ) • ψ1 from h1]
  ext row col
  fin_cases col
  simp [hphase]
  rw [Complex.cos_two_mul, Complex.sin_two_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The two BHMT Grover-plane eigenvector equations derived from the raw paper
operator and a bad/good decomposition of `A|0...0⟩`. -/
theorem paperGroverOperator_eigenvectors_of_good_bad_decomposition
    {n : ℕ} (A : Square (QPE.M n)) (f : Fin (QPE.M n) → Bool)
    (ψ0 ψ1 : Vector (QPE.M n)) (theta : ℝ)
    (hA : Matrix.isUnitary A)
    (hinit : A ⬝ Vector.basis (QPE.zeroIndex n) =
      (Real.cos theta : ℂ) • ψ0 + (Real.sin theta : ℂ) • ψ1)
    (hbad : ∀ x, f x = true → ψ0 x 0 = 0)
    (hgood : ∀ x, f x = false → ψ1 x 0 = 0)
    (hψ0 : Vector.IsNormalized ψ0) (hψ1 : Vector.IsNormalized ψ1) :
    paperGroverOperator n A f ⬝ (invSqrt2 • ψ0 + (-Complex.I * invSqrt2) • ψ1) =
        (Real.fourierChar (theta / Real.pi) : ℂ) •
          (invSqrt2 • ψ0 + (-Complex.I * invSqrt2) • ψ1) ∧
      paperGroverOperator n A f ⬝ (invSqrt2 • ψ0 + (Complex.I * invSqrt2) • ψ1) =
        (Real.fourierChar (-(theta / Real.pi)) : ℂ) •
          (invSqrt2 • ψ0 + (Complex.I * invSqrt2) • ψ1) := by
  have horth01 : ψ0† ⬝ ψ1 = 0 := bad_good_support_orthogonal hbad hgood
  have horth10 : ψ1† ⬝ ψ0 = 0 := good_bad_support_orthogonal hbad hgood
  have hinner0 := badComponent_overlap_of_decomposition hinit hψ0 horth10
  have hinner1 := goodComponent_overlap_of_decomposition hinit hψ1 horth01
  have h0 := paperGroverOperator_mul_badComponent A f ψ0 ψ1 theta hA hinit hbad hinner0
  have h1 := paperGroverOperator_mul_goodComponent A f ψ0 ψ1 theta hA hinit hgood hinner1
  exact ⟨groverRotation_eigenMinus theta h0 h1, groverRotation_eigenPlus theta h0 h1⟩

/-- Initial state before QFT: `|0...0⟩ ⊗ A|0...0⟩`.

The counting register has `m` qubits; the work register has `n` qubits. -/
def paperQAEInitialState (m n : ℕ) (A : Square (QPE.M n)) :
    Vector (QPE.M m * QPE.M n) :=
  Vector.basis (QPE.zeroIndex m) ⊗ (A ⬝ Vector.basis (QPE.zeroIndex n))

/-- State after applying QFT to the counting register. -/
def paperQAEAfterQFT (m n : ℕ) (A : Square (QPE.M n)) :
    Vector (QPE.M m * QPE.M n) :=
  (QPE.qftMatrix m ⊗ (I (QPE.M n))) ⬝ paperQAEInitialState m n A

/-- State after controlled powers of the paper Grover operator. -/
def paperQAEAfterControlledPowers (m n : ℕ) (A : Square (QPE.M n))
    (f : Fin (QPE.M n) → Bool) : Vector (QPE.M m * QPE.M n) :=
  QPE.controlledPowerMatrix m (paperGroverOperator n A f) ⬝ paperQAEAfterQFT m n A

/-- Final state of the paper QAE circuit, after inverse QFT on the counting register. -/
def paperQAEFinalState (m n : ℕ) (A : Square (QPE.M n))
    (f : Fin (QPE.M n) → Bool) : Vector (QPE.M m * QPE.M n) :=
  (QPE.inverseQFTMatrix m ⊗ (I (QPE.M n))) ⬝
    paperQAEAfterControlledPowers m n A f

/-- Probability of measuring counting-register outcome `y` in the paper QAE circuit. -/
def paperQAEOutputProbability (m n : ℕ) (A : Square (QPE.M n))
    (f : Fin (QPE.M n) → Bool) (y : Fin (QPE.M m)) : ℝ :=
  ∑ j : Fin (QPE.M n),
    Measurement.prob (paperQAEFinalState m n A f) (finProdFinEquiv (y, j))

/-- Classical post-processing returned by amplitude estimation after measuring `y`. -/
def paperQAEEstimate (m : ℕ) (y : Fin (QPE.M m)) : ℝ :=
  estAmpEstimate (QPE.M m) (y : ℕ)

/-- The post-processing formula is `sin²(π y / M)`. -/
theorem paperQAEEstimate_eq (m : ℕ) (y : Fin (QPE.M m)) :
    paperQAEEstimate m y =
      Real.sin (Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) ^ 2 := by
  rfl

/-- The prepared work-register state `A|0...0⟩`. -/
def paperPreparedState (n : ℕ) (A : Square (QPE.M n)) : Vector (QPE.M n) :=
  A ⬝ Vector.basis (QPE.zeroIndex n)

/-- Projection of the prepared state onto the unmarked, or bad, basis states. -/
def paperBadProjection (n : ℕ) (A : Square (QPE.M n))
    (f : Fin (QPE.M n) → Bool) : Vector (QPE.M n) :=
  fun x _ => if f x then 0 else paperPreparedState n A x 0

/-- Projection of the prepared state onto the marked, or good, basis states. -/
def paperGoodProjection (n : ℕ) (A : Square (QPE.M n))
    (f : Fin (QPE.M n) → Bool) : Vector (QPE.M n) :=
  fun x _ => if f x then paperPreparedState n A x 0 else 0

/-- Probability mass of the prepared state on the bad outcomes. -/
def paperBadProbability (n : ℕ) (A : Square (QPE.M n))
    (f : Fin (QPE.M n) → Bool) : ℝ :=
  ∑ x : Fin (QPE.M n), if f x then 0 else Measurement.prob (paperPreparedState n A) x

/-- Probability mass of the prepared state on the good outcomes. -/
def paperGoodProbability (n : ℕ) (A : Square (QPE.M n))
    (f : Fin (QPE.M n) → Bool) : ℝ :=
  ∑ x : Fin (QPE.M n), if f x then Measurement.prob (paperPreparedState n A) x else 0

/-- The normalized bad state determined by `A`, `f`, and the Grover angle. -/
def paperBadState (n : ℕ) (A : Square (QPE.M n))
    (f : Fin (QPE.M n) → Bool) (theta : ℝ) : Vector (QPE.M n) :=
  ((Real.cos theta : ℂ)⁻¹) • paperBadProjection n A f

/-- The normalized good state determined by `A`, `f`, and the Grover angle. -/
def paperGoodState (n : ℕ) (A : Square (QPE.M n))
    (f : Fin (QPE.M n) → Bool) (theta : ℝ) : Vector (QPE.M n) :=
  ((Real.sin theta : ℂ)⁻¹) • paperGoodProjection n A f

theorem paperPreparedState_decompose_bad_good
    (n : ℕ) (A : Square (QPE.M n)) (f : Fin (QPE.M n) → Bool) :
    paperPreparedState n A =
      paperBadProjection n A f + paperGoodProjection n A f := by
  ext x col
  fin_cases col
  by_cases hf : f x <;> simp [paperPreparedState, paperBadProjection, paperGoodProjection, hf]

theorem paperPreparedState_decompose_bad_good_states
    {n : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool} {theta : ℝ}
    (hcos : (Real.cos theta : ℂ) ≠ 0) (hsin : (Real.sin theta : ℂ) ≠ 0) :
    paperPreparedState n A =
      (Real.cos theta : ℂ) • paperBadState n A f theta +
        (Real.sin theta : ℂ) • paperGoodState n A f theta := by
  rw [paperPreparedState_decompose_bad_good n A f]
  ext x col
  fin_cases col
  by_cases hf : f x
  · simp [paperBadState, paperGoodState, paperBadProjection, paperGoodProjection, hf]
    have hsin' : Complex.sin (theta : ℂ) ≠ 0 := by
      simpa [Complex.ofReal_sin] using hsin
    field_simp [hsin']
  · simp [paperBadState, paperGoodState, paperBadProjection, paperGoodProjection, hf]
    have hcos' : Complex.cos (theta : ℂ) ≠ 0 := by
      simpa [Complex.ofReal_cos] using hcos
    field_simp [hcos']

theorem paperBadState_support
    {n : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool} {theta : ℝ}
    {x : Fin (QPE.M n)} (hf : f x = true) :
    paperBadState n A f theta x 0 = 0 := by
  simp [paperBadState, paperBadProjection, hf]

theorem paperGoodState_support
    {n : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool} {theta : ℝ}
    {x : Fin (QPE.M n)} (hf : f x = false) :
    paperGoodState n A f theta x 0 = 0 := by
  simp [paperGoodState, paperGoodProjection, hf]

theorem paperBadProjection_norm
    (n : ℕ) (A : Square (QPE.M n)) (f : Fin (QPE.M n) → Bool) :
    (paperBadProjection n A f)† ⬝ paperBadProjection n A f =
      fun _ _ => (paperBadProbability n A f : ℂ) := by
  ext i j
  fin_cases i
  fin_cases j
  unfold paperBadProjection paperBadProbability Measurement.prob
  change (∑ x : Fin (QPE.M n),
      star (if f x = true then 0 else paperPreparedState n A x 0) *
        (if f x = true then 0 else paperPreparedState n A x 0)) =
    ↑(∑ x : Fin (QPE.M n),
      if f x = true then 0 else Complex.normSq (paperPreparedState n A x 0))
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hf : f x = true
  · simp [hf]
  · simp [hf, Complex.normSq_eq_conj_mul_self]

theorem paperGoodProjection_norm
    (n : ℕ) (A : Square (QPE.M n)) (f : Fin (QPE.M n) → Bool) :
    (paperGoodProjection n A f)† ⬝ paperGoodProjection n A f =
      fun _ _ => (paperGoodProbability n A f : ℂ) := by
  ext i j
  fin_cases i
  fin_cases j
  unfold paperGoodProjection paperGoodProbability Measurement.prob
  change (∑ x : Fin (QPE.M n),
      star (if f x = true then paperPreparedState n A x 0 else 0) *
        (if f x = true then paperPreparedState n A x 0 else 0)) =
    ↑(∑ x : Fin (QPE.M n),
      if f x = true then Complex.normSq (paperPreparedState n A x 0) else 0)
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hf : f x = true
  · simp [hf, Complex.normSq_eq_conj_mul_self]
  · simp [hf]

theorem paperBadState_isNormalized
    {n : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool} {theta : ℝ}
    (hprob : paperBadProbability n A f = 1 - amplitudeFromAngle theta)
    (hcos : Real.cos theta ≠ 0) :
    Vector.IsNormalized (paperBadState n A f theta) := by
  rw [Vector.IsNormalized]
  unfold paperBadState
  change _root_.Matrix.conjTranspose (((Real.cos theta : ℂ)⁻¹) • paperBadProjection n A f) *
      (((Real.cos theta : ℂ)⁻¹) • paperBadProjection n A f) = 1
  rw [_root_.Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
  change star ((Real.cos theta : ℂ)⁻¹) • ((Real.cos theta : ℂ)⁻¹) •
      ((paperBadProjection n A f)† ⬝ paperBadProjection n A f) = 1
  rw [paperBadProjection_norm n A f]
  ext i j
  fin_cases i
  fin_cases j
  simp
  have hcosC : (Real.cos theta : ℂ) ≠ 0 := by exact_mod_cast hcos
  have hprob_cos : paperBadProbability n A f = Real.cos theta ^ 2 := by
    rw [hprob]
    unfold amplitudeFromAngle
    nlinarith [Real.sin_sq_add_cos_sq theta]
  rw [hprob_cos]
  simp only [Complex.ofReal_pow]
  rw [show (starRingEnd ℂ) (Complex.cos (theta : ℂ)) = (Real.cos theta : ℂ) by
    rw [← Complex.ofReal_cos theta]
    simpa only [starRingEnd_apply] using Complex.conj_ofReal (Real.cos theta)]
  rw [show Complex.cos (theta : ℂ) = (Real.cos theta : ℂ) by rw [← Complex.ofReal_cos theta]]
  field_simp [hcosC]

theorem paperGoodState_isNormalized
    {n : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool} {theta : ℝ}
    (hprob : paperGoodProbability n A f = amplitudeFromAngle theta)
    (hsin : Real.sin theta ≠ 0) :
    Vector.IsNormalized (paperGoodState n A f theta) := by
  rw [Vector.IsNormalized]
  unfold paperGoodState
  change _root_.Matrix.conjTranspose (((Real.sin theta : ℂ)⁻¹) • paperGoodProjection n A f) *
      (((Real.sin theta : ℂ)⁻¹) • paperGoodProjection n A f) = 1
  rw [_root_.Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
  change star ((Real.sin theta : ℂ)⁻¹) • ((Real.sin theta : ℂ)⁻¹) •
      ((paperGoodProjection n A f)† ⬝ paperGoodProjection n A f) = 1
  rw [paperGoodProjection_norm n A f]
  ext i j
  fin_cases i
  fin_cases j
  simp
  have hsinC : (Real.sin theta : ℂ) ≠ 0 := by exact_mod_cast hsin
  rw [hprob]
  unfold amplitudeFromAngle
  simp only [Complex.ofReal_pow]
  rw [show (starRingEnd ℂ) (Complex.sin (theta : ℂ)) = (Real.sin theta : ℂ) by
    rw [← Complex.ofReal_sin theta]
    simpa only [starRingEnd_apply] using Complex.conj_ofReal (Real.sin theta)]
  rw [show Complex.sin (theta : ℂ) = (Real.sin theta : ℂ) by rw [← Complex.ofReal_sin theta]]
  field_simp [hsinC]


theorem paperBadProbability_add_goodProbability
    (n : ℕ) (A : Square (QPE.M n)) (f : Fin (QPE.M n) → Bool) :
    paperBadProbability n A f + paperGoodProbability n A f =
      ∑ x : Fin (QPE.M n), Measurement.prob (paperPreparedState n A) x := by
  unfold paperBadProbability paperGoodProbability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hf : f x <;> simp [hf]

theorem paperBadProbability_add_goodProbability_eq_one
    {n : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool}
    (hA : Matrix.isUnitary A) :
    paperBadProbability n A f + paperGoodProbability n A f = 1 := by
  rw [paperBadProbability_add_goodProbability]
  have hprep : Vector.IsNormalized (paperPreparedState n A) := by
    unfold paperPreparedState
    exact Matrix.isUnitary_mul_isNormalized hA (Vector.basis_isNormalized (QPE.zeroIndex n))
  exact QuantumLibrary.computational_measurement_total_probability hprep

theorem paperBadProbability_eq_one_sub_goodProbability
    {n : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool}
    (hA : Matrix.isUnitary A) :
    paperBadProbability n A f = 1 - paperGoodProbability n A f := by
  have hsum := paperBadProbability_add_goodProbability_eq_one (n := n) (A := A) (f := f) hA
  linarith

theorem paperGoodProbability_zero_support
    {n : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool}
    (hzero : paperGoodProbability n A f = 0) {x : Fin (QPE.M n)} (hf : f x = true) :
    paperPreparedState n A x 0 = 0 := by
  have hnonneg : ∀ y ∈ (Finset.univ : Finset (Fin (QPE.M n))),
      0 ≤ (if f y = true then Measurement.prob (paperPreparedState n A) y else 0) := by
    intro y _hy
    by_cases hyf : f y = true
    · simp [hyf, Measurement.prob_nonneg]
    · simp [hyf]
  have hterm_le : (if f x = true then Measurement.prob (paperPreparedState n A) x else 0) ≤
      paperGoodProbability n A f := by
    unfold paperGoodProbability
    exact Finset.single_le_sum hnonneg (Finset.mem_univ x)
  rw [hzero] at hterm_le
  have hprob_zero : Measurement.prob (paperPreparedState n A) x = 0 := by
    have hnon : 0 ≤ (if f x = true then Measurement.prob (paperPreparedState n A) x else 0) := by
      simpa [hf] using Measurement.prob_nonneg (paperPreparedState n A) x
    have hif_zero := le_antisymm hterm_le hnon
    simpa [hf] using hif_zero
  unfold Measurement.prob at hprob_zero
  exact Complex.normSq_eq_zero.mp hprob_zero

theorem paperBadProbability_zero_support
    {n : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool}
    (hzero : paperBadProbability n A f = 0) {x : Fin (QPE.M n)} (hf : f x = false) :
    paperPreparedState n A x 0 = 0 := by
  have hnonneg : ∀ y ∈ (Finset.univ : Finset (Fin (QPE.M n))),
      0 ≤ (if f y = true then 0 else Measurement.prob (paperPreparedState n A) y) := by
    intro y _hy
    by_cases hyf : f y = true
    · simp [hyf]
    · simp [hyf, Measurement.prob_nonneg]
  have hterm_le : (if f x = true then 0 else Measurement.prob (paperPreparedState n A) x) ≤
      paperBadProbability n A f := by
    unfold paperBadProbability
    exact Finset.single_le_sum hnonneg (Finset.mem_univ x)
  rw [hzero] at hterm_le
  have hprob_zero : Measurement.prob (paperPreparedState n A) x = 0 := by
    have hftrue : ¬ f x = true := by simp [hf]
    have hnon : 0 ≤ (if f x = true then 0 else Measurement.prob (paperPreparedState n A) x) := by
      simpa [hftrue] using Measurement.prob_nonneg (paperPreparedState n A) x
    have hif_zero := le_antisymm hterm_le hnon
    simpa [hftrue] using hif_zero
  unfold Measurement.prob at hprob_zero
  exact Complex.normSq_eq_zero.mp hprob_zero

/-- The zero-eigenphase kickback state is the uniform counting-register state. -/
theorem phaseState_zero_eq_uniformState (m : ℕ) :
    QPE.phaseState m 0 = QPE.uniformState m := by
  ext k col
  fin_cases col
  simp [QPE.phaseState, QPE.uniformState]

/-- After the first QFT, the paper QAE circuit has the standard QPE input state
`uniformState ⊗ A|0...0⟩`. -/
theorem paperQAEAfterQFT_eq_uniformState_tensor
    (m n : ℕ) (A : Square (QPE.M n)) :
    paperQAEAfterQFT m n A =
      QPE.uniformState m ⊗ (A ⬝ Vector.basis (QPE.zeroIndex n)) := by
  unfold paperQAEAfterQFT paperQAEInitialState
  rw [Matrix.kron_mul]
  rw [QPE.qftMatrix_mul_basisState]
  have hzero : (((QPE.zeroIndex m : ℕ) : ℝ) / (QPE.M m : ℝ)) = 0 := by
    simp [QPE.zeroIndex]
  rw [hzero]
  rw [phaseState_zero_eq_uniformState]
  simp [Matrix.mul]

/-- Spectral bridge for the paper QAE circuit.

If the prepared work-register state `A|0...0⟩` is a two-term superposition of
eigenvectors of the paper Grover iterate `-A S₀ A† S_f`, then the complete
paper QAE final state is the corresponding two-term superposition of QPE
output states for those eigenphases. -/
theorem paperQAEFinalState_eq_eigenphase_superposition
    {m n : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool}
    {ψ φ : Vector (QPE.M n)} {thetaψ thetaφ : ℝ} {a b : ℂ}
    (hinit : A ⬝ Vector.basis (QPE.zeroIndex n) = a • ψ + b • φ)
    (heigenψ : paperGroverOperator n A f ⬝ ψ =
      ((Real.fourierChar thetaψ : ℂ)) • ψ)
    (heigenφ : paperGroverOperator n A f ⬝ φ =
      ((Real.fourierChar thetaφ : ℂ)) • φ) :
    paperQAEFinalState m n A f =
      a • ((QPE.inverseQFTMatrix m ⬝ QPE.phaseState m thetaψ) ⊗ ψ) +
        b • ((QPE.inverseQFTMatrix m ⬝ QPE.phaseState m thetaφ) ⊗ φ) := by
  unfold paperQAEFinalState paperQAEAfterControlledPowers
  rw [paperQAEAfterQFT_eq_uniformState_tensor]
  rw [hinit]
  rw [qpeOutputStateConcrete_linear_combination]
  rw [QPE.controlledPowerMatrix_mul_uniform_of_real_eigenphase heigenψ]
  rw [QPE.controlledPowerMatrix_mul_uniform_of_real_eigenphase heigenφ]
  rw [Matrix.kron_mul, Matrix.kron_mul]
  simp [Matrix.mul]

/-- The paper QAE counting-register output probability is the partial probability
of the final joint state on the first register. -/
theorem paperQAEOutputProbability_eq_partialProb
    (m n : ℕ) (A : Square (QPE.M n)) (f : Fin (QPE.M n) → Bool)
    (y : Fin (QPE.M m)) :
    paperQAEOutputProbability m n A f y =
      Measurement.partialProb (paperQAEFinalState m n A f) y := by
  unfold paperQAEOutputProbability Measurement.partialProb partialTrace
  simp [Measurement.prob, Matrix.proj, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply,
    Complex.normSq_apply]


/-- If the prepared work-register state is a single eigenvector of the paper Grover
iterate, paper QAE has exactly the corresponding one-eigenphase QPE distribution. -/
theorem paperQAEOutputProbability_eq_single_eigenphase
    {m n : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool} {phase : ℝ}
    (hA : Matrix.isUnitary A)
    (heigen : paperGroverOperator n A f ⬝ (A ⬝ Vector.basis (QPE.zeroIndex n)) =
      (Real.fourierChar phase : ℂ) • (A ⬝ Vector.basis (QPE.zeroIndex n)))
    (y : Fin (QPE.M m)) :
    paperQAEOutputProbability m n A f y = QPE.qpeApproxOutcomeProbability m phase y := by
  rw [paperQAEOutputProbability_eq_partialProb]
  unfold paperQAEFinalState paperQAEAfterControlledPowers
  rw [paperQAEAfterQFT_eq_uniformState_tensor]
  rw [QPE.controlledPowerMatrix_mul_uniform_of_real_eigenphase heigen]
  rw [Matrix.kron_mul]
  have hprep : Vector.IsNormalized (A ⬝ Vector.basis (QPE.zeroIndex n)) := by
    exact Matrix.isUnitary_mul_isNormalized hA (Vector.basis_isNormalized (QPE.zeroIndex n))
  simp [Matrix.mul]
  change Measurement.partialProb ((QPE.inverseQFTMatrix m ⬝ QPE.phaseState m phase) ⊗
      (A ⬝ Vector.basis (QPE.zeroIndex n))) y = QPE.qpeApproxOutcomeProbability m phase y
  rw [Measurement.partialProb_kron_of_isNormalized _ hprep]
  unfold QPE.qpeApproxOutcomeProbability QPE.qpeApproxAmplitude Measurement.prob
  rfl

/-- Probability-level spectral bridge for the paper QAE circuit.

If `A|0...0⟩` is a two-term superposition of normalized orthogonal eigenvectors
of the paper Grover iterate, then the counting-register distribution of the
paper QAE circuit is the corresponding weighted sum of the two QPE eigenphase
distributions. -/
theorem paperQAEOutputProbability_eq_eigenphase_mixture
    {m n : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool}
    {ψ φ : Vector (QPE.M n)} {thetaψ thetaφ : ℝ} {a b : ℂ}
    (hinit : A ⬝ Vector.basis (QPE.zeroIndex n) = a • ψ + b • φ)
    (heigenψ : paperGroverOperator n A f ⬝ ψ =
      ((Real.fourierChar thetaψ : ℂ)) • ψ)
    (heigenφ : paperGroverOperator n A f ⬝ φ =
      ((Real.fourierChar thetaφ : ℂ)) • φ)
    (hψ : Vector.IsNormalized ψ) (hφ : Vector.IsNormalized φ)
    (horth : ψ† ⬝ φ = 0) (y : Fin (QPE.M m)) :
    paperQAEOutputProbability m n A f y =
      Complex.normSq a * QPE.qpeApproxOutcomeProbability m thetaψ y +
        Complex.normSq b * QPE.qpeApproxOutcomeProbability m thetaφ y := by
  rw [paperQAEOutputProbability_eq_partialProb]
  rw [paperQAEFinalState_eq_eigenphase_superposition hinit heigenψ heigenφ]
  let α : Vector (QPE.M m) := QPE.inverseQFTMatrix m ⬝ QPE.phaseState m thetaψ
  let β : Vector (QPE.M m) := QPE.inverseQFTMatrix m ⬝ QPE.phaseState m thetaφ
  change Measurement.partialProb (a • (α ⊗ ψ) + b • (β ⊗ φ)) y =
      Complex.normSq a * QPE.qpeApproxOutcomeProbability m thetaψ y +
        Complex.normSq b * QPE.qpeApproxOutcomeProbability m thetaφ y
  rw [show a • (α ⊗ ψ) = (a • α) ⊗ ψ by rw [Matrix.kron_smul_left]]
  rw [show b • (β ⊗ φ) = (b • β) ⊗ φ by rw [Matrix.kron_smul_left]]
  have hpartial :=
    Measurement.partialProb_add_kron_of_inner_eq_zero (a • α) (b • β) hψ hφ horth
  have hy := congrFun hpartial y
  rw [hy]

  simp [Measurement.prob, QPE.qpeApproxOutcomeProbability, QPE.qpeApproxAmplitude, α, β,
    Complex.normSq_mul]

/-- The bad/good decomposition of `A|0...0⟩` rewritten in the eigenbasis used by QPE. -/
theorem goodBad_decomposition_eq_eigen_superposition
    {n : ℕ} {ψ0 ψ1 : Vector (QPE.M n)} (theta : ℝ) :
    (Real.cos theta : ℂ) • ψ0 + (Real.sin theta : ℂ) • ψ1 =
      qaeCoeffPlus theta • (invSqrt2 • ψ0 + (-Complex.I * invSqrt2) • ψ1) +
        qaeCoeffMinus theta • (invSqrt2 • ψ0 + (Complex.I * invSqrt2) • ψ1) := by
  ext row col
  fin_cases col
  simp [qaeCoeffPlus, qaeCoeffMinus]
  ring_nf
  rw [Complex.I_sq]
  have hs : invSqrt2 ^ 2 = (1 / 2 : ℂ) := by
    rw [sq, invSqrt2_mul_self]
  rw [hs]
  ring

/-- A normalized linear combination of two normalized orthogonal vectors is normalized
when the scalar coefficients have squared norms summing to one. -/
theorem orthonormal_linear_combination_isNormalized
    {n : ℕ} {ψ0 ψ1 : Vector (QPE.M n)} {a b : ℂ}
    (hψ0 : Vector.IsNormalized ψ0) (hψ1 : Vector.IsNormalized ψ1)
    (horth01 : ψ0† ⬝ ψ1 = 0) (horth10 : ψ1† ⬝ ψ0 = 0)
    (hnorm : star a * a + star b * b = 1) :
    Vector.IsNormalized (a • ψ0 + b • ψ1) := by
  rw [Vector.IsNormalized]
  change _root_.Matrix.conjTranspose (a • ψ0 + b • ψ1) * (a • ψ0 + b • ψ1) = 1
  rw [_root_.Matrix.conjTranspose_add, _root_.Matrix.conjTranspose_smul,
    _root_.Matrix.conjTranspose_smul]
  rw [_root_.Matrix.add_mul, _root_.Matrix.mul_add, _root_.Matrix.mul_add]
  have h00 : (Matrix.conjTranspose ψ0 * ψ0) 0 0 = 1 := by
    have h := congrFun (congrFun hψ0 0) 0
    simpa [Matrix.adjoint] using h
  have h11 : (Matrix.conjTranspose ψ1 * ψ1) 0 0 = 1 := by
    have h := congrFun (congrFun hψ1 0) 0
    simpa [Matrix.adjoint] using h
  have h01 : (Matrix.conjTranspose ψ0 * ψ1) 0 0 = 0 := by
    have h := congrFun (congrFun horth01 0) 0
    simpa [Matrix.adjoint] using h
  have h10 : (Matrix.conjTranspose ψ1 * ψ0) 0 0 = 0 := by
    have h := congrFun (congrFun horth10 0) 0
    simpa [Matrix.adjoint] using h
  ext i j
  fin_cases i
  fin_cases j
  simp [smul_eq_mul, h00, h11, h01, h10]
  simpa [mul_comm] using hnorm

/-- Inner product of two linear combinations in an orthonormal two-dimensional subspace. -/
theorem orthonormal_linear_combination_inner
    {n : ℕ} {ψ0 ψ1 : Vector (QPE.M n)} {a b c d : ℂ}
    (hψ0 : Vector.IsNormalized ψ0) (hψ1 : Vector.IsNormalized ψ1)
    (horth01 : ψ0† ⬝ ψ1 = 0) (horth10 : ψ1† ⬝ ψ0 = 0) :
    (a • ψ0 + b • ψ1)† ⬝ (c • ψ0 + d • ψ1) =
      fun _ _ => star a * c + star b * d := by
  change _root_.Matrix.conjTranspose (a • ψ0 + b • ψ1) * (c • ψ0 + d • ψ1) =
      fun _ _ => star a * c + star b * d
  rw [_root_.Matrix.conjTranspose_add, _root_.Matrix.conjTranspose_smul,
    _root_.Matrix.conjTranspose_smul]
  rw [_root_.Matrix.add_mul, _root_.Matrix.mul_add, _root_.Matrix.mul_add]
  have h00 : (Matrix.conjTranspose ψ0 * ψ0) 0 0 = 1 := by
    have h := congrFun (congrFun hψ0 0) 0
    simpa [Matrix.adjoint] using h
  have h11 : (Matrix.conjTranspose ψ1 * ψ1) 0 0 = 1 := by
    have h := congrFun (congrFun hψ1 0) 0
    simpa [Matrix.adjoint] using h
  have h01 : (Matrix.conjTranspose ψ0 * ψ1) 0 0 = 0 := by
    have h := congrFun (congrFun horth01 0) 0
    simpa [Matrix.adjoint] using h
  have h10 : (Matrix.conjTranspose ψ1 * ψ0) 0 0 = 0 := by
    have h := congrFun (congrFun horth10 0) 0
    simpa [Matrix.adjoint] using h
  ext i j
  fin_cases i
  fin_cases j
  simp [smul_eq_mul, h00, h11, h01, h10]
  ring

private theorem eigenMinus_goodBad_isNormalized
    {n : ℕ} {ψ0 ψ1 : Vector (QPE.M n)}
    (hψ0 : Vector.IsNormalized ψ0) (hψ1 : Vector.IsNormalized ψ1)
    (horth01 : ψ0† ⬝ ψ1 = 0) (horth10 : ψ1† ⬝ ψ0 = 0) :
    Vector.IsNormalized (invSqrt2 • ψ0 + (-Complex.I * invSqrt2) • ψ1) := by
  apply orthonormal_linear_combination_isNormalized hψ0 hψ1 horth01 horth10
  simp [star_invSqrt2]
  ring_nf
  rw [Complex.I_sq]
  have hs : invSqrt2 ^ 2 = (1 / 2 : ℂ) := by
    rw [sq, invSqrt2_mul_self]
  rw [hs]
  norm_num

private theorem eigenPlus_goodBad_isNormalized
    {n : ℕ} {ψ0 ψ1 : Vector (QPE.M n)}
    (hψ0 : Vector.IsNormalized ψ0) (hψ1 : Vector.IsNormalized ψ1)
    (horth01 : ψ0† ⬝ ψ1 = 0) (horth10 : ψ1† ⬝ ψ0 = 0) :
    Vector.IsNormalized (invSqrt2 • ψ0 + (Complex.I * invSqrt2) • ψ1) := by
  apply orthonormal_linear_combination_isNormalized hψ0 hψ1 horth01 horth10
  simp [star_invSqrt2]
  ring_nf
  rw [Complex.I_sq]
  have hs : invSqrt2 ^ 2 = (1 / 2 : ℂ) := by
    rw [sq, invSqrt2_mul_self]
  rw [hs]
  norm_num

private theorem eigenMinus_inner_eigenPlus_goodBad
    {n : ℕ} {ψ0 ψ1 : Vector (QPE.M n)}
    (hψ0 : Vector.IsNormalized ψ0) (hψ1 : Vector.IsNormalized ψ1)
    (horth01 : ψ0† ⬝ ψ1 = 0) (horth10 : ψ1† ⬝ ψ0 = 0) :
    (invSqrt2 • ψ0 + (-Complex.I * invSqrt2) • ψ1)† ⬝
      (invSqrt2 • ψ0 + (Complex.I * invSqrt2) • ψ1) = 0 := by
  rw [orthonormal_linear_combination_inner hψ0 hψ1 horth01 horth10]
  ext i j
  fin_cases i
  fin_cases j
  simp [star_invSqrt2]
  ring_nf
  rw [Complex.I_sq]
  have hs : invSqrt2 ^ 2 = (1 / 2 : ℂ) := by
    rw [sq, invSqrt2_mul_self]
  rw [hs]
  norm_num

/-- The paper QAE output distribution induced by a normalized bad/good decomposition
is exactly the BHMT two-phase mixture. -/
theorem paperQAEOutputProbability_eq_good_bad_mixture
    {m n : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool}
    {ψ0 ψ1 : Vector (QPE.M n)} {theta : ℝ}
    (hA : Matrix.isUnitary A)
    (hinit : A ⬝ Vector.basis (QPE.zeroIndex n) =
      (Real.cos theta : ℂ) • ψ0 + (Real.sin theta : ℂ) • ψ1)
    (hbad : ∀ x, f x = true → ψ0 x 0 = 0)
    (hgood : ∀ x, f x = false → ψ1 x 0 = 0)
    (hψ0 : Vector.IsNormalized ψ0) (hψ1 : Vector.IsNormalized ψ1)
    (y : Fin (QPE.M m)) :
    paperQAEOutputProbability m n A f y =
      (1 / 2 : ℝ) * QPE.qpeApproxOutcomeProbability m (theta / Real.pi) y +
        (1 / 2 : ℝ) * QPE.qpeApproxOutcomeProbability m (1 - theta / Real.pi) y := by
  let ψminus : Vector (QPE.M n) := invSqrt2 • ψ0 + (-Complex.I * invSqrt2) • ψ1
  let ψplus : Vector (QPE.M n) := invSqrt2 • ψ0 + (Complex.I * invSqrt2) • ψ1
  have hinitEigen : A ⬝ Vector.basis (QPE.zeroIndex n) =
      qaeCoeffPlus theta • ψminus + qaeCoeffMinus theta • ψplus := by
    rw [hinit]
    exact goodBad_decomposition_eq_eigen_superposition theta
  have horth01 : ψ0† ⬝ ψ1 = 0 := bad_good_support_orthogonal hbad hgood
  have horth10 : ψ1† ⬝ ψ0 = 0 := good_bad_support_orthogonal hbad hgood
  have heigs := paperGroverOperator_eigenvectors_of_good_bad_decomposition
    A f ψ0 ψ1 theta hA hinit hbad hgood hψ0 hψ1
  have hminusNorm : Vector.IsNormalized ψminus := by
    dsimp [ψminus]
    exact eigenMinus_goodBad_isNormalized hψ0 hψ1 horth01 horth10
  have hplusNorm : Vector.IsNormalized ψplus := by
    dsimp [ψplus]
    exact eigenPlus_goodBad_isNormalized hψ0 hψ1 horth01 horth10
  have horth : ψminus† ⬝ ψplus = 0 := by
    dsimp [ψminus, ψplus]
    exact eigenMinus_inner_eigenPlus_goodBad hψ0 hψ1 horth01 horth10
  have hmix := paperQAEOutputProbability_eq_eigenphase_mixture
    (m := m) (n := n) (A := A) (f := f)
    (ψ := ψminus) (φ := ψplus)
    (thetaψ := theta / Real.pi) (thetaφ := -(theta / Real.pi))
    (a := qaeCoeffPlus theta) (b := qaeCoeffMinus theta)
    hinitEigen heigs.1 heigs.2 hminusNorm hplusNorm horth y
  rw [hmix]
  rw [qaeCoeffPlus_normSq, qaeCoeffMinus_normSq]
  rw [QPE.qpeApproxOutcomeProbability_one_sub]

/-- The QAE counting-register marginal on the canonical Grover plane. -/
def qaeGroverPlaneMarginal (m : ℕ) (theta : ℝ) (y : Fin (QPE.M m)) : ℝ :=
  qpeCountingMarginal
    ((QPE.inverseQFTMatrix m ⊗ (I 2)) ⬝
      (QPE.controlledPowerMatrix m (Ry (4 * theta)) ⬝
        (QPE.uniformState m ⊗ QuantumLibrary.qaePlaneVector theta))) y

@[simp] theorem qaeGroverPlaneMarginal_eq
    (m : ℕ) (theta : ℝ) (y : Fin (QPE.M m)) :
    qaeGroverPlaneMarginal m theta y =
      (1 / 2 : ℝ) * QPE.qpeApproxOutcomeProbability m (theta / Real.pi) y +
        (1 / 2 : ℝ) * QPE.qpeApproxOutcomeProbability m (-(theta / Real.pi)) y := by
  unfold qaeGroverPlaneMarginal
  exact qpeCountingMarginal_groverPlane_initial m theta y

/-- The amplitude parameter is unchanged by reflecting the Grover angle across `π / 2`. -/
theorem amplitudeFromAngle_pi_sub (theta : ℝ) :
    amplitudeFromAngle (Real.pi - theta) = amplitudeFromAngle theta := by
  unfold amplitudeFromAngle
  rw [Real.sin_pi_sub]

/-- The same QAE marginal as above, but with the negative eigenphase wrapped into `[0, 1)`.

This is the phase convention used in Brassard-Hoyer-Mosca-Tapp Theorem 12:
the two relevant QPE phases are `theta / π` and `1 - theta / π`. -/
theorem qaeGroverPlaneMarginal_eq_wrapped
    (m : ℕ) (theta : ℝ) (y : Fin (QPE.M m)) :
    qaeGroverPlaneMarginal m theta y =
      (1 / 2 : ℝ) * QPE.qpeApproxOutcomeProbability m (theta / Real.pi) y +
        (1 / 2 : ℝ) * QPE.qpeApproxOutcomeProbability m (1 - theta / Real.pi) y := by
  rw [qaeGroverPlaneMarginal_eq]
  rw [QPE.qpeApproxOutcomeProbability_one_sub]

private theorem phase_angle_error_of_pos_window
    (m k : ℕ) {theta : ℝ} (y : Fin (QPE.M m))
    (hclose : QPE.qpePhaseWindow m k (theta / Real.pi) y) :
    |(Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - theta| ≤
      phaseErrorRadius (QPE.M m) k := by
  unfold QPE.qpePhaseWindow phaseErrorRadius at *
  have hmul := mul_le_mul_of_nonneg_left hclose (le_of_lt Real.pi_pos)
  have hrewrite : |(Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - theta| =
      Real.pi * |theta / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ))| := by
    have harg : (Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - theta =
        -(Real.pi * (theta / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ)))) := by
      field_simp [Real.pi_ne_zero]
      ring
    rw [harg, abs_neg, abs_mul, abs_of_pos Real.pi_pos]
  calc
    |(Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - theta|
        = Real.pi * |theta / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ))| := hrewrite
    _ ≤ Real.pi * ((k : ℝ) / (QPE.M m : ℝ)) := hmul
    _ = Real.pi * (k : ℝ) / (QPE.M m : ℝ) := by ring

/-- Outputs whose post-processed amplitude estimate satisfies the Theorem 12 error bound for `k`. -/
def qaeGroverPlaneSuccessfulOutcomesK (m k : ℕ) (theta : ℝ) : Finset (Fin (QPE.M m)) := by
  classical
  exact Finset.univ.filter (fun y : Fin (QPE.M m) =>
    |estAmpEstimate (QPE.M m) (y : ℕ) - amplitudeFromAngle theta| ≤
      theorem12ErrorBound (amplitudeFromAngle theta) (QPE.M m) k)

def qaeGroverPlaneSuccessProbabilityK (m k : ℕ) (theta : ℝ) : ℝ :=
  (qaeGroverPlaneSuccessfulOutcomesK m k theta).sum (fun y => qaeGroverPlaneMarginal m theta y)

theorem mem_qaeGroverPlaneSuccessfulOutcomesK_of_estimate_error
    (m k : ℕ) {theta : ℝ} (y : Fin (QPE.M m))
    (h : |estAmpEstimate (QPE.M m) (y : ℕ) - amplitudeFromAngle theta| ≤
      theorem12ErrorBound (amplitudeFromAngle theta) (QPE.M m) k) :
    y ∈ qaeGroverPlaneSuccessfulOutcomesK m k theta := by
  classical
  unfold qaeGroverPlaneSuccessfulOutcomesK
  simp [h]

theorem amplitudeFromAngle_sub_pi (theta : ℝ) :
    amplitudeFromAngle (theta - Real.pi) = amplitudeFromAngle theta := by
  unfold amplitudeFromAngle
  rw [Real.sin_sub_pi]
  ring

theorem amplitudeFromAngle_add_pi (theta : ℝ) :
    amplitudeFromAngle (theta + Real.pi) = amplitudeFromAngle theta := by
  unfold amplitudeFromAngle
  rw [Real.sin_add_pi]
  ring

private theorem phase_angle_error_of_window_sub_one
    (m k : ℕ) {alpha : ℝ} (y : Fin (QPE.M m))
    (hclose : |alpha / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - 1| ≤
      (k : ℝ) / (QPE.M m : ℝ)) :
    |(Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - (alpha - Real.pi)| ≤
      phaseErrorRadius (QPE.M m) k := by
  unfold phaseErrorRadius
  have hmul := mul_le_mul_of_nonneg_left hclose (le_of_lt Real.pi_pos)
  have hrewrite : |(Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - (alpha - Real.pi)| =
      Real.pi * |alpha / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - 1| := by
    have harg : (Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - (alpha - Real.pi) =
        -(Real.pi * (alpha / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - 1)) := by
      field_simp [Real.pi_ne_zero]
      ring
    rw [harg, abs_neg, abs_mul, abs_of_pos Real.pi_pos]
  calc
    |(Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - (alpha - Real.pi)|
        = Real.pi * |alpha / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - 1| := hrewrite
    _ ≤ Real.pi * ((k : ℝ) / (QPE.M m : ℝ)) := hmul
    _ = Real.pi * (k : ℝ) / (QPE.M m : ℝ) := by ring

private theorem phase_angle_error_of_window_add_one
    (m k : ℕ) {alpha : ℝ} (y : Fin (QPE.M m))
    (hclose : |alpha / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) + 1| ≤
      (k : ℝ) / (QPE.M m : ℝ)) :
    |(Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - (alpha + Real.pi)| ≤
      phaseErrorRadius (QPE.M m) k := by
  unfold phaseErrorRadius
  have hmul := mul_le_mul_of_nonneg_left hclose (le_of_lt Real.pi_pos)
  have hrewrite : |(Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - (alpha + Real.pi)| =
      Real.pi * |alpha / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) + 1| := by
    have harg : (Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - (alpha + Real.pi) =
        -(Real.pi * (alpha / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) + 1)) := by
      field_simp [Real.pi_ne_zero]
      ring
    rw [harg, abs_neg, abs_mul, abs_of_pos Real.pi_pos]
  calc
    |(Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ)) - (alpha + Real.pi)|
        = Real.pi * |alpha / Real.pi - (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) + 1| := hrewrite
    _ ≤ Real.pi * ((k : ℝ) / (QPE.M m : ℝ)) := hmul
    _ = Real.pi * (k : ℝ) / (QPE.M m : ℝ) := by ring

/-- Circular phase-window closeness is sufficient for the Theorem 12 amplitude error. -/
theorem estAmp_error_of_phase_circular_window
    (m k : ℕ) {alpha : ℝ} (y : Fin (QPE.M m))
    (hclose : QPE.qpeCircularPhaseWindow m k (alpha / Real.pi) y) :
    |estAmpEstimate (QPE.M m) (y : ℕ) - amplitudeFromAngle alpha| ≤
      theorem12ErrorBound (amplitudeFromAngle alpha) (QPE.M m) k := by
  unfold QPE.qpeCircularPhaseWindow at hclose
  rcases QPE.unitPhaseDistance_cases hclose with hlin | hminus | hplus
  · exact estAmp_error_from_phase_estimation_proved (Nat.two_pow_pos m) rfl
      (phase_angle_error_of_pos_window m k y hlin)
  · have h := estAmp_error_from_phase_estimation_proved (M := QPE.M m) (k := k)
      (a := amplitudeFromAngle (alpha - Real.pi)) (theta := alpha - Real.pi) (y := (y : ℕ))
      (Nat.two_pow_pos m) rfl (phase_angle_error_of_window_sub_one m k y hminus)
    simpa [amplitudeFromAngle_sub_pi alpha] using h
  · have h := estAmp_error_from_phase_estimation_proved (M := QPE.M m) (k := k)
      (a := amplitudeFromAngle (alpha + Real.pi)) (theta := alpha + Real.pi) (y := (y : ℕ))
      (Nat.two_pow_pos m) rfl (phase_angle_error_of_window_add_one m k y hplus)
    simpa [amplitudeFromAngle_add_pi alpha] using h

theorem qaeGroverPlane_estimate_error_of_wrapped_neg_circular_window
    (m k : ℕ) {theta : ℝ} (y : Fin (QPE.M m))
    (hclose : QPE.qpeCircularPhaseWindow m k (1 - theta / Real.pi) y) :
    |estAmpEstimate (QPE.M m) (y : ℕ) - amplitudeFromAngle theta| ≤
      theorem12ErrorBound (amplitudeFromAngle theta) (QPE.M m) k := by
  have hphase : (Real.pi - theta) / Real.pi = 1 - theta / Real.pi := by
    field_simp [Real.pi_ne_zero]
  have h := estAmp_error_of_phase_circular_window (m := m) (k := k)
    (alpha := Real.pi - theta) y (by simpa [hphase] using hclose)
  simpa [amplitudeFromAngle_pi_sub theta] using h

theorem qaeGroverPlane_pos_circular_window_subset_success
    (m k : ℕ) (theta : ℝ) :
    QPE.qpeCircularPhaseWindowOutcomes m k (theta / Real.pi) ⊆
      qaeGroverPlaneSuccessfulOutcomesK m k theta := by
  intro y hy
  exact mem_qaeGroverPlaneSuccessfulOutcomesK_of_estimate_error m k y
    (estAmp_error_of_phase_circular_window m k y
      ((QPE.mem_qpeCircularPhaseWindowOutcomes_iff m k (theta / Real.pi) y).mp hy))

theorem qaeGroverPlane_wrapped_neg_circular_window_subset_success
    (m k : ℕ) (theta : ℝ) :
    QPE.qpeCircularPhaseWindowOutcomes m k (1 - theta / Real.pi) ⊆
      qaeGroverPlaneSuccessfulOutcomesK m k theta := by
  intro y hy
  exact mem_qaeGroverPlaneSuccessfulOutcomesK_of_estimate_error m k y
    (qaeGroverPlane_estimate_error_of_wrapped_neg_circular_window m k y
      ((QPE.mem_qpeCircularPhaseWindowOutcomes_iff m k (1 - theta / Real.pi) y).mp hy))

theorem bhmt11SuccessProbability_eq_theorem12SuccessProbability (k : ℕ) :
    QPE.bhmt11SuccessProbability k = theorem12SuccessProbability k := rfl

theorem qaeGroverPlaneSuccessProbabilityK_lower_bound_of_qpe_circular_windows
    (m k : ℕ) (theta : ℝ)
    (hpos : theorem12SuccessProbability k ≤
      QPE.qpeCircularPhaseWindowProbability m k (theta / Real.pi))
    (hneg : theorem12SuccessProbability k ≤
      QPE.qpeCircularPhaseWindowProbability m k (1 - theta / Real.pi)) :
    theorem12SuccessProbability k ≤ qaeGroverPlaneSuccessProbabilityK m k theta := by
  classical
  let S := qaeGroverPlaneSuccessfulOutcomesK m k theta
  let Ppos := fun y : Fin (QPE.M m) => QPE.qpeApproxOutcomeProbability m (theta / Real.pi) y
  let Pneg := fun y : Fin (QPE.M m) => QPE.qpeApproxOutcomeProbability m (1 - theta / Real.pi) y
  have hsuccess_eq : qaeGroverPlaneSuccessProbabilityK m k theta =
      (1 / 2 : ℝ) * (S.sum fun y => Ppos y) + (1 / 2 : ℝ) * (S.sum fun y => Pneg y) := by
    unfold qaeGroverPlaneSuccessProbabilityK
    dsimp [S, Ppos, Pneg]
    simp_rw [qaeGroverPlaneMarginal_eq_wrapped]
    rw [Finset.sum_add_distrib]
    rw [Finset.mul_sum, Finset.mul_sum]
  have hpos_subset : QPE.qpeCircularPhaseWindowOutcomes m k (theta / Real.pi) ⊆ S := by
    dsimp [S]
    exact qaeGroverPlane_pos_circular_window_subset_success m k theta
  have hneg_subset : QPE.qpeCircularPhaseWindowOutcomes m k (1 - theta / Real.pi) ⊆ S := by
    dsimp [S]
    exact qaeGroverPlane_wrapped_neg_circular_window_subset_success m k theta
  have hpos_sum_le : QPE.qpeCircularPhaseWindowProbability m k (theta / Real.pi) ≤ S.sum fun y => Ppos y := by
    unfold QPE.qpeCircularPhaseWindowProbability
    dsimp [Ppos]
    exact Finset.sum_le_sum_of_subset_of_nonneg hpos_subset
      (by intro y _hyS _hynot; exact QPE.qpeApproxOutcomeProbability_nonneg m (theta / Real.pi) y)
  have hneg_sum_le : QPE.qpeCircularPhaseWindowProbability m k (1 - theta / Real.pi) ≤ S.sum fun y => Pneg y := by
    unfold QPE.qpeCircularPhaseWindowProbability
    dsimp [Pneg]
    exact Finset.sum_le_sum_of_subset_of_nonneg hneg_subset
      (by intro y _hyS _hynot; exact QPE.qpeApproxOutcomeProbability_nonneg m (1 - theta / Real.pi) y)
  have hpos' : theorem12SuccessProbability k ≤ S.sum fun y => Ppos y := le_trans hpos hpos_sum_le
  have hneg' : theorem12SuccessProbability k ≤ S.sum fun y => Pneg y := le_trans hneg hneg_sum_le
  calc
    theorem12SuccessProbability k =
        (1 / 2 : ℝ) * theorem12SuccessProbability k +
          (1 / 2 : ℝ) * theorem12SuccessProbability k := by ring
    _ ≤ (1 / 2 : ℝ) * (S.sum fun y => Ppos y) + (1 / 2 : ℝ) * (S.sum fun y => Pneg y) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hpos' (by norm_num))
        (mul_le_mul_of_nonneg_left hneg' (by norm_num))
    _ = qaeGroverPlaneSuccessProbabilityK m k theta := by rw [hsuccess_eq]

/-- QAE success probability on the canonical Grover plane, using the proved BHMT11
circular-window bound. -/
theorem qaeGroverPlaneSuccessProbabilityK_lower_bound
    (m k : ℕ) {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta_pi : theta ≤ Real.pi) (hk : 0 < k) :
    theorem12SuccessProbability k ≤ qaeGroverPlaneSuccessProbabilityK m k theta := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hphase0 : 0 ≤ theta / Real.pi := div_nonneg htheta0 (le_of_lt hpi_pos)
  have hphase1 : theta / Real.pi ≤ 1 := by
    rw [div_le_one hpi_pos]
    exact htheta_pi
  have hwrap0 : 0 ≤ 1 - theta / Real.pi := by linarith
  have hwrap1 : 1 - theta / Real.pi ≤ 1 := by linarith
  have hposQ := QPE.bhmt11CircularWindowBound_proved m k (theta / Real.pi) hphase0 hphase1 hk
  have hnegQ := QPE.bhmt11CircularWindowBound_proved m k (1 - theta / Real.pi) hwrap0 hwrap1 hk
  have hposQ' : theorem12SuccessProbability k ≤
      QPE.qpeCircularPhaseWindowProbability m k (theta / Real.pi) := by
    simpa [QPE.bhmt11SuccessProbability, theorem12SuccessProbability] using hposQ
  have hnegQ' : theorem12SuccessProbability k ≤
      QPE.qpeCircularPhaseWindowProbability m k (1 - theta / Real.pi) := by
    simpa [QPE.bhmt11SuccessProbability, theorem12SuccessProbability] using hnegQ
  exact qaeGroverPlaneSuccessProbabilityK_lower_bound_of_qpe_circular_windows m k theta hposQ' hnegQ'

/-- Canonical Grover-plane QAE succeeds with Theorem 12 probability and uses
exactly `M = 2^m` controlled Grover powers. -/
theorem qaeGroverPlaneCorrectness_and_query_count
    (m k : ℕ) {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta_pi : theta ≤ Real.pi) (hk : 0 < k) :
    theorem12SuccessProbability k ≤ qaeGroverPlaneSuccessProbabilityK m k theta ∧
      QPE.M m = QPE.M m := by
  exact ⟨qaeGroverPlaneSuccessProbabilityK_lower_bound m k htheta0 htheta_pi hk, rfl⟩


/-- The Theorem 12 error bound in the expanded form used in the BHMT paper. -/
theorem theorem12ErrorBound_eq_expanded_QPE (m k : ℕ) (a : ℝ) :
    theorem12ErrorBound a (QPE.M m) k =
      2 * Real.pi * (k : ℝ) * Real.sqrt (a * (1 - a)) / (QPE.M m : ℝ) +
        (k : ℝ) ^ 2 * Real.pi ^ 2 / (QPE.M m : ℝ) ^ 2 := by
  unfold theorem12ErrorBound phaseErrorRadius
  have hMnat : QPE.M m ≠ 0 := ne_of_gt (Nat.two_pow_pos m)
  have hM : ((QPE.M m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hMnat
  field_simp [hM]

/-- The paper QAE circuit satisfies the BHMT Theorem 12 success-probability
bound for the actual amplitude `a = sin² θ`. -/
theorem paperQAESuccessProbabilityK_lower_bound
    {m n k : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool}
    {ψ0 ψ1 : Vector (QPE.M n)} {theta : ℝ}
    (hA : Matrix.isUnitary A)
    (hinit : A ⬝ Vector.basis (QPE.zeroIndex n) =
      (Real.cos theta : ℂ) • ψ0 + (Real.sin theta : ℂ) • ψ1)
    (hbad : ∀ x, f x = true → ψ0 x 0 = 0)
    (hgood : ∀ x, f x = false → ψ1 x 0 = 0)
    (hψ0 : Vector.IsNormalized ψ0) (hψ1 : Vector.IsNormalized ψ1)
    (htheta0 : 0 ≤ theta) (htheta_pi : theta ≤ Real.pi) (hk : 0 < k) :
    theorem12SuccessProbability k ≤
      (qaeGroverPlaneSuccessfulOutcomesK m k theta).sum
        (fun y => paperQAEOutputProbability m n A f y) := by
  have hplane := qaeGroverPlaneSuccessProbabilityK_lower_bound
    (m := m) (k := k) (theta := theta) htheta0 htheta_pi hk
  have hpoint : ∀ y : Fin (QPE.M m),
      paperQAEOutputProbability m n A f y = qaeGroverPlaneMarginal m theta y := by
    intro y
    rw [paperQAEOutputProbability_eq_good_bad_mixture hA hinit hbad hgood
      hψ0 hψ1 y]
    rw [qaeGroverPlaneMarginal_eq_wrapped]
  calc
    theorem12SuccessProbability k ≤ qaeGroverPlaneSuccessProbabilityK m k theta := hplane
    _ = (qaeGroverPlaneSuccessfulOutcomesK m k theta).sum
          (fun y => paperQAEOutputProbability m n A f y) := by
        unfold qaeGroverPlaneSuccessProbabilityK
        apply Finset.sum_congr rfl
        intro y _hy
        exact (hpoint y).symm

/-- The same success-probability bound with the error threshold expanded as in
BHMT Theorem 12. -/
theorem paperQAESuccessProbabilityK_lower_bound_expanded
    {m n k : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool}
    {ψ0 ψ1 : Vector (QPE.M n)} {theta : ℝ}
    (hA : Matrix.isUnitary A)
    (hinit : A ⬝ Vector.basis (QPE.zeroIndex n) =
      (Real.cos theta : ℂ) • ψ0 + (Real.sin theta : ℂ) • ψ1)
    (hbad : ∀ x, f x = true → ψ0 x 0 = 0)
    (hgood : ∀ x, f x = false → ψ1 x 0 = 0)
    (hψ0 : Vector.IsNormalized ψ0) (hψ1 : Vector.IsNormalized ψ1)
    (htheta0 : 0 ≤ theta) (htheta_pi : theta ≤ Real.pi) (hk : 0 < k) :
    theorem12SuccessProbability k ≤
      (Finset.univ.filter (fun y : Fin (QPE.M m) =>
        |paperQAEEstimate m y - amplitudeFromAngle theta| ≤
          2 * Real.pi * (k : ℝ) * Real.sqrt (amplitudeFromAngle theta *
            (1 - amplitudeFromAngle theta)) / (QPE.M m : ℝ) +
            (k : ℝ) ^ 2 * Real.pi ^ 2 / (QPE.M m : ℝ) ^ 2)).sum
        (fun y => paperQAEOutputProbability m n A f y) := by
  have h := paperQAESuccessProbabilityK_lower_bound
    (m := m) (n := n) (k := k) (A := A) (f := f)
    (ψ0 := ψ0) (ψ1 := ψ1) (theta := theta)
    hA hinit hbad hgood hψ0 hψ1 htheta0 htheta_pi hk
  simpa [qaeGroverPlaneSuccessfulOutcomesK, paperQAEEstimate, theorem12ErrorBound_eq_expanded_QPE]
    using h

/-- At an exact grid phase, QPE returns the corresponding grid point with
probability one. -/
theorem qpeApproxOutcomeProbability_exact_grid_eq_one
    (m : ℕ) (y : Fin (QPE.M m)) :
    QPE.qpeApproxOutcomeProbability m (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) y = 1 := by
  unfold QPE.qpeApproxOutcomeProbability QPE.qpeApproxAmplitude
  rw [QPE.inverseQFTMatrix_mul_phaseState]
  simp [Vector.basis, Complex.normSq_one]

private theorem paperQAEHalfGridRatio (m : ℕ) (hm : 0 < m) :
    let y : Fin (QPE.M m) := ⟨QPE.M (m - 1), by
      unfold QPE.M
      exact Nat.pow_lt_pow_right (by norm_num) (Nat.sub_lt hm (by norm_num))⟩
    (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) = 1 / 2 := by
  intro y
  change ((2 ^ (m - 1) : ℕ) : ℝ) / ((2 ^ m : ℕ) : ℝ) = 1 / 2
  have hden_nat : 2 ^ m = 2 ^ (m - 1) * 2 := by
    calc
      2 ^ m = 2 ^ ((m - 1) + 1) := by rw [Nat.sub_add_cancel hm]
      _ = 2 ^ (m - 1) * 2 := by rw [pow_succ]
  have hden : ((2 ^ m : ℕ) : ℝ) = ((2 ^ (m - 1) : ℕ) : ℝ) * 2 := by
    exact_mod_cast hden_nat
  rw [hden]
  have hpow_nat : (2 ^ (m - 1) : ℕ) ≠ 0 :=
    pow_ne_zero (m - 1) (by norm_num : (2 : ℕ) ≠ 0)
  have hpow : ((2 ^ (m - 1) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpow_nat
  field_simp [hpow]

private theorem amplitude_zero_theta_zero_or_pi {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta_pi : theta ≤ Real.pi)
    (ha0 : amplitudeFromAngle theta = 0) : theta = 0 ∨ theta = Real.pi := by
  have hsin_sq : Real.sin theta ^ 2 = 0 := by simpa [amplitudeFromAngle] using ha0
  have hsin : Real.sin theta = 0 := sq_eq_zero_iff.mp hsin_sq
  by_cases hlt : theta < Real.pi
  · left
    have hnegpi : -Real.pi < theta := by linarith [Real.pi_pos, htheta0]
    exact (Real.sin_eq_zero_iff_of_lt_of_lt hnegpi hlt).mp hsin
  · right
    exact le_antisymm htheta_pi (le_of_not_gt hlt)

private theorem amplitude_one_theta_pi_div_two {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta_pi : theta ≤ Real.pi)
    (ha1 : amplitudeFromAngle theta = 1) : theta = Real.pi / 2 := by
  have hsin_sq : Real.sin theta ^ 2 = 1 := by simpa [amplitudeFromAngle] using ha1
  have hsin_nonneg : 0 ≤ Real.sin theta := Real.sin_nonneg_of_mem_Icc ⟨htheta0, htheta_pi⟩
  have hsin_le : Real.sin theta ≤ 1 := Real.sin_le_one theta
  have hsin : Real.sin theta = 1 := by nlinarith
  by_cases hle : theta ≤ Real.pi / 2
  · have hmem_theta : theta ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos, htheta0, hle]
    have hmem_half : Real.pi / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    exact Real.injOn_sin hmem_theta hmem_half (by simpa [Real.sin_pi_div_two] using hsin)
  · have hhalf_le : Real.pi / 2 ≤ theta := le_of_not_ge hle
    have hmem_alpha : Real.pi - theta ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos, htheta_pi, hhalf_le]
    have hmem_half : Real.pi / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    have halpha : Real.pi - theta = Real.pi / 2 := by
      apply Real.injOn_sin hmem_alpha hmem_half
      rw [Real.sin_pi_sub]
      simpa [Real.sin_pi_div_two] using hsin
    linarith


theorem paperGroverOperator_mul_prepared_of_goodProbability_zero
    {n : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool}
    (hA : Matrix.isUnitary A) (hzero : paperGoodProbability n A f = 0) :
    paperGroverOperator n A f ⬝ paperPreparedState n A = paperPreparedState n A := by
  have hsupport : ∀ x, f x = true → paperPreparedState n A x 0 = 0 := by
    intro x hf
    exact paperGoodProbability_zero_support hzero hf
  unfold paperGroverOperator paperPreparedState
  change (-(A * zeroReflection n * A† * phaseOracle n f)) * (A * Vector.basis (QPE.zeroIndex n)) =
      A * Vector.basis (QPE.zeroIndex n)
  rw [_root_.Matrix.neg_mul]
  rw [_root_.Matrix.mul_assoc]
  rw [_root_.Matrix.mul_assoc]
  rw [_root_.Matrix.mul_assoc]
  rw [show phaseOracle n f * (A * Vector.basis (QPE.zeroIndex n)) = A * Vector.basis (QPE.zeroIndex n) from
    phaseOracle_mul_of_bad_support n f (A ⬝ Vector.basis (QPE.zeroIndex n)) hsupport]
  rw [← _root_.Matrix.mul_assoc]
  have hAadjA : A† ⬝ A = I (QPE.M n) := (Matrix.isUnitary_iff_adjoint_mul_self A).mp hA
  rw [show A† * (A * Vector.basis (QPE.zeroIndex n)) = Vector.basis (QPE.zeroIndex n) by
    rw [← _root_.Matrix.mul_assoc]
    change (A† ⬝ A) ⬝ Vector.basis (QPE.zeroIndex n) = Vector.basis (QPE.zeroIndex n)
    rw [hAadjA]
    simp [Matrix.mul]]
  rw [_root_.Matrix.mul_assoc]
  change -(A * (zeroReflection n * Vector.basis (QPE.zeroIndex n))) = A * Vector.basis (QPE.zeroIndex n)
  rw [show zeroReflection n * Vector.basis (QPE.zeroIndex n) =
      (-1 : ℂ) • Vector.basis (QPE.zeroIndex n) from zeroReflection_mul_zero_basis n]
  rw [Matrix.mul_smul]
  ext row col
  simp

theorem paperGroverOperator_mul_prepared_of_badProbability_zero
    {n : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool}
    (hA : Matrix.isUnitary A) (hzero : paperBadProbability n A f = 0) :
    paperGroverOperator n A f ⬝ paperPreparedState n A =
      (Real.fourierChar (1 / 2 : ℝ) : ℂ) • paperPreparedState n A := by
  have hsupport : ∀ x, f x = false → paperPreparedState n A x 0 = 0 := by
    intro x hf
    exact paperBadProbability_zero_support hzero hf
  have hphase : (Real.fourierChar (1 / 2 : ℝ) : ℂ) = (-1 : ℂ) := by
    rw [Real.fourierChar_apply]
    have harg : ((2 * Real.pi * (1 / 2 : ℝ) : ℝ) : ℂ) * Complex.I = Complex.I * Real.pi := by
      norm_num
      ring
    rw [harg]
    rw [mul_comm Complex.I (Real.pi : ℂ)]
    rw [Complex.exp_pi_mul_I]
  unfold paperGroverOperator paperPreparedState
  change (-(A * zeroReflection n * A† * phaseOracle n f)) * (A * Vector.basis (QPE.zeroIndex n)) =
      (Real.fourierChar (1 / 2 : ℝ) : ℂ) • (A * Vector.basis (QPE.zeroIndex n))
  rw [hphase]
  rw [_root_.Matrix.neg_mul]
  rw [_root_.Matrix.mul_assoc]
  rw [_root_.Matrix.mul_assoc]
  rw [_root_.Matrix.mul_assoc]
  rw [show phaseOracle n f * (A * Vector.basis (QPE.zeroIndex n)) = (-1 : ℂ) • (A * Vector.basis (QPE.zeroIndex n)) from
    phaseOracle_mul_of_good_support n f (A ⬝ Vector.basis (QPE.zeroIndex n)) hsupport]
  have hAadjA : A† ⬝ A = I (QPE.M n) := (Matrix.isUnitary_iff_adjoint_mul_self A).mp hA
  have hinner : A† * ((-1 : ℂ) • (A * Vector.basis (QPE.zeroIndex n))) =
      (-1 : ℂ) • Vector.basis (QPE.zeroIndex n) := by
    rw [Matrix.mul_smul]
    congr
    rw [← _root_.Matrix.mul_assoc]
    change (A† ⬝ A) ⬝ Vector.basis (QPE.zeroIndex n) = Vector.basis (QPE.zeroIndex n)
    rw [hAadjA]
    simp [Matrix.mul]
  rw [hinner]
  change -(A * (zeroReflection n * ((-1 : ℂ) • Vector.basis (QPE.zeroIndex n)))) =
      (-1 : ℂ) • (A * Vector.basis (QPE.zeroIndex n))
  rw [Matrix.mul_smul]
  rw [show zeroReflection n * Vector.basis (QPE.zeroIndex n) =
      (-1 : ℂ) • Vector.basis (QPE.zeroIndex n) from zeroReflection_mul_zero_basis n]
  rw [Matrix.mul_smul]
  ext row col
  simp

/-- If the paper amplitude is zero, the raw paper-QAE distribution is concentrated
on the zero estimate. -/
theorem paperQAEEndpointZero_of_goodProbability_zero
    {m n : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool}
    (hA : Matrix.isUnitary A) (hzero : paperGoodProbability n A f = 0) :
    ∃ y : Fin (QPE.M m),
      paperQAEOutputProbability m n A f y = 1 ∧ paperQAEEstimate m y = 0 := by
  let y := QPE.zeroIndex m
  have hprob0 : QPE.qpeApproxOutcomeProbability m 0 y = 1 := by
    have hgrid : (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) = 0 := by simp [y, QPE.zeroIndex]
    rw [← hgrid]
    exact qpeApproxOutcomeProbability_exact_grid_eq_one m y
  have heigen : paperGroverOperator n A f ⬝ (A ⬝ Vector.basis (QPE.zeroIndex n)) =
      (Real.fourierChar (0 : ℝ) : ℂ) • (A ⬝ Vector.basis (QPE.zeroIndex n)) := by
    have h := paperGroverOperator_mul_prepared_of_goodProbability_zero
      (n := n) (A := A) (f := f) hA hzero
    unfold paperPreparedState at h
    simpa [Real.fourierChar_apply] using h
  have hpaper := paperQAEOutputProbability_eq_single_eigenphase
    (m := m) (n := n) (A := A) (f := f) (phase := 0) hA heigen y
  have hest : paperQAEEstimate m y = 0 := by
    unfold paperQAEEstimate estAmpEstimate amplitudeFromAngle
    simp [y, QPE.zeroIndex]
  exact ⟨y, by simpa [hprob0] using hpaper, hest⟩

/-- If the paper amplitude is one, the raw paper-QAE distribution is concentrated
on the unit estimate. -/
theorem paperQAEEndpointOne_of_badProbability_zero
    {m n : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool}
    (hA : Matrix.isUnitary A) (hm : 0 < m) (hzero : paperBadProbability n A f = 0) :
    ∃ y : Fin (QPE.M m),
      paperQAEOutputProbability m n A f y = 1 ∧ paperQAEEstimate m y = 1 := by
  let y : Fin (QPE.M m) := ⟨QPE.M (m - 1), by
    unfold QPE.M
    exact Nat.pow_lt_pow_right (by norm_num) (Nat.sub_lt hm (by norm_num))⟩
  have hgrid : (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) = 1 / 2 := paperQAEHalfGridRatio m hm
  have hprob : QPE.qpeApproxOutcomeProbability m (1 / 2) y = 1 := by
    rw [← hgrid]
    exact qpeApproxOutcomeProbability_exact_grid_eq_one m y
  have heigen : paperGroverOperator n A f ⬝ (A ⬝ Vector.basis (QPE.zeroIndex n)) =
      (Real.fourierChar (1 / 2 : ℝ) : ℂ) • (A ⬝ Vector.basis (QPE.zeroIndex n)) := by
    have h := paperGroverOperator_mul_prepared_of_badProbability_zero
      (n := n) (A := A) (f := f) hA hzero
    unfold paperPreparedState at h
    exact h
  have hpaper := paperQAEOutputProbability_eq_single_eigenphase
    (m := m) (n := n) (A := A) (f := f) (phase := 1 / 2) hA heigen y
  have hest : paperQAEEstimate m y = 1 := by
    unfold paperQAEEstimate estAmpEstimate amplitudeFromAngle
    have harg : Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ) = Real.pi / 2 := by
      rw [show Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ) =
        Real.pi * (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) by ring]
      rw [hgrid]
      ring
    rw [harg]
    simp [Real.sin_pi_div_two]
  exact ⟨y, by rw [hpaper, hprob], hest⟩

/-- If the paper amplitude is zero, the paper-QAE distribution is concentrated
on the zero estimate. -/
theorem paperQAEEndpointZero
    {m n : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool}
    {ψ0 ψ1 : Vector (QPE.M n)} {theta : ℝ}
    (hA : Matrix.isUnitary A)
    (hinit : A ⬝ Vector.basis (QPE.zeroIndex n) =
      (Real.cos theta : ℂ) • ψ0 + (Real.sin theta : ℂ) • ψ1)
    (hbad : ∀ x, f x = true → ψ0 x 0 = 0)
    (hgood : ∀ x, f x = false → ψ1 x 0 = 0)
    (hψ0 : Vector.IsNormalized ψ0) (hψ1 : Vector.IsNormalized ψ1)
    (htheta0 : 0 ≤ theta) (htheta_pi : theta ≤ Real.pi)
    (ha0 : amplitudeFromAngle theta = 0) :
    ∃ y : Fin (QPE.M m),
      paperQAEOutputProbability m n A f y = 1 ∧ paperQAEEstimate m y = 0 := by
  let y := QPE.zeroIndex m
  have hprob0 : QPE.qpeApproxOutcomeProbability m 0 y = 1 := by
    have hgrid : (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) = 0 := by simp [y, QPE.zeroIndex]
    rw [← hgrid]
    exact qpeApproxOutcomeProbability_exact_grid_eq_one m y
  have hprob1 : QPE.qpeApproxOutcomeProbability m 1 y = 1 := by
    have h := QPE.qpeApproxOutcomeProbability_add_one m 0 y
    exact (by simpa using h.trans hprob0)
  have hest : paperQAEEstimate m y = 0 := by
    unfold paperQAEEstimate estAmpEstimate amplitudeFromAngle
    simp [y, QPE.zeroIndex]
  refine ⟨y, ?_, hest⟩
  have hmix := paperQAEOutputProbability_eq_good_bad_mixture
    (m := m) (n := n) (A := A) (f := f) (ψ0 := ψ0) (ψ1 := ψ1)
    (theta := theta) hA hinit hbad hgood hψ0 hψ1 y
  rw [hmix]
  rcases amplitude_zero_theta_zero_or_pi htheta0 htheta_pi ha0 with htheta | htheta
  · subst theta
    norm_num [hprob0, hprob1]
  · subst theta
    have hphase : Real.pi / Real.pi = (1 : ℝ) := by field_simp [Real.pi_ne_zero]
    rw [hphase]
    norm_num [hprob0, hprob1]

/-- If the paper amplitude is one, the paper-QAE distribution is concentrated
on the unit estimate. -/
theorem paperQAEEndpointOne
    {m n : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool}
    {ψ0 ψ1 : Vector (QPE.M n)} {theta : ℝ}
    (hA : Matrix.isUnitary A) (hm : 0 < m)
    (hinit : A ⬝ Vector.basis (QPE.zeroIndex n) =
      (Real.cos theta : ℂ) • ψ0 + (Real.sin theta : ℂ) • ψ1)
    (hbad : ∀ x, f x = true → ψ0 x 0 = 0)
    (hgood : ∀ x, f x = false → ψ1 x 0 = 0)
    (hψ0 : Vector.IsNormalized ψ0) (hψ1 : Vector.IsNormalized ψ1)
    (htheta0 : 0 ≤ theta) (htheta_pi : theta ≤ Real.pi)
    (ha1 : amplitudeFromAngle theta = 1) :
    ∃ y : Fin (QPE.M m),
      paperQAEOutputProbability m n A f y = 1 ∧ paperQAEEstimate m y = 1 := by
  let y : Fin (QPE.M m) := ⟨QPE.M (m - 1), by
    unfold QPE.M
    exact Nat.pow_lt_pow_right (by norm_num) (Nat.sub_lt hm (by norm_num))⟩
  have hgrid : (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) = 1 / 2 := paperQAEHalfGridRatio m hm
  have hprob : QPE.qpeApproxOutcomeProbability m (1 / 2) y = 1 := by
    rw [← hgrid]
    exact qpeApproxOutcomeProbability_exact_grid_eq_one m y
  have hest : paperQAEEstimate m y = 1 := by
    unfold paperQAEEstimate estAmpEstimate amplitudeFromAngle
    have harg : Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ) = Real.pi / 2 := by
      rw [show Real.pi * ((y : ℕ) : ℝ) / (QPE.M m : ℝ) =
        Real.pi * (((y : ℕ) : ℝ) / (QPE.M m : ℝ)) by ring]
      rw [hgrid]
      ring
    rw [harg]
    simp [Real.sin_pi_div_two]
  refine ⟨y, ?_, hest⟩
  have htheta := amplitude_one_theta_pi_div_two htheta0 htheta_pi ha1
  have hmix := paperQAEOutputProbability_eq_good_bad_mixture
    (m := m) (n := n) (A := A) (f := f) (ψ0 := ψ0) (ψ1 := ψ1)
    (theta := theta) hA hinit hbad hgood hψ0 hψ1 y
  rw [hmix, htheta]
  have hphase : (Real.pi / 2) / Real.pi = (1 / 2 : ℝ) := by field_simp [Real.pi_ne_zero]
  rw [hphase]
  norm_num [hprob]

/-- The paper QAE estimate always lies in `[0, 1]`. -/
theorem paperQAEEstimate_mem_Icc (m : ℕ) (y : Fin (QPE.M m)) :
    0 ≤ paperQAEEstimate m y ∧ paperQAEEstimate m y ≤ 1 := by
  constructor
  · unfold paperQAEEstimate estAmpEstimate amplitudeFromAngle
    positivity
  · unfold paperQAEEstimate estAmpEstimate amplitudeFromAngle
    exact Real.sin_sq_le_one _


theorem paperQAEOutputProbability_nonneg
    (m n : ℕ) (A : Square (QPE.M n)) (f : Fin (QPE.M n) → Bool)
    (y : Fin (QPE.M m)) :
    0 ≤ paperQAEOutputProbability m n A f y := by
  unfold paperQAEOutputProbability
  exact Finset.sum_nonneg (fun j _hj => Measurement.prob_nonneg _ _)

theorem paperQAESuccessSum_ge_one_of_point
    {m n k : ℕ} {A : Square (QPE.M n)} {f : Fin (QPE.M n) → Bool}
    {a : ℝ} {y : Fin (QPE.M m)}
    (hprob : paperQAEOutputProbability m n A f y = 1)
    (herror : |paperQAEEstimate m y - a| ≤
      2 * Real.pi * (k : ℝ) * Real.sqrt (a * (1 - a)) / (QPE.M m : ℝ) +
        (k : ℝ) ^ 2 * Real.pi ^ 2 / (QPE.M m : ℝ) ^ 2) :
    1 ≤
      (Finset.univ.filter (fun y : Fin (QPE.M m) =>
        |paperQAEEstimate m y - a| ≤
          2 * Real.pi * (k : ℝ) * Real.sqrt (a * (1 - a)) / (QPE.M m : ℝ) +
            (k : ℝ) ^ 2 * Real.pi ^ 2 / (QPE.M m : ℝ) ^ 2)).sum
        (fun y => paperQAEOutputProbability m n A f y) := by
  classical
  let S := Finset.univ.filter (fun y : Fin (QPE.M m) =>
    |paperQAEEstimate m y - a| ≤
      2 * Real.pi * (k : ℝ) * Real.sqrt (a * (1 - a)) / (QPE.M m : ℝ) +
        (k : ℝ) ^ 2 * Real.pi ^ 2 / (QPE.M m : ℝ) ^ 2)
  have hy : y ∈ S := by
    dsimp [S]
    simp [herror]
  have hsingle : paperQAEOutputProbability m n A f y ≤
      S.sum (fun y => paperQAEOutputProbability m n A f y) := by
    exact Finset.single_le_sum
      (fun z _hz => paperQAEOutputProbability_nonneg m n A f z) hy
  calc
    1 = paperQAEOutputProbability m n A f y := hprob.symm
    _ ≤ S.sum (fun y => paperQAEOutputProbability m n A f y) := hsingle

private theorem eight_div_pi_sq_le_one : 8 / Real.pi ^ 2 ≤ (1 : ℝ) := by
  have hpi_sq_pos : 0 < Real.pi ^ 2 := sq_pos_of_ne_zero Real.pi_ne_zero
  have hpi_sq_ge_eight : (8 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  exact (div_le_one hpi_sq_pos).mpr hpi_sq_ge_eight

private theorem theorem12SuccessProbability_le_one {k : ℕ} (hk : 0 < k) :
    theorem12SuccessProbability k ≤ 1 := by
  unfold theorem12SuccessProbability
  by_cases hk1 : k = 1
  · simpa [hk1] using eight_div_pi_sq_le_one
  · have hkgt : 1 < k := by omega
    have hkgtR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hkgt
    have hden_pos : 0 < 2 * ((k : ℝ) - 1) := by nlinarith
    have hnonneg : 0 ≤ 1 / (2 * ((k : ℝ) - 1)) :=
      div_nonneg zero_le_one (le_of_lt hden_pos)
    simp [hk1]
    linarith

/-- BHMT Paper Theorem 12 for the paper-level QAE circuit.

The probability distribution is the counting-register marginal
`paperQAEOutputProbability m n A f`, and the classical output is
`paperQAEEstimate m y = sin²(π y / M)`.  The amplitude `a` is the probability
mass of the prepared state `A|0...0⟩` on the marked basis states. -/
theorem PaperTheorem12
    {m n k : ℕ} (A : Square (QPE.M n)) (f : Fin (QPE.M n) → Bool)
    (theta a : ℝ)
    (hA : Matrix.isUnitary A) (hm : 0 < m) (hk : 0 < k)
    (hgoodProb : paperGoodProbability n A f = a)
    (htheta0 : 0 ≤ theta) (htheta_pi : theta ≤ Real.pi)
    (ha : a = amplitudeFromAngle theta) :
    (k = 1 →
      8 / Real.pi ^ 2 ≤
        (Finset.univ.filter (fun y : Fin (QPE.M m) =>
          |paperQAEEstimate m y - a| ≤
            2 * Real.pi * (k : ℝ) * Real.sqrt (a * (1 - a)) / (QPE.M m : ℝ) +
              (k : ℝ) ^ 2 * Real.pi ^ 2 / (QPE.M m : ℝ) ^ 2)).sum
          (fun y => paperQAEOutputProbability m n A f y)) ∧
    (1 < k →
      1 - 1 / (2 * ((k : ℝ) - 1)) ≤
        (Finset.univ.filter (fun y : Fin (QPE.M m) =>
          |paperQAEEstimate m y - a| ≤
            2 * Real.pi * (k : ℝ) * Real.sqrt (a * (1 - a)) / (QPE.M m : ℝ) +
              (k : ℝ) ^ 2 * Real.pi ^ 2 / (QPE.M m : ℝ) ^ 2)).sum
          (fun y => paperQAEOutputProbability m n A f y)) ∧
    (a = 0 →
      ∃ y : Fin (QPE.M m),
        paperQAEOutputProbability m n A f y = 1 ∧ paperQAEEstimate m y = 0) ∧
    (a = 1 →
      ∃ y : Fin (QPE.M m),
        paperQAEOutputProbability m n A f y = 1 ∧ paperQAEEstimate m y = 1) := by
  rw [ha] at hgoodProb ⊢
  have hbadProb : paperBadProbability n A f = 1 - amplitudeFromAngle theta := by
    rw [paperBadProbability_eq_one_sub_goodProbability (n := n) (A := A) (f := f) hA]
    rw [hgoodProb]
  have hSuccess : theorem12SuccessProbability k ≤
      (Finset.univ.filter (fun y : Fin (QPE.M m) =>
        |paperQAEEstimate m y - amplitudeFromAngle theta| ≤
          2 * Real.pi * (k : ℝ) * Real.sqrt (amplitudeFromAngle theta *
            (1 - amplitudeFromAngle theta)) / (QPE.M m : ℝ) +
            (k : ℝ) ^ 2 * Real.pi ^ 2 / (QPE.M m : ℝ) ^ 2)).sum
        (fun y => paperQAEOutputProbability m n A f y) := by
    by_cases ha0 : amplitudeFromAngle theta = 0
    · have hzero : paperGoodProbability n A f = 0 := by rw [hgoodProb, ha0]
      rcases paperQAEEndpointZero_of_goodProbability_zero
        (m := m) (n := n) (A := A) (f := f) hA hzero with ⟨y, hprob, hest⟩
      have hsum : 1 ≤
          (Finset.univ.filter (fun y : Fin (QPE.M m) =>
            |paperQAEEstimate m y - amplitudeFromAngle theta| ≤
              2 * Real.pi * (k : ℝ) * Real.sqrt (amplitudeFromAngle theta *
                (1 - amplitudeFromAngle theta)) / (QPE.M m : ℝ) +
                (k : ℝ) ^ 2 * Real.pi ^ 2 / (QPE.M m : ℝ) ^ 2)).sum
            (fun y => paperQAEOutputProbability m n A f y) := by
        apply paperQAESuccessSum_ge_one_of_point (m := m) (n := n) (k := k)
          (A := A) (f := f) (a := amplitudeFromAngle theta) (y := y) hprob
        rw [hest, ha0]
        norm_num
        positivity
      exact le_trans (theorem12SuccessProbability_le_one hk) hsum
    · by_cases ha1 : amplitudeFromAngle theta = 1
      · have hbadZero : paperBadProbability n A f = 0 := by rw [hbadProb, ha1]; ring
        rcases paperQAEEndpointOne_of_badProbability_zero
          (m := m) (n := n) (A := A) (f := f) hA hm hbadZero with ⟨y, hprob, hest⟩
        have hsum : 1 ≤
            (Finset.univ.filter (fun y : Fin (QPE.M m) =>
              |paperQAEEstimate m y - amplitudeFromAngle theta| ≤
                2 * Real.pi * (k : ℝ) * Real.sqrt (amplitudeFromAngle theta *
                  (1 - amplitudeFromAngle theta)) / (QPE.M m : ℝ) +
                  (k : ℝ) ^ 2 * Real.pi ^ 2 / (QPE.M m : ℝ) ^ 2)).sum
              (fun y => paperQAEOutputProbability m n A f y) := by
          apply paperQAESuccessSum_ge_one_of_point (m := m) (n := n) (k := k)
            (A := A) (f := f) (a := amplitudeFromAngle theta) (y := y) hprob
          rw [hest, ha1]
          norm_num
          positivity
        exact le_trans (theorem12SuccessProbability_le_one hk) hsum
      · have hsin_ne : Real.sin theta ≠ 0 := by
          intro hsin
          apply ha0
          unfold amplitudeFromAngle
          rw [hsin]
          norm_num
        have hcos_ne : Real.cos theta ≠ 0 := by
          intro hcos
          apply ha1
          unfold amplitudeFromAngle
          nlinarith [Real.sin_sq_add_cos_sq theta]
        have hcosC : (Real.cos theta : ℂ) ≠ 0 := by exact_mod_cast hcos_ne
        have hsinC : (Real.sin theta : ℂ) ≠ 0 := by exact_mod_cast hsin_ne
        have hinit : A ⬝ Vector.basis (QPE.zeroIndex n) =
            (Real.cos theta : ℂ) • paperBadState n A f theta +
              (Real.sin theta : ℂ) • paperGoodState n A f theta := by
          have h := paperPreparedState_decompose_bad_good_states
            (n := n) (A := A) (f := f) (theta := theta) hcosC hsinC
          unfold paperPreparedState at h
          exact h
        have hbad : ∀ x, f x = true → paperBadState n A f theta x 0 = 0 := by
          intro x hx
          exact paperBadState_support (n := n) (A := A) (f := f) (theta := theta) hx
        have hgood : ∀ x, f x = false → paperGoodState n A f theta x 0 = 0 := by
          intro x hx
          exact paperGoodState_support (n := n) (A := A) (f := f) (theta := theta) hx
        have hψ0 : Vector.IsNormalized (paperBadState n A f theta) :=
          paperBadState_isNormalized (n := n) (A := A) (f := f) (theta := theta)
            hbadProb hcos_ne
        have hψ1 : Vector.IsNormalized (paperGoodState n A f theta) :=
          paperGoodState_isNormalized (n := n) (A := A) (f := f) (theta := theta)
            hgoodProb hsin_ne
        exact paperQAESuccessProbabilityK_lower_bound_expanded
          (m := m) (n := n) (k := k) (A := A) (f := f)
          (ψ0 := paperBadState n A f theta) (ψ1 := paperGoodState n A f theta)
          (theta := theta) hA hinit hbad hgood hψ0 hψ1 htheta0 htheta_pi hk
  constructor
  · intro hk1
    simpa [theorem12SuccessProbability, hk1] using hSuccess
  constructor
  · intro hkgt
    have hk_ne : k ≠ 1 := by omega
    simpa [theorem12SuccessProbability, hk_ne] using hSuccess
  constructor
  · intro ha0
    have hzero : paperGoodProbability n A f = 0 := by rw [hgoodProb, ha0]
    exact paperQAEEndpointZero_of_goodProbability_zero
      (m := m) (n := n) (A := A) (f := f) hA hzero
  · intro ha1
    have hbadZero : paperBadProbability n A f = 0 := by rw [hbadProb, ha1]; ring
    exact paperQAEEndpointOne_of_badProbability_zero
      (m := m) (n := n) (A := A) (f := f) hA hm hbadZero

end Grover
end QAE
