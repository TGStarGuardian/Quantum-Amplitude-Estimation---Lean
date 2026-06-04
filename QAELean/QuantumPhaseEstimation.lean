import QAELean.QuantumLibraryBridge
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Field.GeomSum
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.Order.Round

/-!
# Quantum phase estimation

This module starts a QPE formalization on top of `duckki/quantum-computing-lean`.
It focuses on the semantic core needed by QAE: an eigenstate of a unitary with
phase `φ = y/M` is transformed by controlled powers into a Fourier-basis state,
and an inverse QFT maps that state to the computational-basis state `|y⟩`.

The library currently supplies matrices, vectors, tensor products, unitarity, and
computational-basis measurement.  It does not yet supply a reusable circuit DSL
or QFT library, so this file introduces QPE-specific matrix-level operators and
correctness contracts.
-/

noncomputable section

namespace QAE
namespace QPE

open QuantumComputing
open scoped BigOperators

/-- Squared norm of `exp(2πix) - 1`, written in the sine form used by the
standard phase-estimation probability bound. -/
theorem phase_sub_one_normSq (x : ℝ) :
    Complex.normSq ((Real.fourierChar x : ℂ) - 1) = 4 * Real.sin (Real.pi * x) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  have h := Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * x)
  norm_num at h
  rw [Real.fourierChar_apply]
  have harg : ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I =
      Complex.I * (2 * Real.pi * x : ℂ) := by
    rw [mul_comm]
    norm_num
  rw [harg]
  rw [h]
  have hs : Real.sin (2 * Real.pi * x / 2) = Real.sin (Real.pi * x) := by
    ring_nf
  rw [hs]
  rw [mul_pow, sq_abs]
  ring_nf

/-- Dimension of the `m`-qubit counting register. -/
def M (m : ℕ) : ℕ := 2 ^ m

/-- The QPE counting-register dimension is never zero. -/
instance m_neZero (m : ℕ) : NeZero (M m) :=
  ⟨(Nat.two_pow_pos m).ne'⟩

/-- The first computational-basis index of the counting register. -/
def zeroIndex (m : ℕ) : Fin (M m) :=
  ⟨0, by unfold M; exact Nat.two_pow_pos m⟩

/-- The uniform state prepared on the counting register before controlled powers. -/
def uniformState (m : ℕ) : Vector (M m) :=
  fun _ _ => ((M m : ℝ)⁻¹.sqrt : ℂ)

/-- The Fourier basis state with phase `y/M`. -/
def fourierState (m : ℕ) (y : Fin (M m)) : Vector (M m) :=
  fun k _ => ((M m : ℝ)⁻¹.sqrt : ℂ) * (Real.fourierChar (((k : ℕ) * (y : ℕ) : ℝ) / (M m : ℝ)) : ℂ)

/-- The counting-register state after phase kickback for an arbitrary real phase.
For exact phases `theta = y / M`, this specializes to `fourierState m y`. -/
def phaseState (m : ℕ) (theta : ℝ) : Vector (M m) :=
  fun k _ => (((M m : ℝ).sqrt : ℂ)⁻¹) * (Real.fourierChar ((k : ℕ) * theta) : ℂ)

/-- The forward QFT matrix on the `m`-qubit counting register.

The convention is `|y⟩ ↦ 1 / sqrt(M) * Σ_k exp(2π i k y / M) |k⟩`, matching
`fourierState`. -/
def qftMatrix (m : ℕ) : Square (M m) :=
  fun row col => ((M m : ℝ)⁻¹.sqrt : ℂ) *
    (Real.fourierChar (((row : ℕ) * (col : ℕ) : ℝ) / (M m : ℝ)) : ℂ)

/-- The inverse QFT matrix, written as the conjugate Fourier matrix. -/
def inverseQFTMatrix (m : ℕ) : Square (M m) :=
  fun row col => ((M m : ℝ)⁻¹.sqrt : ℂ) *
    (Real.fourierChar (-(((row : ℕ) * (col : ℕ) : ℝ) / (M m : ℝ))) : ℂ)

/-- The amplitude assigned by approximate QPE to counting-register outcome `y`
for arbitrary phase `theta`.  Equivalently, this is the `y`th coefficient of
`inverseQFTMatrix m ⬝ phaseState m theta`. -/
def qpeApproxAmplitude (m : ℕ) (theta : ℝ) (y : Fin (M m)) : ℂ :=
  (inverseQFTMatrix m ⬝ phaseState m theta) y 0

/-- The counting-register probability mass assigned by approximate QPE to `y`
for arbitrary phase `theta`. -/
def qpeApproxOutcomeProbability (m : ℕ) (theta : ℝ) (y : Fin (M m)) : ℝ :=
  Complex.normSq (qpeApproxAmplitude m theta y)

/-- The non-wrapped phase-estimation success predicate `|theta - y/M| ≤ k/M`.

BHMT Theorem 11 states the corresponding circular-distance version.  The QAE
correctness layer uses this predicate for phases already represented in the
standard interval, namely `theta / π` and `1 - theta / π`. -/
def qpePhaseWindow (m k : ℕ) (theta : ℝ) (y : Fin (M m)) : Prop :=
  |theta - (((y : ℕ) : ℝ) / (M m : ℝ))| ≤ (k : ℝ) / (M m : ℝ)

/-- Outcomes in the QPE success window of radius `k/M`. -/
def qpePhaseWindowOutcomes (m k : ℕ) (theta : ℝ) : Finset (Fin (M m)) := by
  classical
  exact Finset.univ.filter (qpePhaseWindow m k theta)

/-- Probability mass assigned by approximate QPE to the success window. -/
def qpePhaseWindowProbability (m k : ℕ) (theta : ℝ) : ℝ :=
  (qpePhaseWindowOutcomes m k theta).sum (fun y => qpeApproxOutcomeProbability m theta y)

/-- Membership in the concrete QPE phase window unfolds to the grid-distance bound. -/
theorem mem_qpePhaseWindowOutcomes_iff (m k : ℕ) (theta : ℝ) (y : Fin (M m)) :
    y ∈ qpePhaseWindowOutcomes m k theta ↔ qpePhaseWindow m k theta y := by
  classical
  unfold qpePhaseWindowOutcomes
  simp

/-- Approximate-QPE outcome probabilities are nonnegative. -/
theorem qpeApproxOutcomeProbability_nonneg (m : ℕ) (theta : ℝ) (y : Fin (M m)) :
    0 ≤ qpeApproxOutcomeProbability m theta y := by
  unfold qpeApproxOutcomeProbability
  exact Complex.normSq_nonneg _

/-- Circular distance on the unit phase interval, specialized to the three shifts
needed when both representatives lie in `[0, 1]`. -/
def unitPhaseDistance (theta grid : ℝ) : ℝ :=
  min |theta - grid| (min |theta - grid - 1| |theta - grid + 1|)

theorem unitPhaseDistance_nonneg (theta grid : ℝ) :
    0 ≤ unitPhaseDistance theta grid := by
  unfold unitPhaseDistance
  exact le_min (abs_nonneg _) (le_min (abs_nonneg _) (abs_nonneg _))

theorem unitPhaseDistance_le_abs_sub (theta grid : ℝ) :
    unitPhaseDistance theta grid ≤ |theta - grid| := by
  unfold unitPhaseDistance
  exact min_le_left _ _

theorem unitPhaseDistance_le_sub_one (theta grid : ℝ) :
    unitPhaseDistance theta grid ≤ |theta - grid - 1| := by
  unfold unitPhaseDistance
  exact le_trans (min_le_right _ _) (min_le_left _ _)

theorem unitPhaseDistance_le_add_one (theta grid : ℝ) :
    unitPhaseDistance theta grid ≤ |theta - grid + 1| := by
  unfold unitPhaseDistance
  exact le_trans (min_le_right _ _) (min_le_right _ _)

theorem unitPhaseDistance_cases {theta grid eps : ℝ}
    (h : unitPhaseDistance theta grid ≤ eps) :
    |theta - grid| ≤ eps ∨ |theta - grid - 1| ≤ eps ∨ |theta - grid + 1| ≤ eps := by
  unfold unitPhaseDistance at h
  rw [min_le_iff] at h
  rcases h with h | h
  · exact Or.inl h
  · rw [min_le_iff] at h
    rcases h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-- Circular phase-estimation success predicate with radius `k/M`. -/
def qpeCircularPhaseWindow (m k : ℕ) (theta : ℝ) (y : Fin (M m)) : Prop :=
  unitPhaseDistance theta (((y : ℕ) : ℝ) / (M m : ℝ)) ≤ (k : ℝ) / (M m : ℝ)

/-- Outcomes in the circular QPE success window. -/
def qpeCircularPhaseWindowOutcomes (m k : ℕ) (theta : ℝ) : Finset (Fin (M m)) := by
  classical
  exact Finset.univ.filter (qpeCircularPhaseWindow m k theta)

/-- Probability mass assigned by approximate QPE to the circular success window. -/
def qpeCircularPhaseWindowProbability (m k : ℕ) (theta : ℝ) : ℝ :=
  (qpeCircularPhaseWindowOutcomes m k theta).sum (fun y => qpeApproxOutcomeProbability m theta y)

/-- Outcomes outside the circular QPE success window. -/
def qpeCircularPhaseWindowFailureOutcomes (m k : ℕ) (theta : ℝ) : Finset (Fin (M m)) := by
  classical
  exact Finset.univ.filter (fun y => ¬ qpeCircularPhaseWindow m k theta y)

/-- Probability mass assigned by approximate QPE to the complement of the circular success window. -/
def qpeCircularPhaseWindowFailureProbability (m k : ℕ) (theta : ℝ) : ℝ :=
  (qpeCircularPhaseWindowFailureOutcomes m k theta).sum
    (fun y => qpeApproxOutcomeProbability m theta y)

theorem mem_qpeCircularPhaseWindowOutcomes_iff
    (m k : ℕ) (theta : ℝ) (y : Fin (M m)) :
    y ∈ qpeCircularPhaseWindowOutcomes m k theta ↔
      qpeCircularPhaseWindow m k theta y := by
  classical
  unfold qpeCircularPhaseWindowOutcomes
  simp

theorem mem_qpeCircularPhaseWindowFailureOutcomes_iff
    (m k : ℕ) (theta : ℝ) (y : Fin (M m)) :
    y ∈ qpeCircularPhaseWindowFailureOutcomes m k theta ↔
      ¬ qpeCircularPhaseWindow m k theta y := by
  classical
  unfold qpeCircularPhaseWindowFailureOutcomes
  simp

theorem qpePhaseWindow_subset_circular (m k : ℕ) (theta : ℝ) :
    qpePhaseWindowOutcomes m k theta ⊆ qpeCircularPhaseWindowOutcomes m k theta := by
  intro y hy
  have hlin := (mem_qpePhaseWindowOutcomes_iff m k theta y).mp hy
  exact (mem_qpeCircularPhaseWindowOutcomes_iff m k theta y).mpr
    (le_trans (unitPhaseDistance_le_abs_sub theta (((y : ℕ) : ℝ) / (M m : ℝ))) hlin)

theorem qpePhaseWindowProbability_le_circular
    (m k : ℕ) (theta : ℝ) :
    qpePhaseWindowProbability m k theta ≤ qpeCircularPhaseWindowProbability m k theta := by
  unfold qpePhaseWindowProbability qpeCircularPhaseWindowProbability
  exact Finset.sum_le_sum_of_subset_of_nonneg (qpePhaseWindow_subset_circular m k theta)
    (by intro y _hyBig _hyNot; exact qpeApproxOutcomeProbability_nonneg m theta y)

theorem exists_qpeCircularPhaseWindow_one_of_mem_unitInterval
    (m : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    ∃ y : Fin (M m), qpeCircularPhaseWindow m 1 theta y := by
  by_cases htheta1 : theta = 1
  · subst theta
    refine ⟨zeroIndex m, ?_⟩
    unfold qpeCircularPhaseWindow unitPhaseDistance
    simp [zeroIndex]
  · have htheta_lt_one : theta < 1 := lt_of_le_of_ne h1 htheta1
    let n : ℕ := Nat.floor ((M m : ℝ) * theta)
    have hMposN : 0 < M m := Nat.two_pow_pos m
    have hMpos : 0 < (M m : ℝ) := by exact_mod_cast hMposN
    have hx_nonneg : 0 ≤ (M m : ℝ) * theta := mul_nonneg (le_of_lt hMpos) h0
    have hx_lt_M : (M m : ℝ) * theta < (M m : ℝ) := by
      nlinarith [hMpos, htheta_lt_one]
    have hn_lt_M : n < M m := by
      dsimp [n]
      exact (Nat.floor_lt hx_nonneg).mpr hx_lt_M
    refine ⟨⟨n, hn_lt_M⟩, ?_⟩
    unfold qpeCircularPhaseWindow
    have hn_le : (n : ℝ) ≤ (M m : ℝ) * theta := by
      dsimp [n]
      exact Nat.floor_le hx_nonneg
    have htheta_lt : (M m : ℝ) * theta < (n : ℝ) + 1 := by
      dsimp [n]
      exact Nat.lt_floor_add_one ((M m : ℝ) * theta)
    have hgrid_le : (n : ℝ) / (M m : ℝ) ≤ theta := by
      rw [div_le_iff₀ hMpos]
      simpa [mul_comm] using hn_le
    have htheta_lt_div : theta < ((n : ℝ) + 1) / (M m : ℝ) := by
      rw [lt_div_iff₀ hMpos]
      simpa [mul_comm] using htheta_lt
    have hsplit : ((n : ℝ) + 1) / (M m : ℝ) = (n : ℝ) / (M m : ℝ) + 1 / (M m : ℝ) := by
      field_simp [hMpos.ne']
    have htheta_sub_lt : theta - (n : ℝ) / (M m : ℝ) < 1 / (M m : ℝ) := by
      rw [hsplit] at htheta_lt_div
      linarith
    have habs_le : |theta - (n : ℝ) / (M m : ℝ)| ≤ 1 / (M m : ℝ) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hgrid_le)]
      exact le_of_lt htheta_sub_lt
    simpa using le_trans (unitPhaseDistance_le_abs_sub theta ((n : ℝ) / (M m : ℝ))) habs_le

theorem exists_mem_qpeCircularPhaseWindowOutcomes_one_of_mem_unitInterval
    (m : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    ∃ y : Fin (M m), y ∈ qpeCircularPhaseWindowOutcomes m 1 theta := by
  rcases exists_qpeCircularPhaseWindow_one_of_mem_unitInterval m h0 h1 with ⟨y, hy⟩
  exact ⟨y, (mem_qpeCircularPhaseWindowOutcomes_iff m 1 theta y).mpr hy⟩

/-- Lower adjacent grid index, namely `⌊M * theta⌋`.

For `theta ∈ [0, 1)`, this is the lower of the two adjacent grid points used in
the BHMT `k = 1` two-nearest-outcome argument. -/
def floorGridIndexNat (m : ℕ) (theta : ℝ) : ℕ :=
  Nat.floor ((M m : ℝ) * theta)

/-- Lower adjacent QPE outcome.  The coercion to `Fin (M m)` is harmlessly
wrapped, and is definitionally the floor index when `theta ∈ [0, 1)`. -/
def qpeLowerAdjacentOutcome (m : ℕ) (theta : ℝ) : Fin (M m) :=
  ⟨floorGridIndexNat m theta % M m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩

/-- Upper adjacent QPE outcome, wrapped around the cyclic grid. -/
def qpeUpperAdjacentOutcome (m : ℕ) (theta : ℝ) : Fin (M m) :=
  ⟨(floorGridIndexNat m theta + 1) % M m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩

/-- Fractional offset of `M * theta` from its lower adjacent integer. -/
def qpeFractionalOffset (m : ℕ) (theta : ℝ) : ℝ :=
  Int.fract ((M m : ℝ) * theta)

theorem floorGridIndexNat_lt_M_of_mem_Ico
    (m : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1) :
    floorGridIndexNat m theta < M m := by
  unfold floorGridIndexNat
  have hMpos : 0 < (M m : ℝ) := by exact_mod_cast (Nat.two_pow_pos m)
  have hx_nonneg : 0 ≤ (M m : ℝ) * theta := mul_nonneg hMpos.le h0
  have hx_lt : (M m : ℝ) * theta < (M m : ℝ) := by
    nlinarith [hMpos, h1]
  exact (Nat.floor_lt hx_nonneg).mpr hx_lt


/-- If the fractional offset vanishes, the phase is exactly the lower grid point. -/
theorem theta_eq_floorGrid_div_of_qpeFractionalOffset_eq_zero
    (m : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (hx : qpeFractionalOffset m theta = 0) :
    theta = (floorGridIndexNat m theta : ℝ) / (M m : ℝ) := by
  have hMpos : 0 < (M m : ℝ) := by exact_mod_cast (Nat.two_pow_pos m)
  rw [show qpeFractionalOffset m theta =
          (M m : ℝ) * theta - (floorGridIndexNat m theta : ℝ) by
        have hMnonneg : 0 ≤ (M m : ℝ) := by exact_mod_cast (Nat.zero_le (M m))
        have hx_nonneg : 0 ≤ (M m : ℝ) * theta := mul_nonneg hMnonneg h0
        unfold qpeFractionalOffset floorGridIndexNat
        rw [Int.fract]
        rw [← natCast_floor_eq_intCast_floor hx_nonneg]] at hx
  have hmul : (M m : ℝ) * theta = (floorGridIndexNat m theta : ℝ) := by
    linarith
  field_simp [hMpos.ne']
  linarith

/-- The lower adjacent outcome is always inside the circular `k = 1` window
for phases represented in `[0, 1)`. -/
theorem qpeLowerAdjacentOutcome_mem_circularWindow_one_of_mem_Ico
    (m : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1) :
    qpeLowerAdjacentOutcome m theta ∈ qpeCircularPhaseWindowOutcomes m 1 theta := by
  let y := qpeLowerAdjacentOutcome m theta
  have hMpos : 0 < (M m : ℝ) := by exact_mod_cast (Nat.two_pow_pos m)
  have hyval : (y : ℕ) = floorGridIndexNat m theta := by
    dsimp [y]
    exact Nat.mod_eq_of_lt (floorGridIndexNat_lt_M_of_mem_Ico m h0 h1)
  have hx_nonneg : 0 ≤ qpeFractionalOffset m theta := Int.fract_nonneg ((M m : ℝ) * theta)
  have hx_lt : qpeFractionalOffset m theta < 1 := Int.fract_lt_one ((M m : ℝ) * theta)
  have hdist : |theta - (((y : ℕ) : ℝ) / (M m : ℝ))| ≤ 1 / (M m : ℝ) := by
    have hrewrite :
        theta - (((y : ℕ) : ℝ) / (M m : ℝ)) =
          qpeFractionalOffset m theta / (M m : ℝ) := by
      rw [hyval]
      rw [show qpeFractionalOffset m theta =
          (M m : ℝ) * theta - (floorGridIndexNat m theta : ℝ) by
        have hMnonneg : 0 ≤ (M m : ℝ) := by exact_mod_cast (Nat.zero_le (M m))
        have hx_nonneg : 0 ≤ (M m : ℝ) * theta := mul_nonneg hMnonneg h0
        unfold qpeFractionalOffset floorGridIndexNat
        rw [Int.fract]
        rw [← natCast_floor_eq_intCast_floor hx_nonneg]]
      field_simp [hMpos.ne']
    rw [hrewrite, abs_div, abs_of_pos hMpos]
    rw [abs_of_nonneg hx_nonneg]
    exact div_le_div_of_nonneg_right hx_lt.le hMpos.le
  apply (mem_qpeCircularPhaseWindowOutcomes_iff m 1 theta y).mpr
  unfold qpeCircularPhaseWindow
  have hdist' : |theta - (((y : ℕ) : ℝ) / (M m : ℝ))| ≤ (1 : ℕ) / (M m : ℝ) := by
    simpa using hdist
  exact le_trans (unitPhaseDistance_le_abs_sub theta (((y : ℕ) : ℝ) / (M m : ℝ))) hdist'

/-- The upper adjacent outcome, with cyclic wraparound, is always inside the
circular `k = 1` window for phases represented in `[0, 1)`. -/
theorem qpeUpperAdjacentOutcome_mem_circularWindow_one_of_mem_Ico
    (m : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1) :
    qpeUpperAdjacentOutcome m theta ∈ qpeCircularPhaseWindowOutcomes m 1 theta := by
  let y := qpeUpperAdjacentOutcome m theta
  let n := floorGridIndexNat m theta
  have hMposNat : 0 < M m := Nat.two_pow_pos m
  have hMpos : 0 < (M m : ℝ) := by exact_mod_cast hMposNat
  have hn_lt : n < M m := by
    dsimp [n]
    exact floorGridIndexNat_lt_M_of_mem_Ico m h0 h1
  have hx_nonneg : 0 ≤ qpeFractionalOffset m theta := Int.fract_nonneg ((M m : ℝ) * theta)
  have hx_lt : qpeFractionalOffset m theta < 1 := Int.fract_lt_one ((M m : ℝ) * theta)
  apply (mem_qpeCircularPhaseWindowOutcomes_iff m 1 theta y).mpr
  unfold qpeCircularPhaseWindow
  by_cases hsucc_lt : n + 1 < M m
  · have hyval : (y : ℕ) = n + 1 := by
      dsimp [y, qpeUpperAdjacentOutcome, n]
      exact Nat.mod_eq_of_lt hsucc_lt
    have hdist : |theta - (((y : ℕ) : ℝ) / (M m : ℝ))| ≤ 1 / (M m : ℝ) := by
      have hrewrite :
          theta - (((y : ℕ) : ℝ) / (M m : ℝ)) =
            (qpeFractionalOffset m theta - 1) / (M m : ℝ) := by
        rw [hyval]
        dsimp [n]
        rw [show qpeFractionalOffset m theta =
          (M m : ℝ) * theta - (floorGridIndexNat m theta : ℝ) by
        have hMnonneg : 0 ≤ (M m : ℝ) := by exact_mod_cast (Nat.zero_le (M m))
        have hx_nonneg : 0 ≤ (M m : ℝ) * theta := mul_nonneg hMnonneg h0
        unfold qpeFractionalOffset floorGridIndexNat
        rw [Int.fract]
        rw [← natCast_floor_eq_intCast_floor hx_nonneg]]
        field_simp [hMpos.ne']
        norm_num [Nat.cast_add]
        ring_nf
      rw [hrewrite, abs_div, abs_of_pos hMpos]
      have hnonpos : qpeFractionalOffset m theta - 1 ≤ 0 := by linarith
      rw [abs_of_nonpos hnonpos]
      have hle : 1 - qpeFractionalOffset m theta ≤ 1 := by linarith
      simpa [neg_sub] using div_le_div_of_nonneg_right hle hMpos.le
    have hdist' : |theta - (((y : ℕ) : ℝ) / (M m : ℝ))| ≤ (1 : ℕ) / (M m : ℝ) := by
      simpa using hdist
    exact le_trans (unitPhaseDistance_le_abs_sub theta (((y : ℕ) : ℝ) / (M m : ℝ))) hdist'
  · have hsucc_eq : n + 1 = M m := by omega
    have hyval : (y : ℕ) = 0 := by
      dsimp [y, qpeUpperAdjacentOutcome, n]
      rw [hsucc_eq, Nat.mod_self]
    have hdist : |theta - (((y : ℕ) : ℝ) / (M m : ℝ)) - 1| ≤ 1 / (M m : ℝ) := by
      have hnreal : ((n : ℕ) : ℝ) + 1 = (M m : ℝ) := by
        exact_mod_cast hsucc_eq
      have hrewrite :
          theta - (((y : ℕ) : ℝ) / (M m : ℝ)) - 1 =
            (qpeFractionalOffset m theta - 1) / (M m : ℝ) := by
        rw [hyval]
        norm_num
        dsimp [n] at hnreal
        rw [show qpeFractionalOffset m theta =
          (M m : ℝ) * theta - (floorGridIndexNat m theta : ℝ) by
        have hMnonneg : 0 ≤ (M m : ℝ) := by exact_mod_cast (Nat.zero_le (M m))
        have hx_nonneg : 0 ≤ (M m : ℝ) * theta := mul_nonneg hMnonneg h0
        unfold qpeFractionalOffset floorGridIndexNat
        rw [Int.fract]
        rw [← natCast_floor_eq_intCast_floor hx_nonneg]]
        field_simp [hMpos.ne']
        nlinarith
      rw [hrewrite, abs_div, abs_of_pos hMpos]
      have hnonpos : qpeFractionalOffset m theta - 1 ≤ 0 := by linarith
      rw [abs_of_nonpos hnonpos]
      have hle : 1 - qpeFractionalOffset m theta ≤ 1 := by linarith
      simpa [neg_sub] using div_le_div_of_nonneg_right hle hMpos.le
    have hdist' : |theta - (((y : ℕ) : ℝ) / (M m : ℝ)) - 1| ≤ (1 : ℕ) / (M m : ℝ) := by
      simpa using hdist
    exact le_trans (unitPhaseDistance_le_sub_one theta (((y : ℕ) : ℝ) / (M m : ℝ))) hdist'

/-- On a nontrivial counting grid, the lower and upper adjacent outcomes are
distinct.  The `m = 0` grid has only one point, so it is handled separately. -/
theorem qpeAdjacentOutcomes_ne_of_pos_m
    (m : ℕ) {theta : ℝ} (hm : 0 < m) (h0 : 0 ≤ theta) (h1 : theta < 1) :
    qpeLowerAdjacentOutcome m theta ≠ qpeUpperAdjacentOutcome m theta := by
  let n := floorGridIndexNat m theta
  have hn_lt : n < M m := by
    dsimp [n]
    exact floorGridIndexNat_lt_M_of_mem_Ico m h0 h1
  have hMgt1 : 1 < M m := by
    unfold M
    exact one_lt_pow₀ Nat.one_lt_two hm.ne'
  intro heq
  have hval : (qpeLowerAdjacentOutcome m theta : ℕ) =
      (qpeUpperAdjacentOutcome m theta : ℕ) := congrArg (fun z : Fin (M m) => (z : ℕ)) heq
  have hlow : (qpeLowerAdjacentOutcome m theta : ℕ) = n := by
    dsimp [n]
    exact Nat.mod_eq_of_lt (floorGridIndexNat_lt_M_of_mem_Ico m h0 h1)
  have hup : (qpeUpperAdjacentOutcome m theta : ℕ) = (n + 1) % M m := by
    dsimp [n]
    rfl
  rw [hlow, hup] at hval
  by_cases hsucc_lt : n + 1 < M m
  · rw [Nat.mod_eq_of_lt hsucc_lt] at hval
    omega
  · have hsucc_eq : n + 1 = M m := by omega
    rw [hsucc_eq, Nat.mod_self] at hval
    omega

private theorem abs_grid_error_le_half_div_M
    (m : ℕ) {theta : ℝ} (h0 : 0 ≤ theta)
    {n : ℕ} (hn : n = (round ((M m : ℝ) * theta)).toNat) :
    |theta - (n : ℝ) / (M m : ℝ)| ≤ 1 / (2 * (M m : ℝ)) := by
  subst n
  have hMpos : 0 < (M m : ℝ) := by exact_mod_cast (Nat.two_pow_pos m)
  let x : ℝ := (M m : ℝ) * theta
  have hx_nonneg : 0 ≤ x := by
    have hMnonneg : 0 ≤ (M m : ℝ) := by exact_mod_cast (Nat.zero_le (M m))
    exact mul_nonneg hMnonneg h0
  have hround_nonneg : 0 ≤ round x := by
    rw [round_eq]
    exact Int.floor_nonneg.mpr (by nlinarith)
  have hround_cast : (((round x).toNat : ℕ) : ℝ) = (round x : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hround_nonneg
  have herr : |(M m : ℝ) * theta - (((round x).toNat : ℕ) : ℝ)| ≤ (1 / 2 : ℝ) := by
    simpa [x, hround_cast] using abs_sub_round x
  have hscaled := div_le_div_of_nonneg_right herr (le_of_lt hMpos)
  have hrewrite : |theta - ((((round x).toNat : ℕ) : ℝ)) / (M m : ℝ)| =
      |((M m : ℝ) * theta - (((round x).toNat : ℕ) : ℝ))| / (M m : ℝ) := by
    calc
      |theta - ((((round x).toNat : ℕ) : ℝ)) / (M m : ℝ)|
          = |(((M m : ℝ) * theta - (((round x).toNat : ℕ) : ℝ)) / (M m : ℝ))| := by
            congr 1
            field_simp [hMpos.ne']
      _ = |((M m : ℝ) * theta - (((round x).toNat : ℕ) : ℝ))| / (M m : ℝ) := by
            rw [abs_div, abs_of_pos hMpos]
  have hhalf : (1 / 2 : ℝ) / (M m : ℝ) = 1 / (2 * (M m : ℝ)) := by ring_nf
  rw [hrewrite]
  simpa [hhalf, one_div, mul_comm, mul_left_comm, mul_assoc] using hscaled

private theorem half_div_M_le_one_div_M (m : ℕ) :
    (1 : ℝ) / (2 * (M m : ℝ)) ≤ 1 / (M m : ℝ) := by
  have hMpos : 0 < (M m : ℝ) := by exact_mod_cast (Nat.two_pow_pos m)
  field_simp [hMpos.ne']
  nlinarith [hMpos]

/-- Failure of the circular window means the circular phase distance is strictly
larger than the window radius. -/
theorem qpeCircularFailure_unitPhaseDistance_gt
    (m k : ℕ) (theta : ℝ) {y : Fin (M m)}
    (hy : y ∈ qpeCircularPhaseWindowFailureOutcomes m k theta) :
    (k : ℝ) / (M m : ℝ) <
      unitPhaseDistance theta (((y : ℕ) : ℝ) / (M m : ℝ)) := by
  have hnot := (mem_qpeCircularPhaseWindowFailureOutcomes_iff m k theta y).mp hy
  unfold qpeCircularPhaseWindow at hnot
  exact lt_of_not_ge hnot

/-- A failed circular-window outcome has a phase-error representative among the
three wrapped errors.  The representative lies in `[-1/2, 1/2]` and is farther
than the window radius. -/
theorem qpeCircularFailure_phase_error_representative
    (m k : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    {y : Fin (M m)}
    (hy : y ∈ qpeCircularPhaseWindowFailureOutcomes m k theta) :
    ∃ delta : ℝ,
      (delta = theta - (((y : ℕ) : ℝ) / (M m : ℝ)) ∨
        delta = theta - (((y : ℕ) : ℝ) / (M m : ℝ)) - 1 ∨
        delta = theta - (((y : ℕ) : ℝ) / (M m : ℝ)) + 1) ∧
      |delta| ≤ (1 : ℝ) / 2 ∧
      (k : ℝ) / (M m : ℝ) < |delta| := by
  let grid : ℝ := ((y : ℕ) : ℝ) / (M m : ℝ)
  have hMpos : 0 < (M m : ℝ) := by exact_mod_cast (Nat.two_pow_pos m)
  have hgrid0 : 0 ≤ grid := by dsimp [grid]; positivity
  have hgrid1 : grid ≤ 1 := by
    dsimp [grid]
    rw [div_le_one hMpos]
    exact_mod_cast (le_of_lt y.isLt)
  have hfail := qpeCircularFailure_unitPhaseDistance_gt m k theta (y := y) hy
  by_cases hclose : |theta - grid| ≤ (1 : ℝ) / 2
  · refine ⟨theta - grid, ?_, hclose, ?_⟩
    · left; rfl
    · exact lt_of_lt_of_le hfail (unitPhaseDistance_le_abs_sub theta grid)
  · have hfar : (1 : ℝ) / 2 < |theta - grid| := lt_of_not_ge hclose
    by_cases hge : grid ≤ theta
    · refine ⟨theta - grid - 1, ?_, ?_, ?_⟩
      · right; left; rfl
      · have hnonpos : theta - grid - 1 ≤ 0 := by linarith
        have hgt : (1 : ℝ) / 2 < theta - grid := by
          simpa [abs_of_nonneg (sub_nonneg.mpr hge)] using hfar
        rw [abs_of_nonpos hnonpos]
        linarith
      · exact lt_of_lt_of_le hfail (unitPhaseDistance_le_sub_one theta grid)
    · have hlt : theta < grid := lt_of_not_ge hge
      refine ⟨theta - grid + 1, ?_, ?_, ?_⟩
      · right; right; rfl
      · have hnonneg : 0 ≤ theta - grid + 1 := by linarith
        have hgt : (1 : ℝ) / 2 < grid - theta := by
          have hsub_nonpos : theta - grid ≤ 0 := by linarith
          have habs : |theta - grid| = grid - theta := by
            rw [abs_of_nonpos hsub_nonpos]
            ring_nf
          linarith
        rw [abs_of_nonneg hnonneg]
        linarith
      · exact lt_of_lt_of_le hfail (unitPhaseDistance_le_add_one theta grid)


private theorem fin_eq_left_or_right_candidate_of_abs_sub_mem_Ico
    {N : ℕ} (hN : 0 < N) {x : ℝ} {i : ℕ} {y : Fin N} {z : ℤ}
    (hmod : ((y : ℕ) : ℤ) ≡ z [ZMOD (N : ℤ)])
    (hlo : (i : ℝ) ≤ |x - (z : ℝ)|)
    (hhi : |x - (z : ℝ)| < (i : ℝ) + 1) :
    y = ⟨((Int.floor x - (i : ℤ) : ℤ) : ZMod N).val, by
      haveI : NeZero N := ⟨hN.ne'⟩
      exact ZMod.val_lt (((Int.floor x - (i : ℤ) : ℤ) : ZMod N))⟩ ∨
      y = ⟨((Int.ceil x + (i : ℤ) : ℤ) : ZMod N).val, by
        haveI : NeZero N := ⟨hN.ne'⟩
        exact ZMod.val_lt (((Int.ceil x + (i : ℤ) : ℤ) : ZMod N))⟩ := by
  have zmod_val_eq_of_modEq :
      ∀ {w : ℤ}, ((y : ℕ) : ℤ) ≡ w [ZMOD (N : ℤ)] →
        y = ⟨(w : ZMod N).val, by
          haveI : NeZero N := ⟨Nat.pos_iff_ne_zero.mp hN⟩
          exact ZMod.val_lt (w : ZMod N)⟩ := by
    intro w hw
    apply Fin.ext
    haveI : NeZero N := ⟨Nat.pos_iff_ne_zero.mp hN⟩
    have hzmod_int : (((y : ℕ) : ℤ) : ZMod N) = (w : ZMod N) :=
      (ZMod.intCast_eq_intCast_iff ((y : ℕ) : ℤ) w N).2 hw
    have hzmod_nat : ((y : ℕ) : ZMod N) = (w : ZMod N) := by
      exact_mod_cast hzmod_int
    have hval := congrArg ZMod.val hzmod_nat
    simpa [ZMod.val_cast_of_lt y.isLt] using hval
  by_cases hz_le : (z : ℝ) ≤ x
  · have habs : |x - (z : ℝ)| = x - (z : ℝ) := by
      rw [abs_of_nonneg]
      linarith
    have hfloor : Int.floor x = z + (i : ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor
      · exact_mod_cast (by linarith : (z : ℝ) + (i : ℝ) ≤ x)
      · exact_mod_cast (by linarith : x < (z : ℝ) + (i : ℝ) + 1)
    have hz : z = Int.floor x - (i : ℤ) := by omega
    left
    exact zmod_val_eq_of_modEq (by simpa [hz] using hmod)
  · have hx_le : x ≤ (z : ℝ) := le_of_lt (lt_of_not_ge hz_le)
    have habs : |x - (z : ℝ)| = (z : ℝ) - x := by
      rw [abs_of_nonpos (by linarith)]
      ring_nf
    have hceil : Int.ceil x = z - (i : ℤ) := by
      apply Int.ceil_eq_iff.mpr
      constructor
      · exact_mod_cast (by linarith : (z : ℝ) - (i : ℝ) - 1 < x)
      · exact_mod_cast (by linarith : x ≤ (z : ℝ) - (i : ℝ))
    have hz : z = Int.ceil x + (i : ℤ) := by omega
    right
    exact zmod_val_eq_of_modEq (by simpa [hz] using hmod)


/-- BHMT tail bucket for a QPE outcome: the integer part of the circular phase error measured in grid units.  For a failed outcome this bucket is at least `k`,
which matches the inverse-square tail in Theorem 11. -/
def qpeCircularDistanceBucket (m : ℕ) (theta : ℝ) (y : Fin (M m)) : ℕ :=
  Nat.floor ((M m : ℝ) * unitPhaseDistance theta (((y : ℕ) : ℝ) / (M m : ℝ)))



theorem qpeCircularDistanceBucket_mem_tail_of_failure
    (m k : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    {y : Fin (M m)} (hk : 0 < k)
    (hy : y ∈ qpeCircularPhaseWindowFailureOutcomes m k theta) :
    qpeCircularDistanceBucket m theta y ∈ Finset.Ioc (k - 1) (M m) := by
  have hMpos : 0 < (M m : ℝ) := by exact_mod_cast (Nat.two_pow_pos m)
  let D := unitPhaseDistance theta (((y : ℕ) : ℝ) / (M m : ℝ))
  have hfail := qpeCircularFailure_unitPhaseDistance_gt m k theta (y := y) hy
  have hk_lt_scaled : (k : ℝ) < (M m : ℝ) * D := by
    have hscaled : (k : ℝ) < D * (M m : ℝ) :=
      (div_lt_iff₀ hMpos).mp (by simpa [D] using hfail)
    simpa [mul_comm] using hscaled
  have hfloor_ge_k : k ≤ qpeCircularDistanceBucket m theta y := by
    by_contra hnot
    have hfloor_lt : qpeCircularDistanceBucket m theta y < k := Nat.lt_of_not_ge hnot
    have hx_nonneg : 0 ≤ (M m : ℝ) * D := by
      have hD_nonneg : 0 ≤ D := by dsimp [D]; exact unitPhaseDistance_nonneg _ _
      positivity
    have hx_lt_k : (M m : ℝ) * D < (k : ℝ) := by
      unfold qpeCircularDistanceBucket at hfloor_lt
      exact (Nat.floor_lt hx_nonneg).mp hfloor_lt
    exact (not_lt_of_ge hk_lt_scaled.le) hx_lt_k
  have hupper : qpeCircularDistanceBucket m theta y ≤ M m := by
    let grid : ℝ := ((y : ℕ) : ℝ) / (M m : ℝ)
    have hgrid0 : 0 ≤ grid := by
      dsimp [grid]
      positivity
    have hgrid1 : grid ≤ 1 := by
      dsimp [grid]
      rw [div_le_one hMpos]
      exact_mod_cast (le_of_lt y.isLt)
    have habs_le_one : |theta - grid| ≤ (1 : ℝ) := by
      rw [abs_le]
      constructor <;> linarith
    have hD_le_one : unitPhaseDistance theta grid ≤ (1 : ℝ) := by
      exact le_trans (unitPhaseDistance_le_abs_sub theta grid) habs_le_one
    have hD_nonneg : 0 ≤ unitPhaseDistance theta grid := unitPhaseDistance_nonneg theta grid
    have hx_nonneg : 0 ≤ (M m : ℝ) * unitPhaseDistance theta grid := by positivity
    have hfloor : (qpeCircularDistanceBucket m theta y : ℝ) ≤ (M m : ℝ) := by
      calc
        (qpeCircularDistanceBucket m theta y : ℝ)
            ≤ (M m : ℝ) * unitPhaseDistance theta grid := by
              unfold qpeCircularDistanceBucket
              dsimp [grid]
              exact Nat.floor_le hx_nonneg
        _ ≤ (M m : ℝ) * 1 := by gcongr
        _ = (M m : ℝ) := by ring_nf
    exact_mod_cast hfloor
  exact Finset.mem_Ioc.mpr ⟨by omega, hupper⟩

/-- The failure representative can be chosen together with the fact that the
actual circular distance is below the representative's absolute error. -/
theorem qpeCircularFailure_phase_error_representative_with_unitDistance
    (m k : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    {y : Fin (M m)}
    (hy : y ∈ qpeCircularPhaseWindowFailureOutcomes m k theta) :
    ∃ delta : ℝ,
      (delta = theta - (((y : ℕ) : ℝ) / (M m : ℝ)) ∨
        delta = theta - (((y : ℕ) : ℝ) / (M m : ℝ)) - 1 ∨
        delta = theta - (((y : ℕ) : ℝ) / (M m : ℝ)) + 1) ∧
      |delta| ≤ (1 : ℝ) / 2 ∧
      (k : ℝ) / (M m : ℝ) < |delta| ∧
      unitPhaseDistance theta (((y : ℕ) : ℝ) / (M m : ℝ)) ≤ |delta| := by
  rcases qpeCircularFailure_phase_error_representative m k h0 h1 hy with
    ⟨delta, hdelta, hhalf, hdist⟩
  have hD : unitPhaseDistance theta (((y : ℕ) : ℝ) / (M m : ℝ)) ≤ |delta| := by
    rcases hdelta with hdelta | hdelta | hdelta
    · rw [hdelta]
      exact unitPhaseDistance_le_abs_sub theta (((y : ℕ) : ℝ) / (M m : ℝ))
    · rw [hdelta]
      exact unitPhaseDistance_le_sub_one theta (((y : ℕ) : ℝ) / (M m : ℝ))
    · rw [hdelta]
      exact unitPhaseDistance_le_add_one theta (((y : ℕ) : ℝ) / (M m : ℝ))
  exact ⟨delta, hdelta, hhalf, hdist, hD⟩

/-- The probability lower bound stated by the BHMT phase-estimation window theorem. -/
def bhmt11SuccessProbability (k : ℕ) : ℝ :=
  if k = 1 then
    8 / Real.pi ^ 2
  else
    1 - 1 / (2 * ((k : ℝ) - 1))

/-- The theorem-shaped target for the BHMT Theorem 11 circular-window probability bound.

The current `unitPhaseDistance` is the three-shift circular distance appropriate for representatives
in `[0, 1]`, so the target includes that interval hypothesis explicitly. -/
def BHMT11CircularWindowBound : Prop :=
  ∀ (m k : ℕ) (theta : ℝ),
    0 ≤ theta -> theta ≤ 1 -> 0 < k ->
      bhmt11SuccessProbability k ≤ qpeCircularPhaseWindowProbability m k theta

/-- Finite inverse-square tail bound in the form used by the BHMT11 failure estimate.
The interval `Ioc (k - 1) n` is `{k, ..., n}`. -/
theorem half_inv_sq_tail_sum_le (k n : ℕ) (hk : 1 < k) :
    (∑ i ∈ Finset.Ioc (k - 1) n, (1 / (2 * (i : ℝ) ^ 2) : ℝ)) ≤
      1 / (2 * ((k : ℝ) - 1)) := by
  have hkpred_ne : k - 1 ≠ 0 := by omega
  have hsum_inv :
      (∑ i ∈ Finset.Ioc (k - 1) n, (((i : ℝ) ^ 2)⁻¹)) ≤
        (((k - 1 : ℕ) : ℝ))⁻¹ := by
    calc
      (∑ i ∈ Finset.Ioc (k - 1) n, (((i : ℝ) ^ 2)⁻¹))
          ≤ ∑ i ∈ Finset.Ioc (k - 1) (max (k - 1) n), (((i : ℝ) ^ 2)⁻¹) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro i hi
              exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hi).1,
                le_trans (Finset.mem_Ioc.mp hi).2 (le_max_right _ _)⟩
            · intro i _hi _hnot
              positivity
      _ ≤ (((k - 1 : ℕ) : ℝ))⁻¹ - (((max (k - 1) n : ℕ) : ℝ))⁻¹ :=
            sum_Ioc_inv_sq_le_sub (α := ℝ) hkpred_ne (le_max_left _ _)
      _ ≤ (((k - 1 : ℕ) : ℝ))⁻¹ := by
            exact sub_le_self _ (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hsum_inv (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    (∑ i ∈ Finset.Ioc (k - 1) n, (1 / (2 * (i : ℝ) ^ 2) : ℝ))
        = (1 / 2 : ℝ) * ∑ i ∈ Finset.Ioc (k - 1) n, (((i : ℝ) ^ 2)⁻¹) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          ring_nf
    _ ≤ (1 / 2 : ℝ) * (((k - 1 : ℕ) : ℝ))⁻¹ := hmul
    _ = 1 / (2 * ((k : ℝ) - 1)) := by
          have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
            rw [Nat.cast_sub hk.le]
            norm_num
          rw [hk1]
          field_simp [show (2 : ℝ) ≠ 0 by norm_num]


/-- The QPE phase-kickback state is periodic with period one in the eigenphase. -/
theorem phaseState_add_one (m : ℕ) (theta : ℝ) :
    phaseState m (theta + 1) = phaseState m theta := by
  ext k j
  simp [phaseState]
  left
  apply Circle.coe_injective
  change (Real.fourierChar ((k : ℕ) * (theta + 1)) : ℂ) =
    (Real.fourierChar ((k : ℕ) * theta) : ℂ)
  have harg :
      ((2 * Real.pi * ((k : ℕ) * (theta + 1)) : ℝ) : ℂ) * Complex.I =
        ((2 * Real.pi * ((k : ℕ) * theta) : ℝ) : ℂ) * Complex.I +
          ((2 * Real.pi * (k : ℕ) : ℝ) : ℂ) * Complex.I := by
    norm_num
    ring_nf
  rw [Real.fourierChar_apply, Real.fourierChar_apply, harg, Complex.exp_add]
  have hk : Complex.exp (((2 * Real.pi * (k : ℕ) : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [show (((2 * Real.pi * (k : ℕ) : ℝ) : ℂ) * Complex.I) =
        (k : ℕ) * ((2 * Real.pi : ℂ) * Complex.I) by
      norm_num
      ring_nf]
    rw [Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
  rw [hk, mul_one]

/-- Approximate-QPE amplitudes are periodic with period one in the eigenphase. -/
theorem qpeApproxAmplitude_add_one (m : ℕ) (theta : ℝ) (y : Fin (M m)) :
    qpeApproxAmplitude m (theta + 1) y = qpeApproxAmplitude m theta y := by
  unfold qpeApproxAmplitude
  rw [phaseState_add_one]

/-- Approximate-QPE probabilities are periodic with period one in the eigenphase. -/
theorem qpeApproxOutcomeProbability_add_one (m : ℕ) (theta : ℝ) (y : Fin (M m)) :
    qpeApproxOutcomeProbability m (theta + 1) y = qpeApproxOutcomeProbability m theta y := by
  unfold qpeApproxOutcomeProbability
  rw [qpeApproxAmplitude_add_one]

/-- Rewriting the negative eigenphase into the paper's wrapped phase `1 - theta`. -/
theorem qpeApproxOutcomeProbability_one_sub (m : ℕ) (theta : ℝ) (y : Fin (M m)) :
    qpeApproxOutcomeProbability m (1 - theta) y = qpeApproxOutcomeProbability m (-theta) y := by
  have h := qpeApproxOutcomeProbability_add_one m (-theta) y
  have harg : -theta + 1 = 1 - theta := by
    ring_nf
  simpa [harg] using h

/-- Closed-form geometric probability for an approximate-QPE outcome at phase error `delta = theta - y/M`.  This is the standard expression used to prove the
nearest-integer success bound; the `delta = 0` branch is the exact-phase case. -/
def qpeApproxGeometricProbability (N : ℕ) (delta : ℝ) : ℝ :=
  if delta = 0 then
    1
  else
    (Real.sin (Real.pi * (N : ℝ) * delta) /
      ((N : ℝ) * Real.sin (Real.pi * delta))) ^ 2


/-- Modular finite-tail summation step for the BHMT11 `k > 1` failure bound.

This separates the analytic/geometric work from the probability bookkeeping.  To
use it, provide a bucket index for every failed outcome, prove each bucket index
lies in the inverse-square tail, prove the pointwise `1/(4 i²)` probability bound
for its bucket, and prove that each bucket has at most two failed outcomes. -/
theorem qpeCircularFailureProbability_le_of_bucket_tail
    (m k n : ℕ) (theta : ℝ) (hk : 1 < k)
    (bucket : Fin (M m) → ℕ)
    (hbucket : ∀ y,
      y ∈ qpeCircularPhaseWindowFailureOutcomes m k theta →
        bucket y ∈ Finset.Ioc (k - 1) n)
    (hpoint : ∀ y,
      y ∈ qpeCircularPhaseWindowFailureOutcomes m k theta →
        qpeApproxOutcomeProbability m theta y ≤ 1 / (4 * (bucket y : ℝ) ^ 2))
    (hfiber : ∀ i,
      i ∈ Finset.Ioc (k - 1) n →
        ((qpeCircularPhaseWindowFailureOutcomes m k theta).filter
          (fun y => bucket y = i)).card ≤ 2) :
    qpeCircularPhaseWindowFailureProbability m k theta ≤
      1 / (2 * ((k : ℝ) - 1)) := by
  classical
  let F := qpeCircularPhaseWindowFailureOutcomes m k theta
  let T := Finset.Ioc (k - 1) n
  let p : Fin (M m) → ℝ := fun y => qpeApproxOutcomeProbability m theta y
  have hmap : ∀ y ∈ F, bucket y ∈ T := by
    intro y hy
    exact hbucket y hy
  have hpartition :
      (∑ i ∈ T, ∑ y ∈ F with bucket y = i, p y) = ∑ y ∈ F, p y := by
    exact Finset.sum_fiberwise_of_maps_to (s := F) (t := T) (g := bucket) hmap p
  have hfiber_sum : ∀ i ∈ T,
      (∑ y ∈ F with bucket y = i, p y) ≤ 1 / (2 * (i : ℝ) ^ 2) := by
    intro i hi
    let S := F.filter (fun y => bucket y = i)
    have hiNat_pos : 0 < i := by
      have hki : k - 1 < i := (Finset.mem_Ioc.mp hi).1
      omega
    have hiR_pos : 0 < (i : ℝ) := by exact_mod_cast hiNat_pos
    have hc_nonneg : 0 ≤ (1 / (4 * (i : ℝ) ^ 2) : ℝ) := by positivity
    have hsum_point :
        (∑ y ∈ S, p y) ≤ ∑ _y ∈ S, (1 / (4 * (i : ℝ) ^ 2) : ℝ) := by
      apply Finset.sum_le_sum
      intro y hy
      have hyF : y ∈ F := (Finset.mem_filter.mp hy).1
      have hbi : bucket y = i := (Finset.mem_filter.mp hy).2
      have hp := hpoint y hyF
      simpa [p, hbi] using hp
    have hconst :
        (∑ _y ∈ S, (1 / (4 * (i : ℝ) ^ 2) : ℝ)) =
          (S.card : ℝ) * (1 / (4 * (i : ℝ) ^ 2) : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hcardR : (S.card : ℝ) ≤ 2 := by
      exact_mod_cast hfiber i hi
    have hcard_mul :
        (S.card : ℝ) * (1 / (4 * (i : ℝ) ^ 2) : ℝ) ≤
          2 * (1 / (4 * (i : ℝ) ^ 2) : ℝ) :=
      mul_le_mul_of_nonneg_right hcardR hc_nonneg
    have htwo : 2 * (1 / (4 * (i : ℝ) ^ 2) : ℝ) = 1 / (2 * (i : ℝ) ^ 2) := by
      field_simp [hiR_pos.ne']
      norm_num
    calc
      (∑ y ∈ F with bucket y = i, p y) = ∑ y ∈ S, p y := by rfl
      _ ≤ ∑ _y ∈ S, (1 / (4 * (i : ℝ) ^ 2) : ℝ) := hsum_point
      _ = (S.card : ℝ) * (1 / (4 * (i : ℝ) ^ 2) : ℝ) := hconst
      _ ≤ 2 * (1 / (4 * (i : ℝ) ^ 2) : ℝ) := hcard_mul
      _ = 1 / (2 * (i : ℝ) ^ 2) := htwo
  have hsum_tail :
      (∑ i ∈ T, ∑ y ∈ F with bucket y = i, p y) ≤
        ∑ i ∈ T, (1 / (2 * (i : ℝ) ^ 2) : ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hfiber_sum i hi
  unfold qpeCircularPhaseWindowFailureProbability
  change (∑ y ∈ F, p y) ≤ 1 / (2 * ((k : ℝ) - 1))
  rw [← hpartition]
  exact le_trans hsum_tail (half_inv_sq_tail_sum_le k n hk)

/-- The real two-nearest-outcome core inequality for the BHMT11 `k = 1` constant.
For `x` the fractional part of `M * theta`, this is the normalized sum of the two
adjacent sine-ratio lower bounds. -/
def bhmtK1TwoNearestCore (x : ℝ) : ℝ :=
  Real.sin (Real.pi * x) ^ 2 / x ^ 2 +
    Real.sin (Real.pi * x) ^ 2 / (1 - x) ^ 2

theorem bhmtK1TwoNearestCore_symm (x : ℝ) :
    bhmtK1TwoNearestCore (1 - x) = bhmtK1TwoNearestCore x := by
  unfold bhmtK1TwoNearestCore
  have hsin : Real.sin (Real.pi * (1 - x)) = Real.sin (Real.pi * x) := by
    have harg : Real.pi * (1 - x) = Real.pi - Real.pi * x := by ring_nf
    rw [harg, Real.sin_pi_sub]
  rw [hsin]
  ring_nf

theorem bhmtK1TwoNearestCore_half : bhmtK1TwoNearestCore (1 / 2) = 8 := by
  unfold bhmtK1TwoNearestCore
  have harg : Real.pi * (1 / 2 : ℝ) = Real.pi / 2 := by ring_nf
  rw [harg, Real.sin_pi_div_two]
  norm_num



/-- Monotonicity on the left half, together with symmetry, gives the global `8`
lower bound.  This is the correct replacement for the false global-convexity
claim: the core function is decreasing on `(0, 1 / 2]` and then increasing by
symmetry. -/
theorem bhmtK1TwoNearestCore_ge_eight_of_antitone_left
    (hanti : AntitoneOn bhmtK1TwoNearestCore (Set.Ioc (0 : ℝ) (1 / 2)))
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    8 ≤ bhmtK1TwoNearestCore x := by
  by_cases hxhalf : x ≤ (1 / 2 : ℝ)
  · have hxmem : x ∈ Set.Ioc (0 : ℝ) (1 / 2) := ⟨hx0, hxhalf⟩
    have hhalfmem : (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) (1 / 2) := ⟨by norm_num, le_rfl⟩
    have hle : bhmtK1TwoNearestCore (1 / 2) ≤ bhmtK1TwoNearestCore x :=
      hanti hxmem hhalfmem hxhalf
    rw [bhmtK1TwoNearestCore_half] at hle
    exact hle
  · have hxhalf_lt : (1 / 2 : ℝ) < x := lt_of_not_ge hxhalf
    let z : ℝ := 1 - x
    have hz0 : 0 < z := by dsimp [z]; linarith
    have hzhalf : z ≤ (1 / 2 : ℝ) := by dsimp [z]; linarith
    have hzmem : z ∈ Set.Ioc (0 : ℝ) (1 / 2) := ⟨hz0, hzhalf⟩
    have hhalfmem : (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) (1 / 2) := ⟨by norm_num, le_rfl⟩
    have hle_z : bhmtK1TwoNearestCore (1 / 2) ≤ bhmtK1TwoNearestCore z :=
      hanti hzmem hhalfmem hzhalf
    have hsym : bhmtK1TwoNearestCore x = bhmtK1TwoNearestCore z := by
      dsimp [z]
      have h := bhmtK1TwoNearestCore_symm x
      simpa using h.symm
    rw [hsym]
    rw [bhmtK1TwoNearestCore_half] at hle_z
    exact hle_z

/-- Explicit derivative of the two-nearest core away from the singular endpoints. -/
theorem deriv_bhmtK1TwoNearestCore
    {x : ℝ} (hx0 : x ≠ 0) (hx1 : 1 - x ≠ 0) :
    deriv bhmtK1TwoNearestCore x =
      2 * Real.pi * Real.sin (Real.pi * x) * Real.cos (Real.pi * x) / x ^ 2 -
        2 * Real.sin (Real.pi * x) ^ 2 / x ^ 3 +
      (2 * Real.pi * Real.sin (Real.pi * x) * Real.cos (Real.pi * x) / (1 - x) ^ 2 +
        2 * Real.sin (Real.pi * x) ^ 2 / (1 - x) ^ 3) := by
  unfold bhmtK1TwoNearestCore
  have hdiff_left : DifferentiableAt ℝ (fun x : ℝ => Real.sin (Real.pi * x) ^ 2 / x ^ 2) x := by
    exact DifferentiableAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 hx0)
  have hdiff_right : DifferentiableAt ℝ (fun x : ℝ => Real.sin (Real.pi * x) ^ 2 / (1 - x) ^ 2) x := by
    exact DifferentiableAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 hx1)
  rw [deriv_fun_add hdiff_left hdiff_right]
  have hden0 : (fun t : ℝ => t ^ 2) x ≠ 0 := by
    exact pow_ne_zero 2 hx0
  have hden1 : (fun t : ℝ => (1 - t) ^ 2) x ≠ 0 := by
    simpa using pow_ne_zero 2 hx1
  rw [deriv_fun_div
    (c := fun t : ℝ => Real.sin (Real.pi * t) ^ 2)
    (d := fun t : ℝ => t ^ 2)
    (x := x) (by fun_prop) (by fun_prop) hden0]
  rw [deriv_fun_div
    (c := fun t : ℝ => Real.sin (Real.pi * t) ^ 2)
    (d := fun t : ℝ => (1 - t) ^ 2)
    (x := x) (by fun_prop) (by fun_prop) hden1]
  have hsin2deriv :
      deriv (fun t : ℝ => Real.sin (Real.pi * t) ^ 2) x =
        2 * Real.pi * Real.sin (Real.pi * x) * Real.cos (Real.pi * x) := by
    rw [deriv_fun_pow (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => Real.sin (Real.pi * t)) x) 2]
    rw [show deriv (fun t : ℝ => Real.sin (Real.pi * t)) x = Real.pi * Real.cos (Real.pi * x) by
      simp [mul_comm]]
    ring_nf
  have hsubderiv : deriv (fun t : ℝ => 1 - t) x = -1 := by
    simp [sub_eq_add_neg]
  rw [hsin2deriv]
  rw [deriv_fun_pow (by fun_prop : DifferentiableAt ℝ (fun x : ℝ => 1 - x) x) 2]
  rw [hsubderiv]
  simp
  field_simp [hx0, hx1]



/-- Derivative-sign reduction for the left-half monotonicity statement.  The only
remaining real-analysis content is to prove the displayed derivative is nonpositive
on `(0, 1 / 2)`. -/
theorem bhmtK1TwoNearestCore_antitone_left_of_deriv_nonpos
    (hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (1 / 2), deriv bhmtK1TwoNearestCore x ≤ 0) :
    AntitoneOn bhmtK1TwoNearestCore (Set.Ioc (0 : ℝ) (1 / 2)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioc (0 : ℝ) (1 / 2)) ?hcont ?hdiff ?hderiv
  · unfold bhmtK1TwoNearestCore
    apply ContinuousOn.add
    · apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro x hx
        exact pow_ne_zero 2 (ne_of_gt hx.1)
    · apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro x hx
        exact pow_ne_zero 2 (ne_of_gt (by linarith [hx.2]))
  · rw [interior_Ioc]
    unfold bhmtK1TwoNearestCore
    apply DifferentiableOn.add
    · apply DifferentiableOn.div
      · fun_prop
      · fun_prop
      · intro x hx
        exact pow_ne_zero 2 (ne_of_gt hx.1)
    · apply DifferentiableOn.div
      · fun_prop
      · fun_prop
      · intro x hx
        exact pow_ne_zero 2 (ne_of_gt (by linarith [hx.2]))
  · intro x hx
    rw [interior_Ioc] at hx
    exact hderiv x hx



theorem qpeApproxGeometricProbability_neg (N : ℕ) (delta : ℝ) :
    qpeApproxGeometricProbability N (-delta) = qpeApproxGeometricProbability N delta := by
  unfold qpeApproxGeometricProbability
  by_cases h : delta = 0
  · simp [h]
  · have hneg : -delta ≠ 0 := neg_ne_zero.mpr h
    simp [h, hneg, Real.sin_neg]

/-- Lower bound for a geometric QPE probability at scaled offset `x / N`. -/
theorem qpeApproxGeometricProbability_lower_bound_scaled
    {N : ℕ} {x : ℝ} (hN : 0 < N) (hx0 : 0 < x) (hx1 : x < 1) :
    Real.sin (Real.pi * x) ^ 2 / (Real.pi ^ 2 * x ^ 2) ≤
      qpeApproxGeometricProbability N (x / (N : ℝ)) := by
  unfold qpeApproxGeometricProbability
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hdelta : x / (N : ℝ) ≠ 0 := by positivity
  simp [hdelta]
  have hNx : (N : ℝ) * (x / (N : ℝ)) = x := by field_simp [hNpos.ne']
  have hargN : Real.pi * (N : ℝ) * (x / (N : ℝ)) = Real.pi * x := by
    rw [mul_assoc, hNx]
  rw [hargN]
  have hxN_pos : 0 < Real.pi * (x / (N : ℝ)) := by positivity
  have hxN_lt_pi : Real.pi * (x / (N : ℝ)) < Real.pi := by
    have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hx_div_lt_one : x / (N : ℝ) < 1 := by
      rw [div_lt_one hNpos]
      nlinarith
    nlinarith [Real.pi_pos, hx_div_lt_one]
  have hden_pos : 0 < Real.sin (Real.pi * (x / (N : ℝ))) :=
    Real.sin_pos_of_pos_of_lt_pi hxN_pos hxN_lt_pi
  have hnum_nonneg : 0 ≤ Real.sin (Real.pi * x) := by
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos, hx1])
  have hsmall_den : (N : ℝ) * Real.sin (Real.pi * (x / (N : ℝ))) ≤ Real.pi * x := by
    have hsin_le := Real.sin_le (le_of_lt hxN_pos)
    calc
      (N : ℝ) * Real.sin (Real.pi * (x / (N : ℝ)))
          ≤ (N : ℝ) * (Real.pi * (x / (N : ℝ))) := by
            gcongr
      _ = Real.pi * x := by field_simp [hNpos.ne']
  have hden_total_pos : 0 < (N : ℝ) * Real.sin (Real.pi * (x / (N : ℝ))) := by positivity
  have hratio :
      Real.sin (Real.pi * x) / (Real.pi * x) ≤
        Real.sin (Real.pi * x) / ((N : ℝ) * Real.sin (Real.pi * (x / (N : ℝ)))) := by
    exact div_le_div_of_nonneg_left hnum_nonneg hden_total_pos hsmall_den
  have hratio_sq :=
    pow_le_pow_left₀ (by positivity : 0 ≤ Real.sin (Real.pi * x) / (Real.pi * x)) hratio 2
  calc
    Real.sin (Real.pi * x) ^ 2 / (Real.pi ^ 2 * x ^ 2)
        = (Real.sin (Real.pi * x) / (Real.pi * x)) ^ 2 := by
          field_simp [Real.pi_ne_zero, ne_of_gt hx0]
    _ ≤ (Real.sin (Real.pi * x) /
          ((N : ℝ) * Real.sin (Real.pi * (x / (N : ℝ))))) ^ 2 := hratio_sq

/-- The normalized two-nearest core bounds the sum of the two adjacent geometric
QPE probabilities. -/
theorem qpeApproxGeometricProbability_two_nearest_lower_bound_of_core
    {N : ℕ} {x : ℝ} (hN : 0 < N) (hx0 : 0 < x) (hx1 : x < 1) :
    bhmtK1TwoNearestCore x / Real.pi ^ 2 ≤
      qpeApproxGeometricProbability N (x / (N : ℝ)) +
        qpeApproxGeometricProbability N (-(1 - x) / (N : ℝ)) := by
  have hleft := qpeApproxGeometricProbability_lower_bound_scaled (N := N) hN hx0 hx1
  have hx10 : 0 < 1 - x := by linarith
  have hx11 : 1 - x < 1 := by linarith
  have hright_pos := qpeApproxGeometricProbability_lower_bound_scaled (N := N) hN hx10 hx11
  have hnegarg : -(1 - x) / (N : ℝ) = -((1 - x) / (N : ℝ)) := by ring_nf
  rw [hnegarg, qpeApproxGeometricProbability_neg N ((1 - x) / (N : ℝ))]
  have hcore : bhmtK1TwoNearestCore x / Real.pi ^ 2 =
      Real.sin (Real.pi * x) ^ 2 / (Real.pi ^ 2 * x ^ 2) +
        Real.sin (Real.pi * (1 - x)) ^ 2 / (Real.pi ^ 2 * (1 - x) ^ 2) := by
    unfold bhmtK1TwoNearestCore
    have hsin1 : Real.sin (Real.pi * (1 - x)) = Real.sin (Real.pi * x) := by
      have harg : Real.pi * (1 - x) = Real.pi - Real.pi * x := by ring_nf
      rw [harg, Real.sin_pi_sub]
    rw [hsin1]
    field_simp [Real.pi_ne_zero, ne_of_gt hx0, ne_of_gt hx10]
  rw [hcore]
  exact add_le_add hleft hright_pos



/-- Conditional `k = 1` two-nearest geometric lower bound from left-half
monotonicity of the core real function. -/
theorem qpeApproxGeometricProbability_two_nearest_lower_bound_k1_of_core_antitone_left
    {N : ℕ} {x : ℝ}
    (hanti : AntitoneOn bhmtK1TwoNearestCore (Set.Ioc (0 : ℝ) (1 / 2)))
    (hN : 0 < N) (hx0 : 0 < x) (hx1 : x < 1) :
    8 / Real.pi ^ 2 ≤
      qpeApproxGeometricProbability N (x / (N : ℝ)) +
        qpeApproxGeometricProbability N (-(1 - x) / (N : ℝ)) := by
  have hcore := qpeApproxGeometricProbability_two_nearest_lower_bound_of_core (N := N) hN hx0 hx1
  have h8 := bhmtK1TwoNearestCore_ge_eight_of_antitone_left hanti hx0 hx1
  have hpi_sq_pos : 0 < Real.pi ^ 2 := sq_pos_of_ne_zero Real.pi_ne_zero
  exact le_trans (div_le_div_of_nonneg_right h8 hpi_sq_pos.le) hcore

/-- If two distinct outcomes are in a circular success window, then any lower bound
on their combined probability is also a lower bound on the whole window probability. -/
theorem qpeCircularPhaseWindowProbability_lower_bound_two_outcomes
    (m k : ℕ) (theta : ℝ) (y₀ y₁ : Fin (M m)) {c : ℝ}
    (hy₀ : y₀ ∈ qpeCircularPhaseWindowOutcomes m k theta)
    (hy₁ : y₁ ∈ qpeCircularPhaseWindowOutcomes m k theta)
    (hy₀₁ : y₀ ≠ y₁)
    (hprob : c ≤ qpeApproxOutcomeProbability m theta y₀ +
      qpeApproxOutcomeProbability m theta y₁) :
    c ≤ qpeCircularPhaseWindowProbability m k theta := by
  classical
  let pair : Finset (Fin (M m)) := {y₀, y₁}
  have hsubset : pair ⊆ qpeCircularPhaseWindowOutcomes m k theta := by
    intro y hy
    simp [pair] at hy
    rcases hy with rfl | rfl
    · exact hy₀
    · exact hy₁
  have hpair_sum :
      pair.sum (fun y => qpeApproxOutcomeProbability m theta y) =
        qpeApproxOutcomeProbability m theta y₀ +
          qpeApproxOutcomeProbability m theta y₁ := by
    simp [pair, hy₀₁]
  have hpair_le_window :
      pair.sum (fun y => qpeApproxOutcomeProbability m theta y) ≤
        (qpeCircularPhaseWindowOutcomes m k theta).sum
          (fun y => qpeApproxOutcomeProbability m theta y) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by intro y _hyBig _hyNot; exact qpeApproxOutcomeProbability_nonneg m theta y)
  unfold qpeCircularPhaseWindowProbability
  rw [hpair_sum] at hpair_le_window
  exact le_trans hprob hpair_le_window

/-- `k = 1` circular-window lower bound from two explicitly identified adjacent
outcomes.  This packages the already-proved two-nearest geometric estimate with
the finset/probability bookkeeping for the circular window; the real core
inequality remains isolated in `hanti`. -/
theorem qpeCircularPhaseWindowProbability_lower_bound_k1_of_two_adjacent_geometric
    (m : ℕ) {theta x : ℝ} (y₀ y₁ : Fin (M m))
    (hanti : AntitoneOn bhmtK1TwoNearestCore (Set.Ioc (0 : ℝ) (1 / 2)))
    (hx₀ : 0 < x) (hx₁ : x < 1)
    (hy₀win : y₀ ∈ qpeCircularPhaseWindowOutcomes m 1 theta)
    (hy₁win : y₁ ∈ qpeCircularPhaseWindowOutcomes m 1 theta)
    (hy₀₁ : y₀ ≠ y₁)
    (hprob₀ : qpeApproxOutcomeProbability m theta y₀ =
      qpeApproxGeometricProbability (M m) (x / (M m : ℝ)))
    (hprob₁ : qpeApproxOutcomeProbability m theta y₁ =
      qpeApproxGeometricProbability (M m) (-(1 - x) / (M m : ℝ))) :
    8 / Real.pi ^ 2 ≤ qpeCircularPhaseWindowProbability m 1 theta := by
  have hgeom := qpeApproxGeometricProbability_two_nearest_lower_bound_k1_of_core_antitone_left
    (N := M m) (x := x) hanti (Nat.two_pow_pos m) hx₀ hx₁
  apply qpeCircularPhaseWindowProbability_lower_bound_two_outcomes
    (m := m) (k := 1) (theta := theta) (y₀ := y₀) (y₁ := y₁)
    hy₀win hy₁win hy₀₁
  simpa [hprob₀, hprob₁] using hgeom

/-- The controlled-power operator `Σ_k |k⟩⟨k| ⊗ U^k`.

Rows and columns are decoded as pairs `(counting-register index, target index)`.
The operator is block diagonal: inside the block selected by `k`, it applies
`U^k` to the target register. -/
def controlledPowerMatrix {n : ℕ} (m : ℕ) (U : Square n) : Square (M m * n) :=
  fun row col =>
    let rowPair := finProdFinEquiv.symm row
    let colPair := finProdFinEquiv.symm col
    if rowPair.1 = colPair.1 then
      (U ^ (colPair.1 : ℕ)) rowPair.2 colPair.2
    else
      0

@[simp] theorem uniformState_apply (m : ℕ) (k : Fin (M m)) :
    uniformState m k 0 = ((M m : ℝ)⁻¹.sqrt : ℂ) := by
  rfl

@[simp] theorem qftMatrix_apply (m : ℕ) (row col : Fin (M m)) :
    qftMatrix m row col = ((M m : ℝ)⁻¹.sqrt : ℂ) *
      (Real.fourierChar (((row : ℕ) * (col : ℕ) : ℝ) / (M m : ℝ)) : ℂ) := by
  rfl

@[simp] theorem inverseQFTMatrix_apply (m : ℕ) (row col : Fin (M m)) :
    inverseQFTMatrix m row col = ((M m : ℝ)⁻¹.sqrt : ℂ) *
      (Real.fourierChar (-(((row : ℕ) * (col : ℕ) : ℝ) / (M m : ℝ))) : ℂ) := by
  rfl

@[simp] theorem phaseState_apply (m : ℕ) (theta : ℝ) (k : Fin (M m)) :
    phaseState m theta k 0 = (((M m : ℝ).sqrt : ℂ)⁻¹) * (Real.fourierChar ((k : ℕ) * theta) : ℂ) := by
  rfl

/-- The approximate-QPE amplitude is the inverse-QFT coefficient of the kicked-back phase state. -/
theorem qpeApproxAmplitude_eq_sum (m : ℕ) (theta : ℝ) (y : Fin (M m)) :
    qpeApproxAmplitude m theta y =
      ∑ k : Fin (M m), inverseQFTMatrix m y k * phaseState m theta k 0 := by
  rfl

@[simp] theorem controlledPowerMatrix_apply_same {n : ℕ} (m : ℕ) (U : Square n)
    (k : Fin (M m)) (i j : Fin n) :
    controlledPowerMatrix m U (finProdFinEquiv (k, i)) (finProdFinEquiv (k, j)) =
      (U ^ (k : ℕ)) i j := by
  simp [controlledPowerMatrix]

@[simp] theorem controlledPowerMatrix_apply_ne {n : ℕ} (m : ℕ) (U : Square n)
    {k l : Fin (M m)} (i j : Fin n) (hkl : k ≠ l) :
    controlledPowerMatrix m U (finProdFinEquiv (k, i)) (finProdFinEquiv (l, j)) = 0 := by
  simp [controlledPowerMatrix, hkl]

/-- The QFT matrix sends a computational-basis state to the corresponding
Fourier state. -/
theorem qftMatrix_mul_basisState (m : ℕ) (y : Fin (M m)) :
    qftMatrix m ⬝ Vector.basis y = fourierState m y := by
  ext k col
  fin_cases col
  simp [qftMatrix, Vector.basis, Vector.basis, Matrix.mul, _root_.Matrix.mul_apply, fourierState]

/-- Powers of a matrix preserve an eigenvector equation. -/
theorem matrix_power_eigenvector {n : ℕ} {U : Square n} {ψ : Vector n} {lam : ℂ}
    (h : U ⬝ ψ = lam • ψ) :
    ∀ k : ℕ, (U ^ k) ⬝ ψ = (lam ^ k) • ψ := by
  intro k
  induction k with
  | zero =>
      simp [Matrix.mul]
  | succ k ih =>
      calc
        (U ^ (Nat.succ k)) ⬝ ψ = U ⬝ ((U ^ k) ⬝ ψ) := by
          change (U ^ (Nat.succ k)) * ψ = U * ((U ^ k) * ψ)
          rw [pow_succ']
          rw [_root_.Matrix.mul_assoc]
        _ = U ⬝ ((lam ^ k) • ψ) := by rw [ih]
        _ = (lam ^ k) • (U ⬝ ψ) := by simp [Matrix.mul, _root_.Matrix.mul_smul]
        _ = (lam ^ k) • (lam • ψ) := by rw [h]
        _ = (lam ^ Nat.succ k) • ψ := by
          rw [pow_succ]
          simp [smul_smul, mul_comm]

/-- Powers of a unitary matrix are unitary. -/
theorem matrix_isUnitary_pow {n : ℕ} {U : Square n} (hU : Matrix.isUnitary U) :
    ∀ k : ℕ, Matrix.isUnitary (U ^ k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ']
      change Matrix.isUnitary (U ⬝ (U ^ k))
      exact Matrix.isUnitary_mul hU ih


/-- The block-diagonal controlled-power matrix is unitary whenever the target
unitary `U` is unitary. -/
theorem controlledPowerMatrix_adjoint_mul_self {n : ℕ} {m : ℕ} {U : Square n}
    (hU : Matrix.isUnitary U) :
    (controlledPowerMatrix m U)† ⬝ controlledPowerMatrix m U = I (M m * n) := by
  ext row col
  rw [← finProdFinEquiv.apply_symm_apply row]
  rw [← finProdFinEquiv.apply_symm_apply col]
  rcases finProdFinEquiv.symm row with ⟨k, i⟩
  rcases finProdFinEquiv.symm col with ⟨l, j⟩
  simp [Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply]
  calc
    (∑ x : Fin (M m * n),
        star (controlledPowerMatrix m U x (finProdFinEquiv (k, i))) *
          controlledPowerMatrix m U x (finProdFinEquiv (l, j)))
        = ∑ p : Fin (M m) × Fin n,
            star (controlledPowerMatrix m U (finProdFinEquiv p) (finProdFinEquiv (k, i))) *
              controlledPowerMatrix m U (finProdFinEquiv p) (finProdFinEquiv (l, j)) := by
          symm
          exact Fintype.sum_equiv finProdFinEquiv
            (fun p : Fin (M m) × Fin n =>
              star (controlledPowerMatrix m U (finProdFinEquiv p) (finProdFinEquiv (k, i))) *
                controlledPowerMatrix m U (finProdFinEquiv p) (finProdFinEquiv (l, j)))
            (fun x : Fin (M m * n) =>
              star (controlledPowerMatrix m U x (finProdFinEquiv (k, i))) *
                controlledPowerMatrix m U x (finProdFinEquiv (l, j)))
            (by intro p; rfl)
    _ = ∑ a : Fin (M m), ∑ b : Fin n,
            star (controlledPowerMatrix m U (finProdFinEquiv (a, b)) (finProdFinEquiv (k, i))) *
              controlledPowerMatrix m U (finProdFinEquiv (a, b)) (finProdFinEquiv (l, j)) := by
          rw [Fintype.sum_prod_type]
    _ = (1 : Square (M m * n)) (finProdFinEquiv (k, i)) (finProdFinEquiv (l, j)) := by
          by_cases hkl : k = l
          · subst l
            have hpow : (U ^ (k : ℕ))† ⬝ (U ^ (k : ℕ)) = (1 : Square n) :=
              (Matrix.isUnitary_iff_adjoint_mul_self (U ^ (k : ℕ))).mp (matrix_isUnitary_pow hU (k : ℕ))
            have hij := congrFun (congrFun hpow i) j
            change (∑ x : Fin n, star ((U ^ (k : ℕ)) x i) * (U ^ (k : ℕ)) x j) =
              (1 : Square n) i j at hij
            have hOne : (1 : Square (M m * n)) (finProdFinEquiv (k, i)) (finProdFinEquiv (k, j)) =
                (1 : Square n) i j := by
              simp [_root_.Matrix.one_apply]
            rw [hOne]
            simpa [controlledPowerMatrix] using hij
          · have hlk : l ≠ k := by
              intro h
              exact hkl h.symm
            simp [controlledPowerMatrix, hkl, hlk]

/-- The concrete controlled-power matrix is unitary whenever `U` is unitary. -/
theorem controlledPowerMatrix_isUnitary {n : ℕ} (m : ℕ) {U : Square n}
    (hU : Matrix.isUnitary U) : Matrix.isUnitary (controlledPowerMatrix m U) := by
  rw [Matrix.isUnitary_iff_adjoint_mul_self]
  exact controlledPowerMatrix_adjoint_mul_self hU

/-- Exact phases are a special case of the arbitrary kicked-back phase state. -/
theorem phaseState_eq_fourierState (m : ℕ) (y : Fin (M m)) :
    phaseState m (((y : ℕ) : ℝ) / (M m : ℝ)) = fourierState m y := by
  ext k col
  fin_cases col
  unfold phaseState fourierState
  calc
    (((M m : ℝ).sqrt : ℂ)⁻¹) * (Real.fourierChar (((k : ℕ) : ℝ) * (((y : ℕ) : ℝ) / (M m : ℝ))) : ℂ)
        = (((M m : ℝ).sqrt : ℂ)⁻¹) * (Real.fourierChar ((((k : ℕ) * (y : ℕ) : ℝ) / (M m : ℝ))) : ℂ) := by
          congr 1
          field_simp [show (M m : ℝ) ≠ 0 by exact_mod_cast (NeZero.ne (M m))]
    _ = ((M m : ℝ)⁻¹.sqrt : ℂ) * (Real.fourierChar ((((k : ℕ) * (y : ℕ) : ℝ) / (M m : ℝ))) : ℂ) := by
          simp

/-- Sum of a nontrivial `M`th root of unity over one full period.  This is the
geometric-series orthogonality theorem underlying QFT unitarity. -/
theorem phase_root_sum_fin_eq_zero (m : ℕ) (d : Fin (M m)) (hd : d ≠ 0) :
    (∑ k : Fin (M m), (Real.fourierChar (((k : ℕ) * (d : ℕ) : ℝ) / (M m : ℝ)) : ℂ)) = 0 := by
  let ζ := (Real.fourierChar (1 / (M m : ℝ)) : ℂ)
  have hζ : IsPrimitiveRoot ζ (M m) := by
    dsimp [ζ]
    rw [Real.fourierChar_apply]
    convert Complex.isPrimitiveRoot_exp (M m) (NeZero.ne (M m)) using 1
    norm_num
    ring_nf
  let z := (Real.fourierChar ((d : ℕ) / (M m : ℝ)) : ℂ)
  have hzpow : z = ζ ^ (d : ℕ) := by
    dsimp [z, ζ]
    norm_cast
    convert AddChar.map_nsmul_eq_pow Real.fourierChar (d : ℕ) (1 / (M m : ℝ)) using 1
    simp [nsmul_eq_mul]
    ring_nf
  have hzN : z ^ (M m) = 1 := by
    rw [hzpow, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hzne : z ≠ 1 := by
    intro h1
    have hdiv : (M m) ∣ (d : ℕ) := by
      rw [← hζ.pow_eq_one_iff_dvd]
      rw [← hzpow]
      exact h1
    have hlt : (d : ℕ) < M m := d.isLt
    have hzero : (d : ℕ) = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
    exact hd (Fin.ext hzero)
  calc
    (∑ k : Fin (M m), (Real.fourierChar (((k : ℕ) * (d : ℕ) : ℝ) / (M m : ℝ)) : ℂ))
        = ∑ k : Fin (M m), z ^ (k : ℕ) := by
          apply Finset.sum_congr rfl
          intro k hk
          dsimp [z]
          rw [show (((k : ℕ) * (d : ℕ) : ℝ) / (M m : ℝ)) =
              ((k : ℕ) : ℝ) * (((d : ℕ) : ℝ) / (M m : ℝ)) by
            field_simp [show (M m : ℝ) ≠ 0 by exact_mod_cast (NeZero.ne (M m))]]
          rw [show (Real.fourierChar (((k : ℕ) : ℝ) * (((d : ℕ) : ℝ) / (M m : ℝ))) : ℂ) =
              (Real.fourierChar (((d : ℕ) : ℝ) / (M m : ℝ)) : ℂ) ^ (k : ℕ) by
            rw [← nsmul_eq_mul]
            norm_cast
            exact AddChar.map_nsmul_eq_pow Real.fourierChar (k : ℕ) (((d : ℕ) : ℝ) / (M m : ℝ))]
    _ = ∑ i ∈ Finset.range (M m), z ^ i := by
          exact (Finset.sum_range (fun i => z ^ i)).symm
    _ = 0 := by
          rw [geom_sum_eq hzne (M m), hzN, sub_self, zero_div]

/-- Full-period root-of-unity sum: the trivial frequency contributes `M`, and
every nontrivial frequency contributes zero. -/
theorem phase_root_sum_fin (m : ℕ) (d : Fin (M m)) :
    (∑ k : Fin (M m), (Real.fourierChar (((k : ℕ) * (d : ℕ) : ℝ) / (M m : ℝ)) : ℂ)) =
      if d = 0 then (M m : ℂ) else 0 := by
  by_cases hd : d = 0
  · simp [hd]
  · simp [hd, phase_root_sum_fin_eq_zero m d hd]

/-- The same roots-of-unity orthogonality theorem in mathlib's additive-character
form over `ZMod`. -/
theorem zmod_stdAddChar_orthogonality (m : ℕ) (d : ZMod (M m)) :
    (∑ x : ZMod (M m), ZMod.stdAddChar (x * d)) = if d = 0 then (M m : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (R := ZMod (M m)) (R' := ℂ)
    (ψ := ZMod.stdAddChar) d (ZMod.isPrimitive_stdAddChar (M m))
  simpa [ZMod.card (M m)] using h

/-- A one-step eigenphase equation implies the power action required by the
controlled-power stage. -/
theorem controlled_power_eigenphase_action {n : ℕ} {m : ℕ} {U : Square n}
    {ψ : Vector n} {y : Fin (M m)}
    (h : U ⬝ ψ = ((Real.fourierChar ((y : ℕ) / (M m : ℝ)) : ℂ)) • ψ) :
    ∀ k : Fin (M m), (U ^ (k : ℕ)) ⬝ ψ =
      ((Real.fourierChar (((k : ℕ) * (y : ℕ) : ℝ) / (M m : ℝ)) : ℂ)) • ψ := by
  intro k
  have hphase :
      (Real.fourierChar (((k : ℕ) : ℝ) * (((y : ℕ) : ℝ) / (M m : ℝ))) : ℂ) =
        (Real.fourierChar (((y : ℕ) : ℝ) / (M m : ℝ)) : ℂ) ^ (k : ℕ) := by
    rw [← nsmul_eq_mul]
    norm_cast
    exact AddChar.map_nsmul_eq_pow Real.fourierChar (k : ℕ) (((y : ℕ) : ℝ) / (M m : ℝ))
  have hpow := matrix_power_eigenvector h (k : ℕ)
  rw [← hphase] at hpow
  convert hpow using 1
  congr 1
  field_simp [show (M m : ℝ) ≠ 0 by exact_mod_cast (NeZero.ne (M m))]

/-- The concrete controlled-power matrix maps the prepared uniform counting
register and an exact eigenvector to the Fourier state required by QPE. -/
theorem controlledPowerMatrix_mul_uniform_of_power_action {n : ℕ} {m : ℕ}
    {U : Square n} {ψ : Vector n} {y : Fin (M m)}
    (hpow : ∀ k : Fin (M m), (U ^ (k : ℕ)) ⬝ ψ =
      ((Real.fourierChar (((k : ℕ) * (y : ℕ) : ℝ) / (M m : ℝ)) : ℂ)) • ψ) :
    controlledPowerMatrix m U ⬝ (uniformState m ⊗ ψ) = fourierState m y ⊗ ψ := by
  ext row col
  fin_cases col
  rw [← finProdFinEquiv.apply_symm_apply row]
  rcases finProdFinEquiv.symm row with ⟨k, i⟩
  change (∑ x : Fin (M m * n),
      controlledPowerMatrix m U (finProdFinEquiv (k, i)) x *
        (uniformState m ⊗ ψ) x 0) = (fourierState m y ⊗ ψ) (finProdFinEquiv (k, i)) 0
  calc
    (∑ x : Fin (M m * n), controlledPowerMatrix m U (finProdFinEquiv (k, i)) x *
        (uniformState m ⊗ ψ) x 0)
        = ∑ p : Fin (M m) × Fin n,
            controlledPowerMatrix m U (finProdFinEquiv (k, i)) (finProdFinEquiv p) *
              (uniformState m ⊗ ψ) (finProdFinEquiv p) 0 := by
          symm
          exact Fintype.sum_equiv finProdFinEquiv
            (fun p : Fin (M m) × Fin n =>
              controlledPowerMatrix m U (finProdFinEquiv (k, i)) (finProdFinEquiv p) *
                (uniformState m ⊗ ψ) (finProdFinEquiv p) 0)
            (fun x : Fin (M m * n) =>
              controlledPowerMatrix m U (finProdFinEquiv (k, i)) x *
                (uniformState m ⊗ ψ) x 0)
            (by intro p; rfl)
    _ = ∑ a : Fin (M m), ∑ b : Fin n,
            controlledPowerMatrix m U (finProdFinEquiv (k, i)) (finProdFinEquiv (a, b)) *
              (uniformState m ⊗ ψ) (finProdFinEquiv (a, b)) 0 := by
          rw [Fintype.sum_prod_type]
    _ = (fourierState m y ⊗ ψ) (finProdFinEquiv (k, i)) 0 := by
          have hki := congrFun (congrFun (hpow k) i) 0
          simp [Matrix.mul, _root_.Matrix.mul_apply] at hki
          have hcol0 : (finProdFinEquiv.symm (0 : Fin (1 * 1))).1 = (0 : Fin 1) :=
            Subsingleton.elim _ _
          have hcol1 : (finProdFinEquiv.symm (0 : Fin (1 * 1))).2 = (0 : Fin 1) :=
            Subsingleton.elim _ _
          simp [controlledPowerMatrix, Matrix.kron, hcol0, hcol1]
          calc
            ∑ x, (U ^ ↑k) i x * ((((M m : ℝ).sqrt : ℂ)⁻¹) * ψ x 0)
                = (((M m : ℝ).sqrt : ℂ)⁻¹) * (∑ x, (U ^ ↑k) i x * ψ x 0) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro x hx
                  ring_nf
            _ = (((M m : ℝ).sqrt : ℂ)⁻¹) *
                ((Real.fourierChar (↑↑k * ↑↑y / ↑(M m)) : ℂ) * ψ i 0) := by
                  rw [hki]
            _ = (((M m : ℝ).sqrt : ℂ)⁻¹) * (Real.fourierChar (↑↑k * ↑↑y / ↑(M m)) : ℂ) * ψ i 0 := by
                  ring_nf
            _ = fourierState m y k 0 * ψ i 0 := by
                  simp [fourierState]

/-- Controlled powers produce the QPE Fourier state from the usual one-step
eigenphase equation. -/
theorem controlledPowerMatrix_mul_uniform_of_eigenphase {n : ℕ} {m : ℕ}
    {U : Square n} {ψ : Vector n} {y : Fin (M m)}
    (h : U ⬝ ψ = ((Real.fourierChar ((y : ℕ) / (M m : ℝ)) : ℂ)) • ψ) :
    controlledPowerMatrix m U ⬝ (uniformState m ⊗ ψ) = fourierState m y ⊗ ψ := by
  exact controlledPowerMatrix_mul_uniform_of_power_action
    (controlled_power_eigenphase_action h)


/-- Controlled powers produce the kicked-back phase state for an arbitrary real eigenphase. -/
theorem controlledPowerMatrix_mul_uniform_of_real_power_action {n : ℕ} {m : ℕ}
    {U : Square n} {ψ : Vector n} {theta : ℝ}
    (hpow : ∀ k : Fin (M m), (U ^ (k : ℕ)) ⬝ ψ = ((Real.fourierChar ((k : ℕ) * theta) : ℂ)) • ψ) :
    controlledPowerMatrix m U ⬝ (uniformState m ⊗ ψ) = phaseState m theta ⊗ ψ := by
  ext row col
  fin_cases col
  rw [← finProdFinEquiv.apply_symm_apply row]
  rcases finProdFinEquiv.symm row with ⟨k, i⟩
  change (∑ x : Fin (M m * n),
      controlledPowerMatrix m U (finProdFinEquiv (k, i)) x *
        (uniformState m ⊗ ψ) x 0) = (phaseState m theta ⊗ ψ) (finProdFinEquiv (k, i)) 0
  calc
    (∑ x : Fin (M m * n), controlledPowerMatrix m U (finProdFinEquiv (k, i)) x *
        (uniformState m ⊗ ψ) x 0)
        = ∑ p : Fin (M m) × Fin n,
            controlledPowerMatrix m U (finProdFinEquiv (k, i)) (finProdFinEquiv p) *
              (uniformState m ⊗ ψ) (finProdFinEquiv p) 0 := by
          symm
          exact Fintype.sum_equiv finProdFinEquiv
            (fun p : Fin (M m) × Fin n =>
              controlledPowerMatrix m U (finProdFinEquiv (k, i)) (finProdFinEquiv p) *
                (uniformState m ⊗ ψ) (finProdFinEquiv p) 0)
            (fun x : Fin (M m * n) =>
              controlledPowerMatrix m U (finProdFinEquiv (k, i)) x *
                (uniformState m ⊗ ψ) x 0)
            (by intro p; rfl)
    _ = ∑ a : Fin (M m), ∑ b : Fin n,
            controlledPowerMatrix m U (finProdFinEquiv (k, i)) (finProdFinEquiv (a, b)) *
              (uniformState m ⊗ ψ) (finProdFinEquiv (a, b)) 0 := by
          rw [Fintype.sum_prod_type]
    _ = (phaseState m theta ⊗ ψ) (finProdFinEquiv (k, i)) 0 := by
          have hki := congrFun (congrFun (hpow k) i) 0
          simp [Matrix.mul, _root_.Matrix.mul_apply] at hki
          have hcol0 : (finProdFinEquiv.symm (0 : Fin (1 * 1))).1 = (0 : Fin 1) :=
            Subsingleton.elim _ _
          have hcol1 : (finProdFinEquiv.symm (0 : Fin (1 * 1))).2 = (0 : Fin 1) :=
            Subsingleton.elim _ _
          simp [controlledPowerMatrix, Matrix.kron, hcol0, hcol1]
          calc
            ∑ x, (U ^ ↑k) i x * ((((M m : ℝ).sqrt : ℂ)⁻¹) * ψ x 0)
                = (((M m : ℝ).sqrt : ℂ)⁻¹) * (∑ x, (U ^ ↑k) i x * ψ x 0) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro x hx
                  ring_nf
            _ = (((M m : ℝ).sqrt : ℂ)⁻¹) *
                ((Real.fourierChar (↑↑k * theta) : ℂ) * ψ i 0) := by
                  rw [hki]
            _ = (((M m : ℝ).sqrt : ℂ)⁻¹) * (Real.fourierChar (↑↑k * theta) : ℂ) * ψ i 0 := by
                  ring_nf
            _ = phaseState m theta k 0 * ψ i 0 := by
                  simp [phaseState]

/-- Controlled powers produce the arbitrary real phase state from the one-step
eigenphase equation. -/
theorem controlledPowerMatrix_mul_uniform_of_real_eigenphase {n : ℕ} {m : ℕ}
    {U : Square n} {ψ : Vector n} {theta : ℝ}
    (heigen : U ⬝ ψ = ((Real.fourierChar theta : ℂ)) • ψ) :
    controlledPowerMatrix m U ⬝ (uniformState m ⊗ ψ) = phaseState m theta ⊗ ψ := by
  exact controlledPowerMatrix_mul_uniform_of_real_power_action (fun k => by
    have hpow := matrix_power_eigenvector heigen (k : ℕ)
    have hphase : (Real.fourierChar ((k : ℕ) * theta) : ℂ) =
        (Real.fourierChar theta : ℂ) ^ (k : ℕ) := by
      rw [← nsmul_eq_mul]
      norm_cast
      exact AddChar.map_nsmul_eq_pow Real.fourierChar (k : ℕ) theta
    rw [← hphase] at hpow
    simpa using hpow)

/-- Complex conjugation reverses the sign of the real phase. -/
theorem star_phase (x : ℝ) : star ((Real.fourierChar x : ℂ)) = (Real.fourierChar (-x) : ℂ) := by
  exact Circle.star_addChar x

/-- The arbitrary-phase QPE phase state is normalized. -/
theorem phaseState_isNormalized (m : ℕ) (theta : ℝ) :
    Vector.IsNormalized (phaseState m theta) := by
  rw [Vector.IsNormalized]
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply]
  simp_rw [← star_phase]
  have hMpos : 0 < (M m : ℝ) := by exact_mod_cast (Nat.two_pow_pos m)
  have hterm : ∀ k : Fin (M m),
      (((M m : ℝ).sqrt : ℂ)⁻¹) * star ((Real.fourierChar ((k : ℕ) * theta) : ℂ)) *
        ((((M m : ℝ).sqrt : ℂ)⁻¹) * (Real.fourierChar ((k : ℕ) * theta) : ℂ)) =
        ((M m : ℂ)⁻¹) := by
    intro k
    rw [star_phase]
    have hphase : (Real.fourierChar (-(↑k * theta)) : ℂ) * (Real.fourierChar (↑k * theta) : ℂ) = 1 := by
      rw [← (show (Real.fourierChar (-(↑k * theta) + ↑k * theta) : ℂ) =
          (Real.fourierChar (-(↑k * theta)) : ℂ) * (Real.fourierChar (↑k * theta) : ℂ) by
        norm_cast
        exact AddChar.map_add_eq_mul Real.fourierChar (-(↑k * theta)) (↑k * theta))]
      simp
    have hsq : (((M m : ℝ).sqrt : ℂ) * ((M m : ℝ).sqrt : ℂ)) = (M m : ℂ) := by
      rw [← Complex.ofReal_mul, ← sq, Real.sq_sqrt hMpos.le]
      norm_num
    calc
      (((↑√↑(M m))⁻¹ : ℂ) * (Real.fourierChar (-(↑k * theta)) : ℂ)) *
          (((↑√↑(M m))⁻¹ : ℂ) * (Real.fourierChar (↑k * theta) : ℂ))
          = ((↑√↑(M m))⁻¹ : ℂ) * ((↑√↑(M m))⁻¹ : ℂ) *
              ((Real.fourierChar (-(↑k * theta)) : ℂ) * (Real.fourierChar (↑k * theta) : ℂ)) := by ring_nf
      _ = ((↑√↑(M m))⁻¹ : ℂ) * ((↑√↑(M m))⁻¹ : ℂ) := by
            rw [hphase, mul_one]
      _ = ((M m : ℂ)⁻¹) := by
            rw [← mul_inv_rev, hsq]
  calc
    (∑ x : Fin (M m),
        (((M m : ℝ).sqrt : ℂ)⁻¹) * star ((Real.fourierChar ((x : ℕ) * theta) : ℂ)) *
          ((((M m : ℝ).sqrt : ℂ)⁻¹) * (Real.fourierChar ((x : ℕ) * theta) : ℂ)))
        = ∑ _x : Fin (M m), ((M m : ℂ)⁻¹) := by
          apply Finset.sum_congr rfl
          intro x _hx
          exact hterm x
    _ = 1 := by
          simp [show (M m : ℂ) ≠ 0 by exact_mod_cast (NeZero.ne (M m))]

/-- The concrete inverse QFT matrix is the adjoint of the concrete QFT matrix. -/
theorem inverseQFTMatrix_eq_adjoint_qftMatrix (m : ℕ) :
    inverseQFTMatrix m = (qftMatrix m)† := by
  ext row col
  simp [Matrix.adjoint, qftMatrix, inverseQFTMatrix]
  left
  congr 1
  ring_nf

/-- Multiplying two phases after conjugating the first subtracts the angles. -/
theorem star_phase_mul (a b : ℝ) : star ((Real.fourierChar a : ℂ)) * (Real.fourierChar b : ℂ) = (Real.fourierChar (b - a) : ℂ) := by
  rw [star_phase]
  rw [show b - a = -a + b by ring_nf]
  norm_cast
  exact (AddChar.map_add_eq_mul Real.fourierChar (-a) b).symm

/-- Orthogonality of QFT phase columns before applying the normalization factor. -/
theorem qft_phase_orthogonality (m : ℕ) (r c : Fin (M m)) :
    (∑ k : Fin (M m),
      star ((Real.fourierChar (((k : ℕ) * (r : ℕ) : ℝ) / (M m : ℝ)) : ℂ)) *
        (Real.fourierChar (((k : ℕ) * (c : ℕ) : ℝ) / (M m : ℝ)) : ℂ)) =
      if r = c then (M m : ℂ) else 0 := by
  by_cases hEq : r = c
  · subst hEq
    simp
    simp_rw [← star_phase]
    calc
      (∑ k : Fin (M m),
        star ((Real.fourierChar (((k : ℕ) * (r : ℕ) : ℝ) / (M m : ℝ)) : ℂ)) *
          (Real.fourierChar (((k : ℕ) * (r : ℕ) : ℝ) / (M m : ℝ)) : ℂ))
          = ∑ _k : Fin (M m), (1 : ℂ) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [star_phase_mul]
            simp
      _ = (M m : ℂ) := by simp
  · by_cases hle : (r : ℕ) ≤ (c : ℕ)
    · simp [hEq]
      simp_rw [← star_phase]
      let d : Fin (M m) := ⟨(c : ℕ) - (r : ℕ), Nat.lt_of_le_of_lt (Nat.sub_le _ _) c.isLt⟩
      have hd : d ≠ 0 := by
        intro hd0
        apply hEq
        apply Fin.ext
        have hval : (c : ℕ) - (r : ℕ) = 0 := by
          simpa [d] using congrArg Fin.val hd0
        exact Nat.le_antisymm hle (Nat.le_of_sub_eq_zero hval)
      calc
        (∑ k : Fin (M m),
          star ((Real.fourierChar (((k : ℕ) * (r : ℕ) : ℝ) / (M m : ℝ)) : ℂ)) *
            (Real.fourierChar (((k : ℕ) * (c : ℕ) : ℝ) / (M m : ℝ)) : ℂ))
          = ∑ k : Fin (M m), (Real.fourierChar (((k : ℕ) * (d : ℕ) : ℝ) / (M m : ℝ)) : ℂ) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [star_phase_mul]
            dsimp [d]
            congr 1
            have hsub : ((c : ℝ) - (r : ℝ)) = (((c : ℕ) - (r : ℕ) : ℕ) : ℝ) := by
              exact (Nat.cast_sub hle).symm
            rw [← hsub]
            ring_nf
        _ = 0 := phase_root_sum_fin_eq_zero m d hd
    · simp [hEq]
      simp_rw [← star_phase]
      have hlt : (c : ℕ) < (r : ℕ) := lt_of_not_ge hle
      let d : Fin (M m) := ⟨(r : ℕ) - (c : ℕ), Nat.lt_of_le_of_lt (Nat.sub_le _ _) r.isLt⟩
      have hd : d ≠ 0 := by
        intro hd0
        have hval : (r : ℕ) - (c : ℕ) = 0 := by
          simpa [d] using congrArg Fin.val hd0
        have : (r : ℕ) ≤ (c : ℕ) := Nat.le_of_sub_eq_zero hval
        exact (not_le_of_gt hlt) this
      have hsum := phase_root_sum_fin_eq_zero m d hd
      have hsumStar : (∑ k : Fin (M m), star ((Real.fourierChar (((k : ℕ) * (d : ℕ) : ℝ) / (M m : ℝ)) : ℂ))) = 0 := by
        have h := congrArg (fun z : ℂ => star z) hsum
        simpa [map_sum] using h
      calc
        (∑ k : Fin (M m),
          star ((Real.fourierChar (((k : ℕ) * (r : ℕ) : ℝ) / (M m : ℝ)) : ℂ)) *
            (Real.fourierChar (((k : ℕ) * (c : ℕ) : ℝ) / (M m : ℝ)) : ℂ))
          = ∑ k : Fin (M m), star ((Real.fourierChar (((k : ℕ) * (d : ℕ) : ℝ) / (M m : ℝ)) : ℂ)) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [star_phase_mul, star_phase]
            dsimp [d]
            congr 1
            have hle' : (c : ℕ) ≤ (r : ℕ) := le_of_lt hlt
            have hsub : ((r : ℝ) - (c : ℝ)) = (((r : ℕ) - (c : ℕ) : ℕ) : ℝ) := by
              exact (Nat.cast_sub hle').symm
            rw [← hsub]
            ring_nf
        _ = 0 := hsumStar

/-- The product of the two QFT normalization factors is `1 / M`. -/
theorem qft_normalization_factor (m : ℕ) :
    ((((M m : ℝ).sqrt : ℂ)⁻¹) * (((M m : ℝ).sqrt : ℂ)⁻¹)) = ((M m : ℂ)⁻¹) := by
  have hpos : 0 < (M m : ℝ) := by exact_mod_cast Nat.two_pow_pos m
  have hsq : (((M m : ℝ).sqrt : ℂ) * ((M m : ℝ).sqrt : ℂ)) = (M m : ℂ) := by
    rw [← Complex.ofReal_mul]
    rw [← sq]
    rw [Real.sq_sqrt hpos.le]
    norm_num
  rw [← mul_inv_rev]
  rw [hsq]

/-- The mixed normalization factor appearing in approximate-QPE amplitudes. -/
theorem qpeApprox_normalization_factor (m : ℕ) :
    (((M m : ℝ)⁻¹.sqrt : ℂ) * (((M m : ℝ).sqrt : ℂ)⁻¹)) = ((M m : ℂ)⁻¹) := by
  rw [Real.sqrt_inv]
  simpa using qft_normalization_factor m

/-- The approximate-QPE amplitude as a normalized finite phase sum. -/
theorem qpeApproxAmplitude_eq_normalized_phase_sum
    (m : ℕ) (theta : ℝ) (y : Fin (M m)) :
    qpeApproxAmplitude m theta y =
      ((M m : ℂ)⁻¹) *
        (∑ k : Fin (M m),
          (Real.fourierChar ((k : ℕ) * (theta - (((y : ℕ) : ℝ) / (M m : ℝ)))) : ℂ)) := by
  unfold qpeApproxAmplitude
  simp [Matrix.mul, _root_.Matrix.mul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    ((↑√↑(M m))⁻¹ * (Real.fourierChar (-(↑↑y * ↑↑k / ↑(M m))) : ℂ) *
        ((↑√↑(M m))⁻¹ * (Real.fourierChar (↑↑k * theta) : ℂ)))
        = (((M m : ℝ)⁻¹.sqrt : ℂ) * (((M m : ℝ).sqrt : ℂ)⁻¹)) *
            ((Real.fourierChar (-(↑↑y * ↑↑k / ↑(M m))) : ℂ) * (Real.fourierChar (↑↑k * theta) : ℂ)) := by
          rw [Real.sqrt_inv]
          norm_num
          ring_nf
    _ = ((M m : ℂ)⁻¹) *
          ((Real.fourierChar (-(↑↑y * ↑↑k / ↑(M m))) : ℂ) * (Real.fourierChar (↑↑k * theta) : ℂ)) := by
          rw [qpeApprox_normalization_factor]
    _ = ((M m : ℂ)⁻¹) *
          (Real.fourierChar ((k : ℕ) * (theta - (((y : ℕ) : ℝ) / (M m : ℝ)))) : ℂ) := by
          congr 1
          rw [← (show (Real.fourierChar (-((((y : ℕ) : ℝ) * ((k : ℕ) : ℝ)) / (M m : ℝ)) + ((k : ℕ) : ℝ) * theta) : ℂ) =
              ((Real.fourierChar (-((((y : ℕ) : ℝ) * ((k : ℕ) : ℝ)) / (M m : ℝ))) : ℂ)) *
                (Real.fourierChar (((k : ℕ) : ℝ) * theta) : ℂ) by
            exact congrArg (fun z : Circle => (z : ℂ))
              (AddChar.map_add_eq_mul Real.fourierChar
                (-((((y : ℕ) : ℝ) * ((k : ℕ) : ℝ)) / (M m : ℝ))) (((k : ℕ) : ℝ) * theta)))]
          congr 1
          field_simp [show (M m : ℝ) ≠ 0 by exact_mod_cast (NeZero.ne (M m))]
          ring_nf

/-- Finite geometric-sum identity for the arbitrary phase state. -/
theorem phase_fin_sum_mul_sub (N : ℕ) (delta : ℝ) :
    (∑ k : Fin N, (Real.fourierChar ((k : ℕ) * delta) : ℂ)) * ((Real.fourierChar delta : ℂ) - 1) =
      (Real.fourierChar (N * delta) : ℂ) - 1 := by
  change (∑ k : Fin N, (fun i : ℕ => (Real.fourierChar (i * delta) : ℂ)) k) * ((Real.fourierChar delta : ℂ) - 1) =
      (Real.fourierChar (N * delta) : ℂ) - 1
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (Real.fourierChar (i * delta) : ℂ)) N]
  simp_rw [show ∀ i : ℕ, (Real.fourierChar (i * delta) : ℂ) =
      (Real.fourierChar delta : ℂ) ^ i by
    intro i
    rw [← nsmul_eq_mul]
    norm_cast
    exact AddChar.map_nsmul_eq_pow Real.fourierChar i delta]
  rw [geom_sum_mul]

/-- Squared norm of the finite phase sum in sine-ratio form. -/
theorem phase_fin_sum_normSq {N : ℕ} {delta : ℝ}
    (hden : Real.sin (Real.pi * delta) ≠ 0) :
    Complex.normSq (∑ k : Fin N, (Real.fourierChar ((k : ℕ) * delta) : ℂ)) =
      (Real.sin (Real.pi * (N : ℝ) * delta) ^ 2) /
        (Real.sin (Real.pi * delta) ^ 2) := by
  let S : ℂ := ∑ k : Fin N, (Real.fourierChar ((k : ℕ) * delta) : ℂ)
  have hmul := congrArg Complex.normSq (phase_fin_sum_mul_sub N delta)
  change Complex.normSq (S * ((Real.fourierChar delta : ℂ) - 1)) =
    Complex.normSq ((Real.fourierChar (N * delta) : ℂ) - 1) at hmul
  rw [Complex.normSq_mul] at hmul
  rw [phase_sub_one_normSq, phase_sub_one_normSq] at hmul
  have hden_sq_ne : 4 * Real.sin (Real.pi * delta) ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hden]
  have hsinarg : Real.sin (Real.pi * ((N : ℝ) * delta)) =
      Real.sin (Real.pi * (N : ℝ) * delta) := by
    congr 1
    ring_nf
  rw [hsinarg] at hmul
  field_simp [hden_sq_ne] at hmul ⊢
  simpa [S, mul_comm, mul_left_comm, mul_assoc] using hmul

/-- The normalized QFT matrix has orthonormal columns. -/
theorem qftMatrix_adjoint_mul_self (m : ℕ) : (qftMatrix m)† ⬝ qftMatrix m = I (M m) := by
  ext r c
  simp [Matrix.mul, Matrix.adjoint, qftMatrix, _root_.Matrix.mul_apply]
  simp_rw [← star_phase]
  calc
    (∑ x : Fin (M m),
        (((M m : ℝ).sqrt : ℂ)⁻¹) * star ((Real.fourierChar (((x : ℕ) * (r : ℕ) : ℝ) / (M m : ℝ)) : ℂ)) *
          ((((M m : ℝ).sqrt : ℂ)⁻¹) * (Real.fourierChar (((x : ℕ) * (c : ℕ) : ℝ) / (M m : ℝ)) : ℂ)))
        = ((((M m : ℝ).sqrt : ℂ)⁻¹) * (((M m : ℝ).sqrt : ℂ)⁻¹)) *
            (∑ x : Fin (M m),
              star ((Real.fourierChar (((x : ℕ) * (r : ℕ) : ℝ) / (M m : ℝ)) : ℂ)) *
                (Real.fourierChar (((x : ℕ) * (c : ℕ) : ℝ) / (M m : ℝ)) : ℂ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          ring_nf
    _ = (1 : Square (M m)) r c := by
          rw [qft_phase_orthogonality]
          by_cases hEq : r = c
          · subst hEq
            simp [qft_normalization_factor]
          · simp [hEq]

/-- The concrete QFT matrix is unitary. -/
theorem qftMatrix_isUnitary (m : ℕ) : Matrix.isUnitary (qftMatrix m) := by
  rw [Matrix.isUnitary_iff_adjoint_mul_self]
  exact qftMatrix_adjoint_mul_self m
/-- Matrix-level correctness facts for the concrete inverse QFT matrix. -/
structure InverseQFTMatrixCorrect (m : ℕ) where
  isUnitary : Matrix.isUnitary (inverseQFTMatrix m)
  maps_fourierState : ∀ y : Fin (M m), inverseQFTMatrix m ⬝ fourierState m y = Vector.basis y


/-- If the concrete QFT matrix is unitary, then the concrete inverse-QFT matrix
satisfies the exact inverse-QFT contract required by QPE. -/
def inverseQFTMatrixCorrectOfQFTUnitary {m : ℕ}
    (hunitary : Matrix.isUnitary (qftMatrix m)) : InverseQFTMatrixCorrect m where
  isUnitary := by
    rw [inverseQFTMatrix_eq_adjoint_qftMatrix]
    rw [Matrix.isUnitary_iff_adjoint_mul_self]
    rw [Matrix.adjoint_adjoint]
    exact (Matrix.isUnitary_iff_mul_adjoint_self (qftMatrix m)).mp hunitary
  maps_fourierState := by
    intro y
    rw [← qftMatrix_mul_basisState]
    rw [inverseQFTMatrix_eq_adjoint_qftMatrix]
    calc
      (qftMatrix m)† ⬝ (qftMatrix m ⬝ Vector.basis y) =
          ((qftMatrix m)† ⬝ qftMatrix m) ⬝ Vector.basis y := by
        change (Matrix.adjoint (qftMatrix m) * (qftMatrix m * Vector.basis y)) =
          ((Matrix.adjoint (qftMatrix m) * qftMatrix m) * Vector.basis y)
        rw [_root_.Matrix.mul_assoc]
      _ = Vector.basis y := by
        have hmul := (Matrix.isUnitary_iff_adjoint_mul_self (qftMatrix m)).mp hunitary
        rw [hmul]
        simp [Matrix.mul]

/-- Approximate-QPE outcome probabilities form a probability distribution. -/
theorem qpeApproxOutcomeProbability_total (m : ℕ) (theta : ℝ) :
    (∑ y : Fin (M m), qpeApproxOutcomeProbability m theta y) = 1 := by
  let s : Vector (M m) := inverseQFTMatrix m ⬝ phaseState m theta
  change (∑ y : Fin (M m), Measurement.prob s y) = 1
  have hs : Vector.IsNormalized s := by
    dsimp [s]
    exact Matrix.isUnitary_mul_isNormalized
      (inverseQFTMatrixCorrectOfQFTUnitary (qftMatrix_isUnitary m)).isUnitary
      (phaseState_isNormalized m theta)
  exact Measurement.sum_prob_of_isNormalized hs

/-- Circular success and circular failure probabilities partition total probability. -/
theorem qpeCircularPhaseWindowProbability_add_failure_eq_one
    (m k : ℕ) (theta : ℝ) :
    qpeCircularPhaseWindowProbability m k theta +
      qpeCircularPhaseWindowFailureProbability m k theta = 1 := by
  classical
  unfold qpeCircularPhaseWindowProbability qpeCircularPhaseWindowFailureProbability
  unfold qpeCircularPhaseWindowOutcomes qpeCircularPhaseWindowFailureOutcomes
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := qpeCircularPhaseWindow m k theta)
    (f := fun y : Fin (M m) => qpeApproxOutcomeProbability m theta y)
  rw [hsplit]
  exact qpeApproxOutcomeProbability_total m theta

/-- Success probability is one minus circular failure probability. -/
theorem qpeCircularPhaseWindowProbability_eq_one_sub_failure
    (m k : ℕ) (theta : ℝ) :
    qpeCircularPhaseWindowProbability m k theta =
      1 - qpeCircularPhaseWindowFailureProbability m k theta := by
  have h := qpeCircularPhaseWindowProbability_add_failure_eq_one m k theta
  linarith

/-- Failure probability is one minus circular success probability. -/
theorem qpeCircularPhaseWindowFailureProbability_eq_one_sub_success
    (m k : ℕ) (theta : ℝ) :
    qpeCircularPhaseWindowFailureProbability m k theta =
      1 - qpeCircularPhaseWindowProbability m k theta := by
  have h := qpeCircularPhaseWindowProbability_add_failure_eq_one m k theta
  linarith


/-- Specification for an inverse QFT on `m` qubits.  This is the exact property
needed by QPE. -/
structure InverseQFTSpec (m : ℕ) where
  matrix : Square (M m)
  isUnitary : Matrix.isUnitary matrix
  maps_fourierState : ∀ y : Fin (M m), matrix ⬝ fourierState m y = Vector.basis y

/-- Turn correctness facts for the concrete inverse QFT matrix into the abstract
QPE inverse-QFT contract. -/
def inverseQFTSpecOfMatrixCorrect {m : ℕ} (h : InverseQFTMatrixCorrect m) : InverseQFTSpec m where
  matrix := inverseQFTMatrix m
  isUnitary := h.isUnitary
  maps_fourierState := h.maps_fourierState

/-- Specification for the controlled-power stage of QPE for a fixed eigenvector.
It says that the stage maps the prepared uniform counting register to the Fourier
basis state while leaving the target eigenvector untouched. -/
structure ControlledPowersSpec {n : ℕ} (m : ℕ) (U : Square n) (ψ : Vector n)
    (y : Fin (M m)) where
  matrix : Square (M m * n)
  isUnitary : Matrix.isUnitary matrix
  eigenvector_normalized : Vector.IsNormalized ψ
  eigenphase : U ⬝ ψ = ((Real.fourierChar ((y : ℕ) / (M m : ℝ)) : ℂ)) • ψ
  maps_uniform_state : matrix ⬝ (uniformState m ⊗ ψ) = fourierState m y ⊗ ψ

/-- Build the abstract controlled-power QPE contract from the concrete matrix. -/
def controlledPowersSpecOfEigenphase {n : ℕ} {m : ℕ} {U : Square n}
    {ψ : Vector n} {y : Fin (M m)}
    (hU : Matrix.isUnitary U)
    (hnorm : Vector.IsNormalized ψ)
    (heigen : U ⬝ ψ = ((Real.fourierChar ((y : ℕ) / (M m : ℝ)) : ℂ)) • ψ) :
    ControlledPowersSpec m U ψ y where
  matrix := controlledPowerMatrix m U
  isUnitary := controlledPowerMatrix_isUnitary m hU
  eigenvector_normalized := hnorm
  eigenphase := heigen
  maps_uniform_state := controlledPowerMatrix_mul_uniform_of_eigenphase heigen

/-- Semantic QPE output for an exact phase: controlled powers followed by the
inverse QFT on the counting register. -/
def exactQPEState {n : ℕ} {m : ℕ} {U : Square n} {ψ : Vector n} {y : Fin (M m)}
    (ctrl : ControlledPowersSpec m U ψ y) (iqft : InverseQFTSpec m) : Vector (M m * n) :=
  (iqft.matrix ⊗ (I n)) ⬝ (ctrl.matrix ⬝ (uniformState m ⊗ ψ))

/-- Exact QPE output state: the counting register is `|y⟩` and the target remains
`ψ`. -/
theorem exactQPEState_eq_basis_tensor_eigenstate {n : ℕ} {m : ℕ} {U : Square n}
    {ψ : Vector n} {y : Fin (M m)}
    (ctrl : ControlledPowersSpec m U ψ y) (iqft : InverseQFTSpec m) :
    exactQPEState ctrl iqft = Vector.basis y ⊗ ψ := by
  unfold exactQPEState
  rw [ctrl.maps_uniform_state]
  rw [Matrix.kron_mul]
  rw [iqft.maps_fourierState]
  simp [Matrix.mul]

/-- Exact QPE correctness for a chosen target basis index.  If the target
post-QPE eigenstate has probability one at `j`, the joint measurement returns
`(y,j)` with probability one. -/
theorem exactQPE_success_probability_one_of_target_basis {n : ℕ} {m : ℕ} {U : Square n}
    {ψ : Vector n} {y : Fin (M m)} {j : Fin n}
    (ctrl : ControlledPowersSpec m U ψ y) (iqft : InverseQFTSpec m)
    (hψj : Measurement.prob ψ j = 1) :
    Measurement.prob (exactQPEState ctrl iqft) (finProdFinEquiv (y, j)) = 1 := by
  rw [exactQPEState_eq_basis_tensor_eigenstate ctrl iqft]
  rw [Measurement.prob_kron_apply]
  simp [hψj]

/-- Exact QPE keeps the target-state distribution while fixing the counting
register at the exact phase index. -/
theorem exactQPE_joint_probability {n : ℕ} {m : ℕ} {U : Square n}
    {ψ : Vector n} {y : Fin (M m)} (j : Fin n)
    (ctrl : ControlledPowersSpec m U ψ y) (iqft : InverseQFTSpec m) :
    Measurement.prob (exactQPEState ctrl iqft) (finProdFinEquiv (y, j)) =
      Measurement.prob ψ j := by
  rw [exactQPEState_eq_basis_tensor_eigenstate ctrl iqft]
  rw [Measurement.prob_kron_apply]
  simp

/-- Concrete exact-QPE state correctness: the counting register is exactly `|y⟩`. -/
theorem exactQPEStateConcrete_eq_basis_tensor_eigenstate {n : ℕ} {m : ℕ} {U : Square n}
    {ψ : Vector n} {y : Fin (M m)}
    (hU : Matrix.isUnitary U)
    (hnorm : Vector.IsNormalized ψ)
    (heigen : U ⬝ ψ = ((Real.fourierChar ((y : ℕ) / (M m : ℝ)) : ℂ)) • ψ) :
    exactQPEState (controlledPowersSpecOfEigenphase hU hnorm heigen) (inverseQFTSpecOfMatrixCorrect (inverseQFTMatrixCorrectOfQFTUnitary (qftMatrix_isUnitary m))) = Vector.basis y ⊗ ψ := by
  exact exactQPEState_eq_basis_tensor_eigenstate
    (controlledPowersSpecOfEigenphase hU hnorm heigen) (inverseQFTSpecOfMatrixCorrect (inverseQFTMatrixCorrectOfQFTUnitary (qftMatrix_isUnitary m)))

/-- Concrete exact-QPE measurement correctness for any target basis index. -/
theorem exactQPEConcrete_joint_probability {n : ℕ} {m : ℕ} {U : Square n}
    {ψ : Vector n} {y : Fin (M m)} (j : Fin n)
    (hU : Matrix.isUnitary U)
    (hnorm : Vector.IsNormalized ψ)
    (heigen : U ⬝ ψ = ((Real.fourierChar ((y : ℕ) / (M m : ℝ)) : ℂ)) • ψ) :
    Measurement.prob (exactQPEState (controlledPowersSpecOfEigenphase hU hnorm heigen) (inverseQFTSpecOfMatrixCorrect (inverseQFTMatrixCorrectOfQFTUnitary (qftMatrix_isUnitary m)))) (finProdFinEquiv (y, j)) =
      Measurement.prob ψ j := by
  exact exactQPE_joint_probability j
    (controlledPowersSpecOfEigenphase hU hnorm heigen) (inverseQFTSpecOfMatrixCorrect (inverseQFTMatrixCorrectOfQFTUnitary (qftMatrix_isUnitary m)))

/-- Concrete exact-QPE success probability when the target state is deterministic
at basis index `j`. -/
theorem exactQPEConcrete_success_probability_one_of_target_basis {n : ℕ} {m : ℕ}
    {U : Square n} {ψ : Vector n} {y : Fin (M m)} {j : Fin n}
    (hU : Matrix.isUnitary U)
    (hnorm : Vector.IsNormalized ψ)
    (heigen : U ⬝ ψ = ((Real.fourierChar ((y : ℕ) / (M m : ℝ)) : ℂ)) • ψ)
    (hψj : Measurement.prob ψ j = 1) :
    Measurement.prob (exactQPEState (controlledPowersSpecOfEigenphase hU hnorm heigen) (inverseQFTSpecOfMatrixCorrect (inverseQFTMatrixCorrectOfQFTUnitary (qftMatrix_isUnitary m)))) (finProdFinEquiv (y, j)) = 1 := by
  rw [exactQPEConcrete_joint_probability j hU hnorm heigen]
  exact hψj

/-- Under the nearest-grid hypothesis, a nonzero phase error cannot make the
sine denominator in the geometric-probability formula vanish. -/
theorem sin_pi_delta_ne_zero_of_nearest {N : ℕ} {delta : ℝ}
    (hN : 0 < N) (hdelta : delta ≠ 0)
    (hclose : |delta| ≤ 1 / (2 * (N : ℝ))) :
    Real.sin (Real.pi * delta) ≠ 0 := by
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hdelta_le_half : |delta| ≤ (1 : ℝ) / 2 := by
    calc
      |delta| ≤ 1 / (2 * (N : ℝ)) := hclose
      _ ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) * (N : ℝ))
          (by norm_num : (0 : ℝ) < 2)]
        nlinarith
  have harg_abs_lt_pi : |Real.pi * delta| < Real.pi := by
    calc
      |Real.pi * delta| = Real.pi * |delta| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
      _ ≤ Real.pi * (1 / 2) := by gcongr
      _ < Real.pi := by nlinarith [Real.pi_pos]
  have harg_ne_zero : Real.pi * delta ≠ 0 := mul_ne_zero Real.pi_ne_zero hdelta
  have hz := (Real.sin_eq_zero_iff_of_lt_of_lt (x := Real.pi * delta)
    (by have := abs_lt.mp harg_abs_lt_pi; exact this.1)
    (by have := abs_lt.mp harg_abs_lt_pi; exact this.2)).mp
  intro hs
  exact harg_ne_zero (hz hs)

/-- The matrix-level approximate-QPE probability equals the standard sine-ratio
geometric probability for any outcome whose sine denominator is nonzero. -/
theorem qpeApproxOutcomeProbability_eq_geometric_of_sin_ne_zero
    (m : ℕ) (theta : ℝ) (y : Fin (M m))
    (hden : Real.sin (Real.pi * (theta - (((y : ℕ) : ℝ) / (M m : ℝ)))) ≠ 0) :
    qpeApproxOutcomeProbability m theta y =
      qpeApproxGeometricProbability (M m)
        (theta - (((y : ℕ) : ℝ) / (M m : ℝ))) := by
  let delta := theta - (((y : ℕ) : ℝ) / (M m : ℝ))
  have hden_delta : Real.sin (Real.pi * delta) ≠ 0 := by
    simpa [delta] using hden
  have hdelta : delta ≠ 0 := by
    intro hzero
    apply hden_delta
    simp [hzero]
  have hdelta_orig : theta - (((y : ℕ) : ℝ) / (M m : ℝ)) ≠ 0 := by
    simpa [delta] using hdelta
  unfold qpeApproxOutcomeProbability qpeApproxGeometricProbability
  simp [hdelta_orig]
  rw [qpeApproxAmplitude_eq_normalized_phase_sum]
  rw [Complex.normSq_mul]
  rw [phase_fin_sum_normSq (N := M m)
    (delta := theta - (((y : ℕ) : ℝ) / (M m : ℝ))) hden]
  simp [Complex.normSq_natCast]
  field_simp [show (M m : ℝ) ≠ 0 by exact_mod_cast (NeZero.ne (M m)), hden]

/-- The matrix-level approximate-QPE probability equals the standard sine-ratio
geometric probability for a nearest-grid outcome. -/
theorem qpeApproxOutcomeProbability_eq_geometric_of_nearest
    (m : ℕ) (theta : ℝ) (y : Fin (M m))
    (hclose : |theta - (((y : ℕ) : ℝ) / (M m : ℝ))| ≤ 1 / (2 * (M m : ℝ))) :
    qpeApproxOutcomeProbability m theta y =
      qpeApproxGeometricProbability (M m)
        (theta - (((y : ℕ) : ℝ) / (M m : ℝ))) := by
  let delta := theta - (((y : ℕ) : ℝ) / (M m : ℝ))
  have hNpos : 0 < M m := Nat.two_pow_pos m
  have hNneC : (M m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne (M m))
  have hclose' : |delta| ≤ 1 / (2 * (M m : ℝ)) := by
    simpa [delta] using hclose
  unfold qpeApproxOutcomeProbability qpeApproxGeometricProbability
  by_cases hdelta : delta = 0
  · simp [delta] at hdelta
    simp [hdelta, qpeApproxAmplitude_eq_normalized_phase_sum, hNneC]
  · have hdelta_orig : theta - (((y : ℕ) : ℝ) / (M m : ℝ)) ≠ 0 := by
      simpa [delta] using hdelta
    have hden : Real.sin (Real.pi * delta) ≠ 0 :=
      sin_pi_delta_ne_zero_of_nearest hNpos hdelta hclose'
    have hden_orig :
        Real.sin (Real.pi * (theta - (((y : ℕ) : ℝ) / (M m : ℝ)))) ≠ 0 := by
      simpa [delta] using hden
    simp [hdelta_orig]
    rw [qpeApproxAmplitude_eq_normalized_phase_sum]
    rw [Complex.normSq_mul]
    rw [phase_fin_sum_normSq (N := M m)
      (delta := theta - (((y : ℕ) : ℝ) / (M m : ℝ))) hden_orig]
    simp [Complex.normSq_natCast]
    field_simp [show (M m : ℝ) ≠ 0 by exact_mod_cast (NeZero.ne (M m)), hden_orig]

/-- Pointwise upper bound for the closed-form approximate-QPE probability: the
numerator sine contributes at most one. -/
theorem qpeApproxGeometricProbability_upper_bound_sin_den {N : ℕ} {delta : ℝ}
    (hN : 0 < N) (hden : Real.sin (Real.pi * delta) ≠ 0) :
    qpeApproxGeometricProbability N delta ≤
      (Real.sin (Real.pi * delta) ^ 2)⁻¹ * ((N : ℝ) ^ 2)⁻¹ := by
  unfold qpeApproxGeometricProbability
  have hdelta : delta ≠ 0 := by
    intro hzero
    apply hden
    simp [hzero]
  simp [hdelta]
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hden_sq_pos : 0 < Real.sin (Real.pi * delta) ^ 2 := sq_pos_of_ne_zero hden
  have hnum_le : Real.sin (Real.pi * (N : ℝ) * delta) ^ 2 ≤ 1 := Real.sin_sq_le_one _
  calc
    (Real.sin (Real.pi * (N : ℝ) * delta) / ((N : ℝ) * Real.sin (Real.pi * delta))) ^ 2
        = Real.sin (Real.pi * (N : ℝ) * delta) ^ 2 /
            ((N : ℝ) ^ 2 * Real.sin (Real.pi * delta) ^ 2) := by
          field_simp [hNpos.ne', hden]
    _ ≤ (Real.sin (Real.pi * delta) ^ 2)⁻¹ * ((N : ℝ) ^ 2)⁻¹ := by
          rw [div_eq_mul_inv]
          rw [mul_inv_rev]
          have hright_nonneg : 0 ≤
              (Real.sin (Real.pi * delta) ^ 2)⁻¹ * ((N : ℝ) ^ 2)⁻¹ := by
            exact mul_nonneg (inv_nonneg.mpr hden_sq_pos.le)
              (inv_nonneg.mpr (sq_nonneg (N : ℝ)))
          simpa using mul_le_mul_of_nonneg_right hnum_le hright_nonneg

/-- Sine denominator lower bound from a scaled distance condition.

This is the trigonometric bridge used in the BHMT tail estimate after reducing
the phase error to the nearest representative in `[-1/2, 1/2]`. -/
theorem sin_pi_lower_of_scaled_distance_le_abs
    {N j : ℕ} {delta : ℝ}
    (hhalf : |delta| ≤ (1 : ℝ) / 2)
    (hdist : (j : ℝ) / (N : ℝ) ≤ |delta|) :
    2 * (j : ℝ) / (N : ℝ) ≤ |Real.sin (Real.pi * delta)| := by
  have harg_le : |Real.pi * delta| ≤ Real.pi / 2 := by
    calc
      |Real.pi * delta| = Real.pi * |delta| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
      _ ≤ Real.pi * ((1 : ℝ) / 2) := by gcongr
      _ = Real.pi / 2 := by ring_nf
  have hsin_lower := Real.mul_abs_le_abs_sin (x := Real.pi * delta) harg_le
  calc
    2 * (j : ℝ) / (N : ℝ) = 2 * ((j : ℝ) / (N : ℝ)) := by ring_nf
    _ ≤ 2 * |delta| := by gcongr
    _ = 2 / Real.pi * |Real.pi * delta| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp [Real.pi_ne_zero]
    _ ≤ |Real.sin (Real.pi * delta)| := hsin_lower


/-- Absolute sine is invariant under subtracting one full phase turn inside
`sin (π * ·)`. -/
theorem abs_sin_pi_mul_sub_one (delta : ℝ) :
    |Real.sin (Real.pi * (delta - 1))| = |Real.sin (Real.pi * delta)| := by
  have harg : Real.pi * (delta - 1) = Real.pi * delta - Real.pi := by ring_nf
  rw [harg, Real.sin_sub_pi, abs_neg]

/-- Absolute sine is invariant under adding one full phase turn inside
`sin (π * ·)`. -/
theorem abs_sin_pi_mul_add_one (delta : ℝ) :
    |Real.sin (Real.pi * (delta + 1))| = |Real.sin (Real.pi * delta)| := by
  have harg : Real.pi * (delta + 1) = Real.pi * delta + Real.pi := by ring_nf
  rw [harg, Real.sin_add_pi, abs_neg]

/-- A failed circular-window outcome has a wrapped phase-error representative to
which the sine-denominator lower bound applies. -/
theorem sin_pi_lower_of_qpeCircularFailure_representative
    (m k : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    {y : Fin (M m)}
    (hy : y ∈ qpeCircularPhaseWindowFailureOutcomes m k theta) :
    ∃ delta : ℝ,
      (delta = theta - (((y : ℕ) : ℝ) / (M m : ℝ)) ∨
        delta = theta - (((y : ℕ) : ℝ) / (M m : ℝ)) - 1 ∨
        delta = theta - (((y : ℕ) : ℝ) / (M m : ℝ)) + 1) ∧
      |delta| ≤ (1 : ℝ) / 2 ∧
      (k : ℝ) / (M m : ℝ) < |delta| ∧
      2 * (k : ℝ) / (M m : ℝ) ≤ |Real.sin (Real.pi * delta)| := by
  rcases qpeCircularFailure_phase_error_representative m k h0 h1 hy with
    ⟨delta, hdelta, hhalf, hdist⟩
  refine ⟨delta, hdelta, hhalf, hdist, ?_⟩
  exact sin_pi_lower_of_scaled_distance_le_abs
    (N := M m) (j := k) hhalf (le_of_lt hdist)

/-- The wrapped representative supplied by a circular-window failure gives the
same sine-denominator lower bound for the literal phase error, because
`|sin (πx)|` is one-periodic. -/
theorem sin_pi_lower_of_qpeCircularFailure_literal
    (m k : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    {y : Fin (M m)}
    (hy : y ∈ qpeCircularPhaseWindowFailureOutcomes m k theta) :
    2 * (k : ℝ) / (M m : ℝ) ≤
      |Real.sin (Real.pi * (theta - (((y : ℕ) : ℝ) / (M m : ℝ))))| := by
  rcases sin_pi_lower_of_qpeCircularFailure_representative m k h0 h1 hy with
    ⟨delta, hdelta, _hhalf, _hdist, hsin⟩
  rcases hdelta with hdelta | hdelta | hdelta
  · simpa [hdelta] using hsin
  · have hlit : theta - (((y : ℕ) : ℝ) / (M m : ℝ)) = delta + 1 := by
      linarith
    rw [hlit, abs_sin_pi_mul_add_one]
    exact hsin
  · have hlit : theta - (((y : ℕ) : ℝ) / (M m : ℝ)) = delta - 1 := by
      linarith
    rw [hlit, abs_sin_pi_mul_sub_one]
    exact hsin

/-- A circular-window failure with positive radius has nonzero approximate-QPE
sine denominator. -/
theorem sin_pi_ne_zero_of_qpeCircularFailure
    (m k : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    {y : Fin (M m)} (hk : 0 < k)
    (hy : y ∈ qpeCircularPhaseWindowFailureOutcomes m k theta) :
    Real.sin (Real.pi * (theta - (((y : ℕ) : ℝ) / (M m : ℝ)))) ≠ 0 := by
  have hsin := sin_pi_lower_of_qpeCircularFailure_literal m k h0 h1 hy
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hMpos : 0 < (M m : ℝ) := by exact_mod_cast (Nat.two_pow_pos m)
  have hleft_pos : 0 < 2 * (k : ℝ) / (M m : ℝ) := by positivity
  have hspos : 0 < |Real.sin (Real.pi * (theta - (((y : ℕ) : ℝ) / (M m : ℝ))))| :=
    lt_of_lt_of_le hleft_pos hsin
  exact abs_pos.mp hspos


/-- A failed outcome's real circular-distance bucket gives a sine-denominator
lower bound for a wrapped phase-error representative. -/
theorem sin_pi_lower_of_qpeCircularFailure_distanceBucket_representative
    (m k : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    {y : Fin (M m)}
    (hy : y ∈ qpeCircularPhaseWindowFailureOutcomes m k theta) :
    ∃ delta : ℝ,
      (delta = theta - (((y : ℕ) : ℝ) / (M m : ℝ)) ∨
        delta = theta - (((y : ℕ) : ℝ) / (M m : ℝ)) - 1 ∨
        delta = theta - (((y : ℕ) : ℝ) / (M m : ℝ)) + 1) ∧
      |delta| ≤ (1 : ℝ) / 2 ∧
      (qpeCircularDistanceBucket m theta y : ℝ) / (M m : ℝ) ≤ |delta| ∧
      2 * (qpeCircularDistanceBucket m theta y : ℝ) / (M m : ℝ) ≤
        |Real.sin (Real.pi * delta)| := by
  rcases qpeCircularFailure_phase_error_representative_with_unitDistance m k h0 h1 hy with
    ⟨delta, hdelta, hhalf, _hdist, hD⟩
  have hbucketD :
      (qpeCircularDistanceBucket m theta y : ℝ) / (M m : ℝ) ≤
        unitPhaseDistance theta (((y : ℕ) : ℝ) / (M m : ℝ)) := by
    have hMpos : 0 < (M m : ℝ) := by exact_mod_cast (Nat.two_pow_pos m)
    have hD_nonneg :
        0 ≤ unitPhaseDistance theta (((y : ℕ) : ℝ) / (M m : ℝ)) :=
      unitPhaseDistance_nonneg theta (((y : ℕ) : ℝ) / (M m : ℝ))
    have hx_nonneg :
        0 ≤ (M m : ℝ) * unitPhaseDistance theta (((y : ℕ) : ℝ) / (M m : ℝ)) := by
      positivity
    have hfloor :
        (qpeCircularDistanceBucket m theta y : ℝ) ≤
          (M m : ℝ) * unitPhaseDistance theta (((y : ℕ) : ℝ) / (M m : ℝ)) := by
      unfold qpeCircularDistanceBucket
      exact Nat.floor_le hx_nonneg
    rw [div_le_iff₀ hMpos]
    simpa [mul_comm] using hfloor
  have hbucket_abs :
      (qpeCircularDistanceBucket m theta y : ℝ) / (M m : ℝ) ≤ |delta| :=
    le_trans hbucketD hD
  refine ⟨delta, hdelta, hhalf, hbucket_abs, ?_⟩
  exact sin_pi_lower_of_scaled_distance_le_abs
    (N := M m) (j := qpeCircularDistanceBucket m theta y) hhalf hbucket_abs

/-- The real circular-distance bucket gives the sine-denominator lower bound for
the literal approximate-QPE phase error. -/
theorem sin_pi_lower_of_qpeCircularFailure_distanceBucket_literal
    (m k : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    {y : Fin (M m)}
    (hy : y ∈ qpeCircularPhaseWindowFailureOutcomes m k theta) :
    2 * (qpeCircularDistanceBucket m theta y : ℝ) / (M m : ℝ) ≤
      |Real.sin (Real.pi * (theta - (((y : ℕ) : ℝ) / (M m : ℝ))))| := by
  rcases sin_pi_lower_of_qpeCircularFailure_distanceBucket_representative m k h0 h1 hy with
    ⟨delta, hdelta, _hhalf, _hdist, hsin⟩
  rcases hdelta with hdelta | hdelta | hdelta
  · simpa [hdelta] using hsin
  · have hlit : theta - (((y : ℕ) : ℝ) / (M m : ℝ)) = delta + 1 := by
      linarith
    rw [hlit, abs_sin_pi_mul_add_one]
    exact hsin
  · have hlit : theta - (((y : ℕ) : ℝ) / (M m : ℝ)) = delta - 1 := by
      linarith
    rw [hlit, abs_sin_pi_mul_sub_one]
    exact hsin

/-- Positive distance bucket implies nonzero approximate-QPE sine denominator. -/
theorem sin_pi_ne_zero_of_qpeCircularFailure_distanceBucket
    (m k : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    {y : Fin (M m)}
    (hy : y ∈ qpeCircularPhaseWindowFailureOutcomes m k theta)
    (hbpos : 0 < qpeCircularDistanceBucket m theta y) :
    Real.sin (Real.pi * (theta - (((y : ℕ) : ℝ) / (M m : ℝ)))) ≠ 0 := by
  have hsin := sin_pi_lower_of_qpeCircularFailure_distanceBucket_literal m k h0 h1 hy
  have hbR : 0 < (qpeCircularDistanceBucket m theta y : ℝ) := by exact_mod_cast hbpos
  have hMpos : 0 < (M m : ℝ) := by exact_mod_cast (Nat.two_pow_pos m)
  have hleft_pos :
      0 < 2 * (qpeCircularDistanceBucket m theta y : ℝ) / (M m : ℝ) := by
    positivity
  have hspos : 0 < |Real.sin (Real.pi * (theta - (((y : ℕ) : ℝ) / (M m : ℝ))))| :=
    lt_of_lt_of_le hleft_pos hsin
  exact abs_pos.mp hspos

theorem qpeApproxGeometricProbability_upper_bound_of_sin_lower
    {N j : ℕ} {delta : ℝ}
    (hN : 0 < N) (hj : 0 < j)
    (hden : Real.sin (Real.pi * delta) ≠ 0)
    (hsin : 2 * (j : ℝ) / (N : ℝ) ≤ |Real.sin (Real.pi * delta)|) :
    qpeApproxGeometricProbability N delta ≤ 1 / (4 * (j : ℝ) ^ 2) := by
  have hgeom := qpeApproxGeometricProbability_upper_bound_sin_den (N := N) (delta := delta) hN hden
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast hj
  have hleft_nonneg : 0 ≤ 2 * (j : ℝ) / (N : ℝ) := by positivity
  have hsin_sq_lower : (2 * (j : ℝ) / (N : ℝ)) ^ 2 ≤ Real.sin (Real.pi * delta) ^ 2 := by
    have habs_left : |2 * (j : ℝ) / (N : ℝ)| ≤ |Real.sin (Real.pi * delta)| := by
      simpa [abs_of_nonneg hleft_nonneg] using hsin
    simpa [sq_abs] using (sq_le_sq.mpr habs_left)
  have hsin_sq_pos : 0 < Real.sin (Real.pi * delta) ^ 2 := sq_pos_of_ne_zero hden
  have htarget_pos : 0 < 4 * (j : ℝ) ^ 2 := by positivity
  have hbound :
      (Real.sin (Real.pi * delta) ^ 2)⁻¹ * ((N : ℝ) ^ 2)⁻¹ ≤
        1 / (4 * (j : ℝ) ^ 2) := by
    have hmul_lower : 4 * (j : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 * Real.sin (Real.pi * delta) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hsin_sq_lower (sq_nonneg (N : ℝ))
      calc
        4 * (j : ℝ) ^ 2 = (N : ℝ) ^ 2 * (2 * (j : ℝ) / (N : ℝ)) ^ 2 := by
          field_simp [hNpos.ne']
          ring_nf
        _ ≤ (N : ℝ) ^ 2 * Real.sin (Real.pi * delta) ^ 2 := hmul
    have hdenom_pos : 0 < (N : ℝ) ^ 2 * Real.sin (Real.pi * delta) ^ 2 := by positivity
    have hinv := (inv_le_inv₀ hdenom_pos htarget_pos).mpr hmul_lower
    have hleft_eq :
        (Real.sin (Real.pi * delta) ^ 2)⁻¹ * ((N : ℝ) ^ 2)⁻¹ =
          ((N : ℝ) ^ 2 * Real.sin (Real.pi * delta) ^ 2)⁻¹ := by
      rw [← mul_inv_rev]
    rw [hleft_eq]
    simpa [one_div] using hinv
  exact le_trans hgeom hbound

/-- Matrix-level inverse-square pointwise tail bound from a sine-denominator lower
bound. -/
theorem qpeApproxOutcomeProbability_upper_bound_of_sin_lower
    (m j : ℕ) (theta : ℝ) (y : Fin (M m))
    (hj : 0 < j)
    (hden : Real.sin (Real.pi * (theta - (((y : ℕ) : ℝ) / (M m : ℝ)))) ≠ 0)
    (hsin : 2 * (j : ℝ) / (M m : ℝ) ≤
      |Real.sin (Real.pi * (theta - (((y : ℕ) : ℝ) / (M m : ℝ))))|) :
    qpeApproxOutcomeProbability m theta y ≤ 1 / (4 * (j : ℝ) ^ 2) := by
  rw [qpeApproxOutcomeProbability_eq_geometric_of_sin_ne_zero m theta y hden]
  exact qpeApproxGeometricProbability_upper_bound_of_sin_lower
    (Nat.two_pow_pos m) hj hden hsin

/-- Pointwise BHMT inverse-square tail bound using the real circular-distance
bucket `j = floor(M * d(theta, y/M))`. -/
theorem qpeApproxOutcomeProbability_failure_upper_bound_distanceBucket
    (m k : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    {y : Fin (M m)} (hk : 1 < k)
    (hy : y ∈ qpeCircularPhaseWindowFailureOutcomes m k theta) :
    qpeApproxOutcomeProbability m theta y ≤
      1 / (4 * (qpeCircularDistanceBucket m theta y : ℝ) ^ 2) := by
  have hbmem := qpeCircularDistanceBucket_mem_tail_of_failure m k h0 h1 (by omega) hy
  have hbpos : 0 < qpeCircularDistanceBucket m theta y := by
    have hlt : k - 1 < qpeCircularDistanceBucket m theta y := (Finset.mem_Ioc.mp hbmem).1
    omega
  have hsin := sin_pi_lower_of_qpeCircularFailure_distanceBucket_literal m k h0 h1 hy
  have hden := sin_pi_ne_zero_of_qpeCircularFailure_distanceBucket m k h0 h1 hy hbpos
  exact qpeApproxOutcomeProbability_upper_bound_of_sin_lower
    m (qpeCircularDistanceBucket m theta y) theta y hbpos hden hsin



/-- An outcome in a fixed circular-distance bucket is one of the two residue
classes at that integer distance from `M * theta`: the class of
`floor(M*theta) - i` or the class of `ceil(M*theta) + i`. -/
theorem qpeCircularDistanceBucket_eq_imp_left_or_right_candidate
    (m i : ℕ) (theta : ℝ) {y : Fin (M m)}
    (hybucket : qpeCircularDistanceBucket m theta y = i) :
    y = ⟨((Int.floor ((M m : ℝ) * theta) - (i : ℤ) : ℤ) : ZMod (M m)).val, by
      exact ZMod.val_lt (((Int.floor ((M m : ℝ) * theta) - (i : ℤ) : ℤ) : ZMod (M m)))⟩ ∨
      y = ⟨((Int.ceil ((M m : ℝ) * theta) + (i : ℤ) : ℤ) : ZMod (M m)).val, by
        exact ZMod.val_lt (((Int.ceil ((M m : ℝ) * theta) + (i : ℤ) : ℤ) : ZMod (M m)))⟩ := by
  let N := M m
  let grid : ℝ := ((y : ℕ) : ℝ) / (N : ℝ)
  let D := unitPhaseDistance theta grid
  have hNposNat : 0 < N := Nat.two_pow_pos m
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNposNat
  have hNnonneg : 0 ≤ (N : ℝ) := le_of_lt hNpos
  have hD_nonneg : 0 ≤ D := by
    dsimp [D, grid]
    exact unitPhaseDistance_nonneg theta (((y : ℕ) : ℝ) / (N : ℝ))
  have hx_nonneg : 0 ≤ (N : ℝ) * D := by positivity
  have hbounds : (i : ℝ) ≤ (N : ℝ) * D ∧ (N : ℝ) * D < (i : ℝ) + 1 := by
    have hb' : Nat.floor ((N : ℝ) * D) = i := by
      simpa [qpeCircularDistanceBucket, N, D, grid] using hybucket
    exact (Nat.floor_eq_iff hx_nonneg).mp hb'
  have hloD : (i : ℝ) ≤ (N : ℝ) * D := hbounds.1
  have hhiD : (N : ℝ) * D < (i : ℝ) + 1 := hbounds.2
  have hD_upper : D < ((i : ℝ) + 1) / (N : ℝ) := by
    rw [lt_div_iff₀ hNpos]
    simpa [mul_comm] using hhiD
  have hcase :
      |theta - grid| < ((i : ℝ) + 1) / (N : ℝ) ∨
        |theta - grid - 1| < ((i : ℝ) + 1) / (N : ℝ) ∨
        |theta - grid + 1| < ((i : ℝ) + 1) / (N : ℝ) := by
    unfold D unitPhaseDistance at hD_upper
    rw [min_lt_iff] at hD_upper
    rcases hD_upper with h | h
    · exact Or.inl h
    · rw [min_lt_iff] at h
      exact Or.inr h
  have hlo0 : (i : ℝ) ≤ (N : ℝ) * |theta - grid| := by
    exact le_trans hloD (mul_le_mul_of_nonneg_left
      (unitPhaseDistance_le_abs_sub theta grid) hNnonneg)
  have hlo1 : (i : ℝ) ≤ (N : ℝ) * |theta - grid - 1| := by
    exact le_trans hloD (mul_le_mul_of_nonneg_left
      (unitPhaseDistance_le_sub_one theta grid) hNnonneg)
  have hlo2 : (i : ℝ) ≤ (N : ℝ) * |theta - grid + 1| := by
    exact le_trans hloD (mul_le_mul_of_nonneg_left
      (unitPhaseDistance_le_add_one theta grid) hNnonneg)
  rcases hcase with hcase0 | hcase1 | hcase2
  · have hhi0 : (N : ℝ) * |theta - grid| < (i : ℝ) + 1 := by
      have hmul := (lt_div_iff₀ hNpos).mp hcase0
      simpa [mul_comm] using hmul
    have hscale :
        (N : ℝ) * |theta - ((y : ℕ) : ℝ) / (N : ℝ)| =
          |(N : ℝ) * theta - ((y : ℕ) : ℝ)| := by
      calc
        (N : ℝ) * |theta - ((y : ℕ) : ℝ) / (N : ℝ)|
            = |(N : ℝ)| * |theta - ((y : ℕ) : ℝ) / (N : ℝ)| := by
              rw [abs_of_pos hNpos]
        _ = |(N : ℝ) * (theta - ((y : ℕ) : ℝ) / (N : ℝ))| := by
              rw [abs_mul]
        _ = |(N : ℝ) * theta - ((y : ℕ) : ℝ)| := by
              congr 1
              field_simp [hNpos.ne']
    have hlo_abs : (i : ℝ) ≤ |(N : ℝ) * theta - (((y : ℕ) : ℤ) : ℝ)| := by
      simpa [N, grid] using (show (i : ℝ) ≤ (N : ℝ) * |theta - ((y : ℕ) : ℝ) / (N : ℝ)| from hlo0)
        |> (fun h => by simpa [hscale] using h)
    have hhi_abs : |(N : ℝ) * theta - (((y : ℕ) : ℤ) : ℝ)| < (i : ℝ) + 1 := by
      have h : (N : ℝ) * |theta - ((y : ℕ) : ℝ) / (N : ℝ)| < (i : ℝ) + 1 := by
        simpa [grid] using hhi0
      simpa [hscale] using h
    simpa [N] using
      fin_eq_left_or_right_candidate_of_abs_sub_mem_Ico
        (N := N) hNposNat (x := (N : ℝ) * theta) (i := i) (y := y)
        (z := ((y : ℕ) : ℤ)) (by rfl) hlo_abs hhi_abs
  · have hhi1 : (N : ℝ) * |theta - grid - 1| < (i : ℝ) + 1 := by
      have hmul := (lt_div_iff₀ hNpos).mp hcase1
      simpa [mul_comm] using hmul
    have hscale :
        (N : ℝ) * |theta - ((y : ℕ) : ℝ) / (N : ℝ) - 1| =
          |(N : ℝ) * theta - (((y : ℕ) : ℤ) + (N : ℤ) : ℤ)| := by
      calc
        (N : ℝ) * |theta - ((y : ℕ) : ℝ) / (N : ℝ) - 1|
            = |(N : ℝ)| * |theta - ((y : ℕ) : ℝ) / (N : ℝ) - 1| := by
              rw [abs_of_pos hNpos]
        _ = |(N : ℝ) * (theta - ((y : ℕ) : ℝ) / (N : ℝ) - 1)| := by
              rw [abs_mul]
        _ = |(N : ℝ) * theta - (((y : ℕ) : ℤ) + (N : ℤ) : ℤ)| := by
              congr 1
              norm_num [Int.cast_add]
              field_simp [hNpos.ne']
              ring_nf
    have hlo_abs : (i : ℝ) ≤ |(N : ℝ) * theta - ((((y : ℕ) : ℤ) + (N : ℤ)) : ℝ)| := by
      have h : (i : ℝ) ≤ (N : ℝ) * |theta - ((y : ℕ) : ℝ) / (N : ℝ) - 1| := by
        simpa [grid] using hlo1
      simpa [hscale] using h
    have hhi_abs : |(N : ℝ) * theta - ((((y : ℕ) : ℤ) + (N : ℤ)) : ℝ)| < (i : ℝ) + 1 := by
      have h : (N : ℝ) * |theta - ((y : ℕ) : ℝ) / (N : ℝ) - 1| < (i : ℝ) + 1 := by
        simpa [grid] using hhi1
      simpa [hscale] using h
    have hmod : ((y : ℕ) : ℤ) ≡ (((y : ℕ) : ℤ) + (N : ℤ)) [ZMOD (N : ℤ)] :=
      (Int.add_modEq_right (a := ((y : ℕ) : ℤ)) (n := (N : ℤ))).symm
    simpa [N] using
      fin_eq_left_or_right_candidate_of_abs_sub_mem_Ico
        (N := N) hNposNat (x := (N : ℝ) * theta) (i := i) (y := y)
        (z := ((y : ℕ) : ℤ) + (N : ℤ)) hmod
        (by simpa [Int.cast_add] using hlo_abs)
        (by simpa [Int.cast_add] using hhi_abs)
  · have hhi2 : (N : ℝ) * |theta - grid + 1| < (i : ℝ) + 1 := by
      have hmul := (lt_div_iff₀ hNpos).mp hcase2
      simpa [mul_comm] using hmul
    have hscale :
        (N : ℝ) * |theta - ((y : ℕ) : ℝ) / (N : ℝ) + 1| =
          |(N : ℝ) * theta - (((y : ℕ) : ℤ) - (N : ℤ) : ℤ)| := by
      calc
        (N : ℝ) * |theta - ((y : ℕ) : ℝ) / (N : ℝ) + 1|
            = |(N : ℝ)| * |theta - ((y : ℕ) : ℝ) / (N : ℝ) + 1| := by
              rw [abs_of_pos hNpos]
        _ = |(N : ℝ) * (theta - ((y : ℕ) : ℝ) / (N : ℝ) + 1)| := by
              rw [abs_mul]
        _ = |(N : ℝ) * theta - (((y : ℕ) : ℤ) - (N : ℤ) : ℤ)| := by
              congr 1
              norm_num [Int.cast_sub]
              field_simp [hNpos.ne']
              ring_nf
    have hlo_abs : (i : ℝ) ≤ |(N : ℝ) * theta - ((((y : ℕ) : ℤ) - (N : ℤ)) : ℝ)| := by
      have h : (i : ℝ) ≤ (N : ℝ) * |theta - ((y : ℕ) : ℝ) / (N : ℝ) + 1| := by
        simpa [grid] using hlo2
      simpa [hscale] using h
    have hhi_abs : |(N : ℝ) * theta - ((((y : ℕ) : ℤ) - (N : ℤ)) : ℝ)| < (i : ℝ) + 1 := by
      have h : (N : ℝ) * |theta - ((y : ℕ) : ℝ) / (N : ℝ) + 1| < (i : ℝ) + 1 := by
        simpa [grid] using hhi2
      simpa [hscale] using h
    have hmod : ((y : ℕ) : ℤ) ≡ (((y : ℕ) : ℤ) - (N : ℤ)) [ZMOD (N : ℤ)] :=
      (by
        rw [Int.ModEq]
        rw [Int.sub_emod]
        simp)
    simpa [N] using
      fin_eq_left_or_right_candidate_of_abs_sub_mem_Ico
        (N := N) hNposNat (x := (N : ℝ) * theta) (i := i) (y := y)
        (z := ((y : ℕ) : ℤ) - (N : ℤ)) hmod
        (by simpa [Int.cast_sub] using hlo_abs)
        (by simpa [Int.cast_sub] using hhi_abs)

/-- Each circular-distance bucket contains at most two grid outcomes. -/
theorem qpeCircularDistanceBucket_filter_card_le_two
    (m k i : ℕ) (theta : ℝ) :
    ((qpeCircularPhaseWindowFailureOutcomes m k theta).filter
      (fun y => qpeCircularDistanceBucket m theta y = i)).card ≤ 2 := by
  classical
  let left : Fin (M m) :=
    ⟨((Int.floor ((M m : ℝ) * theta) - (i : ℤ) : ℤ) : ZMod (M m)).val, by
      exact ZMod.val_lt (((Int.floor ((M m : ℝ) * theta) - (i : ℤ) : ℤ) : ZMod (M m)))⟩
  let right : Fin (M m) :=
    ⟨((Int.ceil ((M m : ℝ) * theta) + (i : ℤ) : ℤ) : ZMod (M m)).val, by
      exact ZMod.val_lt (((Int.ceil ((M m : ℝ) * theta) + (i : ℤ) : ℤ) : ZMod (M m)))⟩
  have hsubset :
      (qpeCircularPhaseWindowFailureOutcomes m k theta).filter
          (fun y => qpeCircularDistanceBucket m theta y = i) ⊆
        ({left, right} : Finset (Fin (M m))) := by
    intro y hy
    have hybucket : qpeCircularDistanceBucket m theta y = i := (Finset.mem_filter.mp hy).2
    rcases qpeCircularDistanceBucket_eq_imp_left_or_right_candidate m i theta hybucket with h | h
    · simp [left, h]
    · simp [right, h]
  exact le_trans (Finset.card_le_card hsubset) Finset.card_le_two


/-- BHMT11 `k > 1` failure bound with the distance-bucket cardinality fact proved. -/
theorem qpeCircularFailureProbability_le_k_gt_one
    (m k : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (hk : 1 < k) :
    qpeCircularPhaseWindowFailureProbability m k theta ≤
      1 / (2 * ((k : ℝ) - 1)) := by
  apply qpeCircularFailureProbability_le_of_bucket_tail
    (m := m) (k := k) (n := M m) (theta := theta) hk
    (bucket := qpeCircularDistanceBucket m theta)
  · intro y hy
    exact qpeCircularDistanceBucket_mem_tail_of_failure m k h0 h1 (by omega) hy
  · intro y hy
    exact qpeApproxOutcomeProbability_failure_upper_bound_distanceBucket m k h0 h1 hk hy
  · exact by
      intro i _hi
      exact qpeCircularDistanceBucket_filter_card_le_two m k i theta

/-- BHMT11 `k > 1` circular-window success bound with no remaining cardinality
hypothesis. -/
theorem qpeCircularPhaseWindowProbability_lower_bound_k_gt_one
    (m k : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (hk : 1 < k) :
    bhmt11SuccessProbability k ≤ qpeCircularPhaseWindowProbability m k theta := by
  have hfail := qpeCircularFailureProbability_le_k_gt_one m k h0 h1 hk
  have hsucc := qpeCircularPhaseWindowProbability_eq_one_sub_failure m k theta
  have hk_ne : k ≠ 1 := by omega
  rw [bhmt11SuccessProbability, if_neg hk_ne]
  rw [hsucc]
  linarith

theorem qpeApproxGeometricProbability_lower_bound {N : ℕ} {delta : ℝ}
    (hN : 0 < N) (hclose : |delta| ≤ 1 / (2 * (N : ℝ))) :
    4 / Real.pi ^ 2 ≤ qpeApproxGeometricProbability N delta := by
  unfold qpeApproxGeometricProbability
  by_cases hdelta : delta = 0
  · simp [hdelta]
    have hpi2 : 4 ≤ Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_three]
    have hpi_sq_pos : 0 < Real.pi ^ 2 := sq_pos_of_ne_zero Real.pi_ne_zero
    exact (div_le_one hpi_sq_pos).mpr hpi2
  · simp [hdelta]
    set a := |Real.sin (Real.pi * (N : ℝ) * delta)|
    set b := |Real.sin (Real.pi * delta)|
    have hNposR : 0 < (N : ℝ) := by exact_mod_cast hN
    have hNnonnegR : 0 ≤ (N : ℝ) := le_of_lt hNposR
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have hpi_nonneg : 0 ≤ Real.pi := le_of_lt hpi_pos
    have hnum_arg_le : |Real.pi * (N : ℝ) * delta| ≤ Real.pi / 2 := by
      calc
        |Real.pi * (N : ℝ) * delta| = Real.pi * (N : ℝ) * |delta| := by
          rw [abs_mul, abs_mul, abs_of_pos hpi_pos, abs_of_nonneg hNnonnegR]
        _ ≤ Real.pi * (N : ℝ) * (1 / (2 * (N : ℝ))) := by
          gcongr
        _ = Real.pi / 2 := by
          field_simp [ne_of_gt hNposR]
    have hnum_lower_raw := Real.mul_abs_le_abs_sin
      (x := Real.pi * (N : ℝ) * delta) hnum_arg_le
    have hnum_lower : 2 * (N : ℝ) * |delta| ≤ a := by
      dsimp [a]
      calc
        2 * (N : ℝ) * |delta| = 2 / Real.pi * |Real.pi * (N : ℝ) * delta| := by
          rw [abs_mul, abs_mul, abs_of_pos hpi_pos, abs_of_nonneg hNnonnegR]
          field_simp [Real.pi_ne_zero]
        _ ≤ |Real.sin (Real.pi * (N : ℝ) * delta)| := hnum_lower_raw
    have hden_upper_raw := Real.abs_sin_le_abs (x := Real.pi * delta)
    have hden_upper : b ≤ Real.pi * |delta| := by
      dsimp [b]
      calc
        |Real.sin (Real.pi * delta)| ≤ |Real.pi * delta| := hden_upper_raw
        _ = Real.pi * |delta| := by
          rw [abs_mul, abs_of_pos hpi_pos]
    have hdelta_le_half : |delta| ≤ (1 : ℝ) / 2 := by
      calc
        |delta| ≤ 1 / (2 * (N : ℝ)) := hclose
        _ ≤ 1 / 2 := by
          have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          rw [div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) * (N : ℝ))
            (by norm_num : (0 : ℝ) < 2)]
          nlinarith
    have harg_abs_lt_pi : |Real.pi * delta| < Real.pi := by
      calc
        |Real.pi * delta| = Real.pi * |delta| := by
          rw [abs_mul, abs_of_pos hpi_pos]
        _ ≤ Real.pi * (1 / 2) := by gcongr
        _ < Real.pi := by nlinarith [Real.pi_pos]
    have harg_ne_zero : Real.pi * delta ≠ 0 := by
      exact mul_ne_zero Real.pi_ne_zero hdelta
    have hsin_ne : Real.sin (Real.pi * delta) ≠ 0 := by
      have hz := (Real.sin_eq_zero_iff_of_lt_of_lt (x := Real.pi * delta)
        (by have := abs_lt.mp harg_abs_lt_pi; exact this.1)
        (by have := abs_lt.mp harg_abs_lt_pi; exact this.2)).mp
      intro hs
      exact harg_ne_zero (hz hs)
    have hb_pos : 0 < b := by
      dsimp [b]
      exact abs_pos.mpr hsin_ne
    have hNb_pos : 0 < (N : ℝ) * b := mul_pos hNposR hb_pos
    have hratio_lower : 2 / Real.pi ≤ a / ((N : ℝ) * b) := by
      rw [le_div_iff₀ hNb_pos]
      calc
        2 / Real.pi * ((N : ℝ) * b) ≤
            2 / Real.pi * ((N : ℝ) * (Real.pi * |delta|)) := by
          gcongr
        _ = 2 * (N : ℝ) * |delta| := by
          field_simp [Real.pi_ne_zero]
        _ ≤ a := hnum_lower
    have hratio_abs_lower :
        2 / Real.pi ≤
          |Real.sin (Real.pi * (N : ℝ) * delta) /
            ((N : ℝ) * Real.sin (Real.pi * delta))| := by
      have habs_ratio :
          |Real.sin (Real.pi * (N : ℝ) * delta) /
            ((N : ℝ) * Real.sin (Real.pi * delta))| = a / ((N : ℝ) * b) := by
        dsimp [a, b]
        rw [abs_div, abs_mul, abs_of_pos hNposR]
      rw [habs_ratio]
      exact hratio_lower
    have htwo_div_pi_nonneg : 0 ≤ 2 / Real.pi := div_nonneg (by norm_num) hpi_nonneg
    have hratio_abs_lower' :
        |2 / Real.pi| ≤
          |Real.sin (Real.pi * (N : ℝ) * delta) /
            ((N : ℝ) * Real.sin (Real.pi * delta))| := by
      simpa [abs_of_nonneg htwo_div_pi_nonneg] using hratio_abs_lower
    have hsquares :
        (2 / Real.pi) ^ 2 ≤
          (Real.sin (Real.pi * (N : ℝ) * delta) /
            ((N : ℝ) * Real.sin (Real.pi * delta))) ^ 2 := by
      simpa [sq_abs] using (sq_le_sq.mpr hratio_abs_lower')
    calc
      4 / Real.pi ^ 2 = (2 / Real.pi) ^ 2 := by ring_nf
      _ ≤ (Real.sin (Real.pi * (N : ℝ) * delta) /
          ((N : ℝ) * Real.sin (Real.pi * delta))) ^ 2 := hsquares

/-- Unconditional matrix-level nearest-outcome lower bound for approximate QPE. -/
theorem qpeApproxOutcomeProbability_lower_bound_nearest
    (m : ℕ) {theta : ℝ} (y : Fin (M m))
    (hclose : |theta - (((y : ℕ) : ℝ) / (M m : ℝ))| ≤ 1 / (2 * (M m : ℝ))) :
    4 / Real.pi ^ 2 ≤ qpeApproxOutcomeProbability m theta y := by
  rw [qpeApproxOutcomeProbability_eq_geometric_of_nearest m theta y hclose]
  exact qpeApproxGeometricProbability_lower_bound (Nat.two_pow_pos m) hclose

/-- Exact-grid lower adjacent outcome has probability one. -/
theorem qpeApproxOutcomeProbability_lowerAdjacent_eq_one_of_fractionalOffset_eq_zero
    (m : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1)
    (hx : qpeFractionalOffset m theta = 0) :
    qpeApproxOutcomeProbability m theta (qpeLowerAdjacentOutcome m theta) = 1 := by
  let y := qpeLowerAdjacentOutcome m theta
  change qpeApproxOutcomeProbability m theta y = 1
  have hyval : (y : ℕ) = floorGridIndexNat m theta := by
    dsimp [y]
    exact Nat.mod_eq_of_lt (floorGridIndexNat_lt_M_of_mem_Ico m h0 h1)
  have htheta := theta_eq_floorGrid_div_of_qpeFractionalOffset_eq_zero m h0 hx
  have htheta_y : theta = ((y : ℕ) : ℝ) / (M m : ℝ) := by
    rw [htheta, hyval]
  have hclose : |theta - (((y : ℕ) : ℝ) / (M m : ℝ))| ≤ 1 / (2 * (M m : ℝ)) := by
    rw [htheta_y]
    simp
  have hgeom := qpeApproxOutcomeProbability_eq_geometric_of_nearest m theta y hclose
  rw [hgeom]
  simp [htheta_y, qpeApproxGeometricProbability]

/-- Exact-grid `k = 1` circular-window lower bound on `[0, 1)`. -/
theorem qpeCircularPhaseWindowProbability_lower_bound_k1_exactGrid_of_mem_Ico
    (m : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1)
    (hx : qpeFractionalOffset m theta = 0) :
    8 / Real.pi ^ 2 ≤ qpeCircularPhaseWindowProbability m 1 theta := by
  let y := qpeLowerAdjacentOutcome m theta
  have hprob_one : qpeApproxOutcomeProbability m theta y = 1 := by
    dsimp [y]
    exact qpeApproxOutcomeProbability_lowerAdjacent_eq_one_of_fractionalOffset_eq_zero m h0 h1 hx
  have htheta := theta_eq_floorGrid_div_of_qpeFractionalOffset_eq_zero m h0 hx
  have hyval : (y : ℕ) = floorGridIndexNat m theta := by
    dsimp [y]
    exact Nat.mod_eq_of_lt (floorGridIndexNat_lt_M_of_mem_Ico m h0 h1)
  have htheta_y : theta = ((y : ℕ) : ℝ) / (M m : ℝ) := by
    rw [htheta, hyval]
  have hywin : y ∈ qpeCircularPhaseWindowOutcomes m 1 theta := by
    apply (mem_qpeCircularPhaseWindowOutcomes_iff m 1 theta y).mpr
    unfold qpeCircularPhaseWindow
    rw [htheta_y]
    unfold unitPhaseDistance
    simp
  have hsingle : qpeApproxOutcomeProbability m theta y ≤
      (qpeCircularPhaseWindowOutcomes m 1 theta).sum
        (fun z => qpeApproxOutcomeProbability m theta z) :=
    Finset.single_le_sum (fun z _hz => qpeApproxOutcomeProbability_nonneg m theta z) hywin
  rw [hprob_one] at hsingle
  have h8_le_one : 8 / Real.pi ^ 2 ≤ 1 := by
    have hpi_sq_pos : 0 < Real.pi ^ 2 := sq_pos_of_ne_zero Real.pi_ne_zero
    have hpi_sq_ge_eight : 8 ≤ Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_three]
    exact (div_le_one hpi_sq_pos).mpr hpi_sq_ge_eight
  exact le_trans h8_le_one hsingle

private theorem qpeApproxOutcomeProbability_eq_sub_one
    (m : ℕ) (theta : ℝ) (y : Fin (M m)) :
    qpeApproxOutcomeProbability m theta y = qpeApproxOutcomeProbability m (theta - 1) y := by
  have h := qpeApproxOutcomeProbability_add_one m (theta - 1) y
  have harg : theta - 1 + 1 = theta := by ring_nf
  simpa [harg] using h

private theorem sin_pi_scaled_fractional_ne_zero
    (m : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Real.sin (Real.pi * (x / (M m : ℝ))) ≠ 0 := by
  have hMpos : 0 < (M m : ℝ) := by exact_mod_cast (Nat.two_pow_pos m)
  have harg_pos : 0 < Real.pi * (x / (M m : ℝ)) := by positivity
  have hx_div_lt_one : x / (M m : ℝ) < 1 := by
    have hMge1 : (1 : ℝ) ≤ (M m : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt (Nat.two_pow_pos m))
    rw [div_lt_one hMpos]
    nlinarith
  have harg_lt_pi : Real.pi * (x / (M m : ℝ)) < Real.pi := by
    nlinarith [Real.pi_pos, hx_div_lt_one]
  exact (Real.sin_pos_of_pos_of_lt_pi harg_pos harg_lt_pi).ne'

private theorem sin_pi_scaled_one_sub_fractional_neg_ne_zero
    (m : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Real.sin (Real.pi * (-(1 - x) / (M m : ℝ))) ≠ 0 := by
  have hx10 : 0 < 1 - x := by linarith
  have hx11 : 1 - x < 1 := by linarith
  have hpos := sin_pi_scaled_fractional_ne_zero m hx10 hx11
  have harg : Real.pi * (-(1 - x) / (M m : ℝ)) =
      -(Real.pi * ((1 - x) / (M m : ℝ))) := by ring_nf
  rw [harg, Real.sin_neg]
  exact neg_ne_zero.mpr hpos

/-- Lower adjacent outcome probability as the lower two-nearest geometric term. -/
theorem qpeApproxOutcomeProbability_lowerAdjacent_eq_geometric_fractionalOffset
    (m : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1)
    (hx0 : 0 < qpeFractionalOffset m theta) :
    qpeApproxOutcomeProbability m theta (qpeLowerAdjacentOutcome m theta) =
      qpeApproxGeometricProbability (M m)
        (qpeFractionalOffset m theta / (M m : ℝ)) := by
  let y := qpeLowerAdjacentOutcome m theta
  change qpeApproxOutcomeProbability m theta y =
      qpeApproxGeometricProbability (M m)
        (qpeFractionalOffset m theta / (M m : ℝ))
  have hMpos : 0 < (M m : ℝ) := by exact_mod_cast (Nat.two_pow_pos m)
  have hyval : (y : ℕ) = floorGridIndexNat m theta := by
    dsimp [y]
    exact Nat.mod_eq_of_lt (floorGridIndexNat_lt_M_of_mem_Ico m h0 h1)
  have hdelta : theta - (((y : ℕ) : ℝ) / (M m : ℝ)) =
      qpeFractionalOffset m theta / (M m : ℝ) := by
    rw [hyval]
    rw [show qpeFractionalOffset m theta =
        (M m : ℝ) * theta - (floorGridIndexNat m theta : ℝ) by
      have hMnonneg : 0 ≤ (M m : ℝ) := by exact_mod_cast (Nat.zero_le (M m))
      have hx_nonneg : 0 ≤ (M m : ℝ) * theta := mul_nonneg hMnonneg h0
      unfold qpeFractionalOffset floorGridIndexNat
      rw [Int.fract]
      rw [← natCast_floor_eq_intCast_floor hx_nonneg]]
    field_simp [hMpos.ne']
  have hden : Real.sin (Real.pi * (theta - (((y : ℕ) : ℝ) / (M m : ℝ)))) ≠ 0 := by
    rw [hdelta]
    exact sin_pi_scaled_fractional_ne_zero m hx0 (Int.fract_lt_one ((M m : ℝ) * theta))
  rw [qpeApproxOutcomeProbability_eq_geometric_of_sin_ne_zero m theta y hden]
  rw [hdelta]

/-- Upper adjacent outcome probability as the upper two-nearest geometric term,
with cyclic wraparound handled by phase periodicity. -/
theorem qpeApproxOutcomeProbability_upperAdjacent_eq_geometric_fractionalOffset
    (m : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1)
    (hx0 : 0 < qpeFractionalOffset m theta) :
    qpeApproxOutcomeProbability m theta (qpeUpperAdjacentOutcome m theta) =
      qpeApproxGeometricProbability (M m)
        (-(1 - qpeFractionalOffset m theta) / (M m : ℝ)) := by
  let y := qpeUpperAdjacentOutcome m theta
  let n := floorGridIndexNat m theta
  change qpeApproxOutcomeProbability m theta y =
      qpeApproxGeometricProbability (M m)
        (-(1 - qpeFractionalOffset m theta) / (M m : ℝ))
  have hMposNat : 0 < M m := Nat.two_pow_pos m
  have hMpos : 0 < (M m : ℝ) := by exact_mod_cast hMposNat
  have hn_lt : n < M m := by
    dsimp [n]
    exact floorGridIndexNat_lt_M_of_mem_Ico m h0 h1
  have hx1 : qpeFractionalOffset m theta < 1 := Int.fract_lt_one ((M m : ℝ) * theta)
  have hden_target : Real.sin (Real.pi * (-(1 - qpeFractionalOffset m theta) / (M m : ℝ))) ≠ 0 :=
    sin_pi_scaled_one_sub_fractional_neg_ne_zero m hx0 hx1
  by_cases hsucc_lt : n + 1 < M m
  · have hyval : (y : ℕ) = n + 1 := by
      dsimp [y, qpeUpperAdjacentOutcome, n]
      exact Nat.mod_eq_of_lt hsucc_lt
    have hdelta : theta - (((y : ℕ) : ℝ) / (M m : ℝ)) =
        -(1 - qpeFractionalOffset m theta) / (M m : ℝ) := by
      rw [hyval]
      dsimp [n]
      rw [show qpeFractionalOffset m theta =
          (M m : ℝ) * theta - (floorGridIndexNat m theta : ℝ) by
        have hMnonneg : 0 ≤ (M m : ℝ) := by exact_mod_cast (Nat.zero_le (M m))
        have hx_nonneg : 0 ≤ (M m : ℝ) * theta := mul_nonneg hMnonneg h0
        unfold qpeFractionalOffset floorGridIndexNat
        rw [Int.fract]
        rw [← natCast_floor_eq_intCast_floor hx_nonneg]]
      field_simp [hMpos.ne']
      norm_num [Nat.cast_add]
      ring_nf
    have hden : Real.sin (Real.pi * (theta - (((y : ℕ) : ℝ) / (M m : ℝ)))) ≠ 0 := by
      rw [hdelta]
      exact hden_target
    rw [qpeApproxOutcomeProbability_eq_geometric_of_sin_ne_zero m theta y hden]
    rw [hdelta]
  · have hsucc_eq : n + 1 = M m := by omega
    have hyval : (y : ℕ) = 0 := by
      dsimp [y, qpeUpperAdjacentOutcome, n]
      rw [hsucc_eq, Nat.mod_self]
    have hdelta_sub : theta - 1 - (((y : ℕ) : ℝ) / (M m : ℝ)) =
        -(1 - qpeFractionalOffset m theta) / (M m : ℝ) := by
      rw [hyval]
      norm_num
      have hnreal : ((n : ℕ) : ℝ) + 1 = (M m : ℝ) := by exact_mod_cast hsucc_eq
      dsimp [n] at hnreal
      rw [show qpeFractionalOffset m theta =
          (M m : ℝ) * theta - (floorGridIndexNat m theta : ℝ) by
        have hMnonneg : 0 ≤ (M m : ℝ) := by exact_mod_cast (Nat.zero_le (M m))
        have hx_nonneg : 0 ≤ (M m : ℝ) * theta := mul_nonneg hMnonneg h0
        unfold qpeFractionalOffset floorGridIndexNat
        rw [Int.fract]
        rw [← natCast_floor_eq_intCast_floor hx_nonneg]]
      field_simp [hMpos.ne']
      nlinarith
    have hden : Real.sin (Real.pi * (theta - 1 - (((y : ℕ) : ℝ) / (M m : ℝ)))) ≠ 0 := by
      rw [hdelta_sub]
      exact hden_target
    rw [qpeApproxOutcomeProbability_eq_sub_one m theta y]
    rw [qpeApproxOutcomeProbability_eq_geometric_of_sin_ne_zero m (theta - 1) y hden]
    rw [hdelta_sub]

/-- The one-point counting grid `m = 0` satisfies the `k = 1` lower bound
directly: the only outcome has probability one and lies in the radius-one window
for `theta ∈ [0, 1]`. -/
theorem qpeCircularPhaseWindowProbability_lower_bound_k1_m_zero
    {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    8 / Real.pi ^ 2 ≤ qpeCircularPhaseWindowProbability 0 1 theta := by
  let y := zeroIndex 0
  have hprob_one : qpeApproxOutcomeProbability 0 theta y = 1 := by
    unfold qpeApproxOutcomeProbability
    rw [qpeApproxAmplitude_eq_normalized_phase_sum]
    simp [M, y, zeroIndex]
  have hywin : y ∈ qpeCircularPhaseWindowOutcomes 0 1 theta := by
    apply (mem_qpeCircularPhaseWindowOutcomes_iff 0 1 theta y).mpr
    unfold qpeCircularPhaseWindow
    have hdist : unitPhaseDistance theta (((y : ℕ) : ℝ) / (M 0 : ℝ)) ≤ 1 := by
      exact le_trans (unitPhaseDistance_le_abs_sub theta (((y : ℕ) : ℝ) / (M 0 : ℝ))) (by
        dsimp [y, zeroIndex, M]
        simpa [abs_of_nonneg h0] using h1)
    simpa [M] using hdist
  unfold qpeCircularPhaseWindowProbability
  have hsingle : qpeApproxOutcomeProbability 0 theta y ≤
      (qpeCircularPhaseWindowOutcomes 0 1 theta).sum
        (fun z => qpeApproxOutcomeProbability 0 theta z) :=
    Finset.single_le_sum (fun z _hz => qpeApproxOutcomeProbability_nonneg 0 theta z) hywin
  rw [hprob_one] at hsingle
  have h8_le_one : 8 / Real.pi ^ 2 ≤ 1 := by
    have hpi_sq_pos : 0 < Real.pi ^ 2 := sq_pos_of_ne_zero Real.pi_ne_zero
    have hpi_sq_ge_eight : 8 ≤ Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_three]
    exact (div_le_one hpi_sq_pos).mpr hpi_sq_ge_eight
  exact le_trans h8_le_one hsingle

/-- Endpoint `theta = 1` for the `k = 1` circular-window lower bound.  The
probability is reduced by periodicity to the exact grid point `theta = 0`. -/
theorem qpeCircularPhaseWindowProbability_lower_bound_k1_theta_one
    (m : ℕ) :
    8 / Real.pi ^ 2 ≤ qpeCircularPhaseWindowProbability m 1 1 := by
  let y := zeroIndex m
  have hprob_zero : qpeApproxOutcomeProbability m 0 y = 1 := by
    have hclose : |(0 : ℝ) - (((y : ℕ) : ℝ) / (M m : ℝ))| ≤
        1 / (2 * (M m : ℝ)) := by
      dsimp [y, zeroIndex]
      simp
    have hgeom := qpeApproxOutcomeProbability_eq_geometric_of_nearest m 0 y hclose
    rw [hgeom]
    simp [qpeApproxGeometricProbability, y, zeroIndex]
  have hprob_one : qpeApproxOutcomeProbability m 1 y = 1 := by
    rw [qpeApproxOutcomeProbability_eq_sub_one]
    simpa using hprob_zero
  have hywin : y ∈ qpeCircularPhaseWindowOutcomes m 1 1 := by
    apply (mem_qpeCircularPhaseWindowOutcomes_iff m 1 1 y).mpr
    unfold qpeCircularPhaseWindow unitPhaseDistance
    dsimp [y, zeroIndex]
    simp
  unfold qpeCircularPhaseWindowProbability
  have hsingle : qpeApproxOutcomeProbability m 1 y ≤
      (qpeCircularPhaseWindowOutcomes m 1 1).sum
        (fun z => qpeApproxOutcomeProbability m 1 z) :=
    Finset.single_le_sum (fun z _hz => qpeApproxOutcomeProbability_nonneg m 1 z) hywin
  rw [hprob_one] at hsingle
  have h8_le_one : 8 / Real.pi ^ 2 ≤ 1 := by
    have hpi_sq_pos : 0 < Real.pi ^ 2 := sq_pos_of_ne_zero Real.pi_ne_zero
    have hpi_sq_ge_eight : 8 ≤ Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_three]
    exact (div_le_one hpi_sq_pos).mpr hpi_sq_ge_eight
  exact le_trans h8_le_one hsingle

theorem qpeCircularPhaseWindowProbability_lower_bound_one_of_mem_unitInterval
    (m : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    4 / Real.pi ^ 2 ≤ qpeCircularPhaseWindowProbability m 1 theta := by
  classical
  let n := (round ((M m : ℝ) * theta)).toNat
  have hn_le : n ≤ M m := by
    dsimp [n]
    have hMpos : 0 < (M m : ℝ) := by exact_mod_cast (Nat.two_pow_pos m)
    let x : ℝ := (M m : ℝ) * theta
    have hx_nonneg : 0 ≤ x := by nlinarith [hMpos, h0]
    have hround_nonneg : 0 ≤ round x := by
      rw [round_eq]
      exact Int.floor_nonneg.mpr (by nlinarith)
    have hx_lt : x + (1 / 2 : ℝ) < (M m : ℝ) + 1 := by
      nlinarith [hMpos, h1]
    have hround_lt : round x < (M m : ℤ) + 1 := by
      rw [round_eq, Int.floor_lt]
      exact_mod_cast hx_lt
    have hnat_lt : (round x).toNat < M m + 1 := by
      rw [← Nat.cast_lt (α := ℤ), Int.toNat_of_nonneg hround_nonneg]
      simpa using hround_lt
    simpa [x] using Nat.lt_succ_iff.mp hnat_lt
  by_cases hn_lt : n < M m
  · let y : Fin (M m) := ⟨n, hn_lt⟩
    have hclose : |theta - (((y : ℕ) : ℝ) / (M m : ℝ))| ≤ 1 / (2 * (M m : ℝ)) := by
      exact abs_grid_error_le_half_div_M m h0 rfl
    have hprob : 4 / Real.pi ^ 2 ≤ qpeApproxOutcomeProbability m theta y :=
      qpeApproxOutcomeProbability_lower_bound_nearest m y hclose
    have hywin : y ∈ qpeCircularPhaseWindowOutcomes m 1 theta := by
      apply (mem_qpeCircularPhaseWindowOutcomes_iff m 1 theta y).mpr
      unfold qpeCircularPhaseWindow
      exact le_trans (unitPhaseDistance_le_abs_sub theta (((y : ℕ) : ℝ) / (M m : ℝ)))
        (by simpa using le_trans hclose (half_div_M_le_one_div_M m))
    unfold qpeCircularPhaseWindowProbability
    exact le_trans hprob
      (Finset.single_le_sum (fun z _hz => qpeApproxOutcomeProbability_nonneg m theta z) hywin)
  · have hn_eq : n = M m := le_antisymm hn_le (Nat.le_of_not_gt hn_lt)
    let y : Fin (M m) := zeroIndex m
    have hclose_raw : |theta - 1| ≤ 1 / (2 * (M m : ℝ)) := by
      have hcloseM : |theta - (n : ℝ) / (M m : ℝ)| ≤ 1 / (2 * (M m : ℝ)) :=
        abs_grid_error_le_half_div_M m h0 rfl
      have hMpos : 0 < (M m : ℝ) := by exact_mod_cast (Nat.two_pow_pos m)
      have hone : (n : ℝ) / (M m : ℝ) = 1 := by
        rw [hn_eq]
        field_simp [hMpos.ne']
      simpa [hone] using hcloseM
    have hclose_sub : |(theta - 1) - (((y : ℕ) : ℝ) / (M m : ℝ))| ≤ 1 / (2 * (M m : ℝ)) := by
      simpa [y, zeroIndex] using hclose_raw
    have hprob_sub : 4 / Real.pi ^ 2 ≤ qpeApproxOutcomeProbability m (theta - 1) y :=
      qpeApproxOutcomeProbability_lower_bound_nearest m y hclose_sub
    have hprob : 4 / Real.pi ^ 2 ≤ qpeApproxOutcomeProbability m theta y := by
      rw [qpeApproxOutcomeProbability_eq_sub_one]
      exact hprob_sub
    have hywin : y ∈ qpeCircularPhaseWindowOutcomes m 1 theta := by
      apply (mem_qpeCircularPhaseWindowOutcomes_iff m 1 theta y).mpr
      unfold qpeCircularPhaseWindow
      exact le_trans (unitPhaseDistance_le_sub_one theta (((y : ℕ) : ℝ) / (M m : ℝ)))
        (by
          have htmp : |theta - (((y : ℕ) : ℝ) / (M m : ℝ)) - 1| ≤ 1 / (2 * (M m : ℝ)) := by
            simpa [y, zeroIndex] using hclose_raw
          simpa using le_trans htmp (half_div_M_le_one_div_M m))
    unfold qpeCircularPhaseWindowProbability
    exact le_trans hprob
      (Finset.single_le_sum (fun z _hz => qpeApproxOutcomeProbability_nonneg m theta z) hywin)

/-- Concrete QPE state for an arbitrary real eigenphase.  Unlike exact QPE, the
counting register is generally a distribution over basis states after inverse QFT. -/
def approxQPEStateConcrete {n : ℕ} {m : ℕ} {U : Square n} {ψ : Vector n}
    (_theta : ℝ) : Vector (M m * n) :=
  (inverseQFTMatrix m ⊗ (I n)) ⬝ (controlledPowerMatrix m U ⬝ (uniformState m ⊗ ψ))

/-- Approximate QPE semantics: after phase kickback and inverse QFT, the counting
register is exactly `inverseQFTMatrix m ⬝ phaseState m theta`. -/
theorem approxQPEStateConcrete_eq_distribution_tensor_eigenstate {n : ℕ} {m : ℕ}
    {U : Square n} {ψ : Vector n} {theta : ℝ}
    (heigen : U ⬝ ψ = ((Real.fourierChar theta : ℂ)) • ψ) :
    approxQPEStateConcrete (U := U) (ψ := ψ) theta =
      (inverseQFTMatrix m ⬝ phaseState m theta) ⊗ ψ := by
  unfold approxQPEStateConcrete
  rw [controlledPowerMatrix_mul_uniform_of_real_eigenphase heigen]
  rw [Matrix.kron_mul]
  simp [Matrix.mul]

/-- Approximate QPE joint probability formula.  The counting-register marginal is
`qpeApproxOutcomeProbability m theta y`; the target register keeps the original
computational-basis distribution of `ψ`. -/
theorem approxQPEConcrete_joint_probability {n : ℕ} {m : ℕ} {U : Square n}
    {ψ : Vector n} {theta : ℝ} (y : Fin (M m)) (j : Fin n)
    (heigen : U ⬝ ψ = ((Real.fourierChar theta : ℂ)) • ψ) :
    Measurement.prob (approxQPEStateConcrete (U := U) (ψ := ψ) theta) (finProdFinEquiv (y, j)) =
      qpeApproxOutcomeProbability m theta y * Measurement.prob ψ j := by
  rw [approxQPEStateConcrete_eq_distribution_tensor_eigenstate heigen]
  rw [Measurement.prob_kron_apply]
  rfl

/-- Approximate QPE specializes to exact QPE when the phase is exactly representable
as `y / M`. -/
theorem approxQPEStateConcrete_eq_exact_phase_distribution {n : ℕ} {m : ℕ}
    {U : Square n} {ψ : Vector n} {y : Fin (M m)}
    (heigen : U ⬝ ψ = ((Real.fourierChar (((y : ℕ) : ℝ) / (M m : ℝ)) : ℂ)) • ψ) :
    approxQPEStateConcrete (U := U) (ψ := ψ) (((y : ℕ) : ℝ) / (M m : ℝ)) =
      Vector.basis y ⊗ ψ := by
  rw [approxQPEStateConcrete_eq_distribution_tensor_eigenstate heigen]
  rw [phaseState_eq_fourierState]
  exact (inverseQFTMatrixCorrectOfQFTUnitary (qftMatrix_isUnitary m)).maps_fourierState y ▸ rfl

end QPE
end QAE
