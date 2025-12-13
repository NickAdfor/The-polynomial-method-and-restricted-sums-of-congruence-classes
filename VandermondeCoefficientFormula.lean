import Mathlib

open MvPolynomial
open Finset
open Matrix
open BigOperators

variable {k : ℕ}

/-- Falling factorial (s)_r = s(s-1)...(s-r+1) -/
def falling_factorial (s : ℕ) (r : ℕ) : ℕ :=
  if r = 0 then 1
  else ∏ i ∈ range r, (s - i)

/-- Polynomial P = (∑ xᵢ)^m * Vandermonde product -/
noncomputable def polynomial_P (m : ℕ) : MvPolynomial (Fin (k+1)) ℚ :=
  let S : MvPolynomial (Fin (k+1)) ℚ := ∑ i : Fin (k+1), X i
  let V : MvPolynomial (Fin (k+1)) ℚ :=
    ∏ i : Fin (k+1), ∏ j : Fin (k+1), if j < i then (X i - X j) else 1
  S ^ m * V

/-- Monomial expression = ∏ᵢ Xᵢ^{cᵢ} -/
noncomputable def monomial_expr (c : Fin (k+1) → ℕ) : MvPolynomial (Fin (k+1)) ℚ :=
  ∏ i : Fin (k+1), (X i) ^ (c i)

/-- Vandermonde matrix (cᵢ^j) -/
def vandermonde_matrix (c : Fin (k+1) → ℕ) : Matrix (Fin (k+1)) (Fin (k+1)) ℚ :=
  Matrix.of (fun i j : Fin (k+1) => (c i : ℚ) ^ (j : ℕ))

/-- Falling factorial matrix ((cᵢ)_j) -/
def falling_factorial_matrix (c : Fin (k+1) → ℕ) : Matrix (Fin (k+1)) (Fin (k+1)) ℚ :=
  Matrix.of (fun i j : Fin (k+1) => (falling_factorial (c i) j : ℚ))

/-- Symmetric group sum expression C = ∑_{σ∈S_{k+1}} (-1)^{sign(σ)} * m! / ∏ᵢ (cᵢ - σ(i))! -/
def symmetric_sum (c : Fin (k+1) → ℕ) (m : ℕ) : ℚ :=
  ∑ σ : Equiv.Perm (Fin (k+1)),
    ((-1 : ℚ)) ^ (σ.sign : ℤ) *
    ((m.factorial : ℚ) / ∏ i : Fin (k+1), ((c i - (σ i : ℕ)).factorial : ℚ))

/-- Expected value: m! / (∏ cᵢ!) * ∏_{i>j} (cᵢ - cⱼ) -/
def expected_value (c : Fin (k+1) → ℕ) (m : ℕ) : ℚ :=
  (m.factorial : ℚ) * (∏ i : Fin (k+1), ∏ j : Fin (k+1),
    if j.val < i.val then ((c i : ℚ) - (c j : ℚ)) else 1) /
    (∏ i : Fin (k+1), ((c i).factorial : ℚ))

/-- Convert a function c : Fin (k+1) → ℕ to Finsupp -/
def toFinsupp (c : Fin (k+1) → ℕ) : (Fin (k+1)) →₀ ℕ :=
  ⟨Finset.univ.filter (λ i => c i ≠ 0), c, λ i => by simp⟩

/-- Vandermonde Coefficient Formula (Lemma 3.1):
    Let c₀, ..., cₖ be nonnegative integers and suppose that ∑ᵢ cᵢ = m + (k+1 choose 2),
    where m is a nonnegative integer. Then the coefficient of ∏ᵢ xᵢ^{cᵢ} in the polynomial
    (x₀ + x₁ + ⋯ + xₖ)^m ∏_{i>j} (xᵢ - xⱼ) is
    (m! / ∏ᵢ cᵢ!) ∏_{i>j} (cᵢ - cⱼ).

    Proof (from the paper):
    The product ∏_{k ≥ i > j ≥ 0} (xᵢ - xⱼ) is precisely the Vandermonde determinant
    det(xᵢ^j)_{0 ≤ i ≤ k, 0 ≤ j ≤ k} which is equal to the sum
    ∑_{σ∈S_{k+1}} (-1)^{sign(σ)} ∏_{i=0}^k xᵢ^{σ(i)},
    where S_{k+1} denotes the set of all permutations of the k+1 symbols 0, ..., k.

    It thus follows that the required coefficient, which we denote by C, is given by
    C = ∑_{σ∈S_{k+1}} (-1)^{sign(σ)} m! / ((c₀ - σ(0))!(c₁ - σ(1))!⋯(cₖ - σ(k))!).

    Similarly, the product ∏_{k ≥ i > j ≥ 0} (cᵢ - cⱼ) is the Vandermonde determinant
    det(cᵢ^j)_{0 ≤ i ≤ k, 0 ≤ j ≤ k}.

    For two integers r ≥ 1 and s let (s)_r denote the product s(s-1)⋯(s-r+1) and define
    also (s)_₀ = 1 for all s. Observe that the matrix ((cᵢ)_j)_{0 ≤ i ≤ k, 0 ≤ j ≤ k}
    can be obtained from the matrix (cᵢ^j)_{0 ≤ i ≤ k, 0 ≤ j ≤ k} by subtracting
    appropriate linear combinations of the columns with indices less than j from the
    column indexed by j, for each j = k, k-1, ..., 1. Therefore, these two matrices
    have the same determinant.

    It thus follows that
    (m! / ∏ᵢ cᵢ!) ∏_{i>j} (cᵢ - cⱼ) = (m! / ∏ᵢ cᵢ!) det((cᵢ)_j)_{0 ≤ i ≤ k, 0 ≤ j ≤ k}
    = (m! / ∏ᵢ cᵢ!) ∑_{σ∈S_{k+1}} (-1)^{sign(σ)} (c₀)_{σ(0)}(c₁)_{σ(1)}⋯(cₖ)_{σ(k)}
    = ∑_{σ∈S_{k+1}} (-1)^{sign(σ)} m! / ((c₀ - σ(0))!(c₁ - σ(1))!⋯(cₖ - σ(k))!) = C,
    completing the proof. □
-/
theorem Vandermonde_coefficient_formula (c : Fin (k+1) → ℕ) (m : ℕ)
    (h_sum : ∑ i : Fin (k+1), c i = m + ((k+1).choose 2)) :
    MvPolynomial.coeff (toFinsupp c)
      ((∑ i : Fin (k+1), X i) ^ m *
       ∏ i : Fin (k+1), ∏ j : Fin (k+1), if j < i then (X i - X j) else 1)
    = expected_value c m := by
  sorry
