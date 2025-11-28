import Mathlib

-- If this tactic in `Polynomial` can be used in `MvPolynomial` is not clear.
macro "by_eval" : tactic => `(tactic| (
  apply Polynomial.funext
  intro x
  simp only [eval_sub, eval_add, eval_X, eval_C, eval_smul, eval_mul, eval_natCast, eval_pow, eval_neg, eval_ofNat, eval_one, eval_zero, smul_eq_mul]
  ring
))


open Finsupp

open scoped Finset

variable {R : Type*} [CommRing R]

open MvPolynomial

open Finsupp Function

/-- Lemma 2.2 :
A multivariate polynomial that vanishes on a large product finset is the zero polynomial. -/
lemma eq_zero_of_eval_zero_at_prod_finset {σ : Type*} [Finite σ] [IsDomain R]
    (P : MvPolynomial σ R) (S : σ → Finset R)
    (Hdeg : ∀ i, P.degreeOf i < #(S i))
    (Heval : ∀ (x : σ → R), (∀ i, x i ∈ S i) → eval x P = 0) :
    P = 0 := by
      exact MvPolynomial.eq_zero_of_eval_zero_at_prod_finset P S Hdeg Heval

variable {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}

/- This part is that I try to extract definition of Q out of the main theorem proof,
but it seems not equivalent to the one in the main theorem proof. Maybe a failed trial.
-- 定义 Q 多项式
noncomputable def construct_Q (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (E : Multiset (ZMod p)) : MvPolynomial (Fin (k + 1)) (ZMod p) :=
  let sumX : MvPolynomial (Fin (k + 1)) (ZMod p) := ∑ i, MvPolynomial.X i
  h * (E.map (fun e => sumX - C e)).prod

/- Aristotle found this block to be false. Here is a proof of the negation:

/-
Q 的总次数引理
-/
lemma Q_total_degree (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (c : Fin (k + 1) → ℕ) (m : ℕ) (hm : m = (∑ i, c i) - h.totalDegree)
    (E : Multiset (ZMod p)) (hE_card : E.card = m) :
    (construct_Q h E).totalDegree = ∑ i, c i := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Choose $p = 2$, $k = 1$, and $h = X_0$.
  use 2, by
    exact ⟨ Nat.prime_two ⟩, 1, MvPolynomial.X 0
  generalize_proofs at *;
  use fun _ => 0;
  unfold construct_Q; aesop;

-/
-- Q 的总次数引理
lemma Q_total_degree (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (c : Fin (k + 1) → ℕ) (m : ℕ) (hm : m = (∑ i, c i) - h.totalDegree)
    (E : Multiset (ZMod p)) (hE_card : E.card = m) :
    (construct_Q h E).totalDegree = ∑ i, c i := by
  sorry

-- Q 中目标单项式系数保持非零的引理
lemma Q_coeff_preserved (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (c : Fin (k + 1) → ℕ) (m : ℕ) (E : Multiset (ZMod p)) (hE_card : E.card = m)
    (h_coeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c)
              ((∑ i, MvPolynomial.X i) ^ m * h) ≠ 0) :
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) (construct_Q h E) ≠ 0 := by
  sorry
-/

/-- Definition of elimination polynomials g_i -/
noncomputable def elimination_polynomials (A : Fin (k + 1) → Finset (ZMod p))
    (c : Fin (k + 1) → ℕ) (hA : ∀ i, (A i).card = c i + 1) :
    Fin (k + 1) → MvPolynomial (Fin (k + 1)) (ZMod p) :=
  fun i => ∏ a ∈ A i, (MvPolynomial.X i - C a)

/-- Elimination polynomials vanish on their defining sets -/
lemma elimination_polynomials_vanish (g : Fin (k + 1) → MvPolynomial (Fin (k + 1)) (ZMod p))
    (A : Fin (k + 1) → Finset (ZMod p)) (c : Fin (k + 1) → ℕ) (hA : ∀ i, (A i).card = c i + 1)
    (hg : g = elimination_polynomials A c hA) :
    ∀ (x : Fin (k + 1) → ZMod p) i, x i ∈ A i → eval x (g i) = 0 := by
  intro x i hx
  rw [hg, elimination_polynomials, eval_prod]
  apply Finset.prod_eq_zero hx
  simp

noncomputable def reduce_polynomial_degrees (P : MvPolynomial (Fin (k + 1)) (ZMod p))
    (g : Fin (k + 1) → MvPolynomial (Fin (k + 1)) (ZMod p))
    (c : Fin (k + 1) → ℕ) : MvPolynomial (Fin (k + 1)) (ZMod p) :=
  -- 逐个单项式处理
  P.support.sum fun m =>
    let coeff := P.coeff m
    -- 检查是否需要替换
    let needs_replacement : Finset (Fin (k + 1)) :=
      Finset.filter (fun i => m i > c i) Finset.univ
    if h : needs_replacement.Nonempty then
      -- 使用 min' 来选择第一个需要替换的变量
      let i : Fin (k + 1) := needs_replacement.min' h
      -- 替换 x_i^{m i} 为 x_i^{m i - (c i + 1)} * g_i
      let new_m : (Fin (k + 1)) →₀ ℕ :=
        Finsupp.update m i (m i - (c i + 1))
      coeff • (MvPolynomial.monomial new_m 1) * g i
    else
      coeff • MvPolynomial.monomial m 1


set_option maxHeartbeats 1000000 in
/-- **Alon-Nathanson-Ruzsa Theorem** (Theorem 2.1)
Proof strategy: Use Lemma 2.2 (eq_zero_of_eval_zero_at_prod_finset) to prove Theorem 2.1

Proof outline:
1. Assume the conclusion is false, i.e., there exists a set E ⊆ Z_p with |E| = m such that ⊕ₕ∑Aᵢ ⊆ E
2. Construct the polynomial Q(x₀,...,xₖ) = h(x₀,...,xₖ) · ∏_{e∈E} (x₀+...+xₖ - e)
   - deg(Q) = deg(h) + m = ∑cᵢ
   - For all (a₀,...,aₖ) ∈ ∏Aᵢ, we have Q(a₀,...,aₖ) = 0
   - The coefficient of monomial ∏xᵢ^{cᵢ} in Q is nonzero

3. For each i, define gᵢ(xᵢ) = ∏_{a∈Aᵢ} (xᵢ - a) = xᵢ^{cᵢ+1} - ∑ⱼ bᵢⱼxᵢʲ
4. Construct polynomial Q̅ by replacing all occurrences of xᵢ^{cᵢ+1} in Q with ∑ⱼ bᵢⱼxᵢʲ
   - For each aᵢ ∈ Aᵢ, gᵢ(aᵢ) = 0, so Q̅ still vanishes on ∏Aᵢ
   - deg_{xᵢ}(Q̅) ≤ cᵢ

5. Apply Lemma 2.2:
   - Q̅ vanishes on ∏Aᵢ
   - Degree in each variable ≤ cᵢ
   - Therefore Q̅ ≡ 0

6. But the coefficient of ∏xᵢ^{cᵢ} in Q̅ is the same as in Q:
   - The replacement process doesn't affect this specific monomial
   - By assumption, this coefficient is nonzero in Q
   - Therefore it's nonzero in Q̅, contradicting Q̅ ≡ 0

Key points:
- Use polynomial replacement technique to reduce degrees to satisfy Lemma 2.2 conditions
- The replacement process preserves the coefficient of the target monomial
- Proof by contradiction
-/
theorem ANR_polynomial_method (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (A : Fin (k + 1) → Finset (ZMod p))
    (c : Fin (k + 1) → ℕ)
    (hA : ∀ i, (A i).card = c i + 1)
    (m : ℕ) (hm : m = (∑ i, c i) - h.totalDegree)
    (h_coeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c)
    ((∑ i : Fin (k + 1), MvPolynomial.X i) ^ m * h) ≠ 0) :
    let S : Finset (ZMod p) :=
      (Fintype.piFinset A).filter (fun f => h.eval f ≠ 0) |>.image (fun f => ∑ i, f i)
    S.card ≥ m + 1 ∧ m < p := by
  -- Define the restricted sumset S
  set S : Finset (ZMod p) :=
  ((Fintype.piFinset A).filter (fun f => h.eval f ≠ 0)).image (fun f => ∑ i, f i) with hS_def

  -- Step 1: Prove |S| ≥ m + 1 by contradiction
  have hS_card : S.card ≥ m + 1 := by
    by_contra! H  -- H: S.card < m + 1

    -- Step 1a: Construct a set E of size ≤ m containing S
    have : S.card ≤ m := by omega
    obtain ⟨E, hE_sub, hE_card⟩ : ∃ E : Multiset (ZMod p), S.val ⊆ E ∧ E.card = m := by
      have hS_size : S.card ≤ m := by omega
      refine ⟨S.val + Multiset.replicate (m - S.card) (0 : ZMod p),
              Multiset.subset_of_le (by simp), ?_⟩
      simp [hS_size]

    -- Step 1b: Construct polynomial Q = h * ∏_{e ∈ E} (∑ x_i - e)
    set sumX : MvPolynomial (Fin (k + 1)) (ZMod p) :=
    ∑ i, MvPolynomial.X i with hsumX_def
    set Q : MvPolynomial (Fin (k + 1)) (ZMod p) :=
    h * (E.map (fun e => sumX - C e)).prod with hQ_def

    -- Q vanishes on the Cartesian product of A_i
    have hQ_zero : ∀ (x : Fin (k + 1) → ZMod p), (∀ i, x i ∈ A i) → eval x Q = 0 := by
      intro x hx
      rw [hQ_def]
      simp
      by_cases hh : eval x h = 0
      · left
        exact hh
      · right
        -- Since x ∈ ∏ A_i and h(x) ≠ 0, we have ∑ x_i ∈ S
        have h_sum_in_S : (∑ i, x i) ∈ S := by
          -- `subst` is always from `aesop?`.
          subst hm
          simp_all [S, sumX, Q]
          apply Exists.intro
          · apply And.intro
            on_goal 2 => { rfl
            }
            · simp_all only [implies_true, not_false_eq_true, and_self]
        -- Since S ⊆ E, we have ∑ x_i ∈ E
        have h_sum_in_E : (∑ i, x i) ∈ E := hE_sub h_sum_in_S
        -- So the factor (sumX - C (∑ x_i)) is in the product and evaluates to zero
        have mem : (sumX - C (∑ i, x i)) ∈ Multiset.map (fun e => sumX - C e) E :=
          Multiset.mem_map.mpr ⟨∑ i, x i, h_sum_in_E, rfl⟩
        have zero_eval : eval x (sumX - C (∑ i, x i)) = 0 := by
          simp [hsumX_def]
        have : (sumX - C (∑ i, x i)) ∈ E.map (fun e => sumX - C e) :=
          Multiset.mem_map.mpr ⟨∑ i, x i, h_sum_in_E, rfl⟩
        have hprod_eq_zero : (MvPolynomial.eval x) (sumX - C (∑ i, x i)) = 0 := by
          simp [MvPolynomial.eval_sub, MvPolynomial.eval_C]
          -- `subst` is always from `aesop?`.
          subst hm
          simp_all [S, sumX, Q]
        have eval_factor_zero : eval x (sumX - C (∑ i, x i)) = 0 := by
          simp [sumX, MvPolynomial.eval_sub, MvPolynomial.eval_C, MvPolynomial.eval_X]
        have prod_zero : (MvPolynomial.eval x) (Multiset.map (fun e => sumX - C e) E).prod = 0 := by
          have : (MvPolynomial.eval x) ((Multiset.map (fun e => sumX - C e) E).prod) =
                (Multiset.map (fun e => (MvPolynomial.eval x) (sumX - C e)) E).prod := by
                exact Eq.symm (Multiset.prod_hom' E (MvPolynomial.eval x) fun i ↦ sumX - C i)
          rw [this]
          -- `subst` is always from `aesop?`.
          subst hm
          simp_all [S, sumX, Q]
          obtain ⟨w, h_1⟩ := h_sum_in_S
          obtain ⟨w_1, h_2⟩ := mem
          obtain ⟨left, right⟩ := h_1
          obtain ⟨left_1, right_1⟩ := h_2
          obtain ⟨left, right_2⟩ := left
          apply Exists.intro
          · apply And.intro
            · apply h_sum_in_E
            · simp_all only [sub_self]
        rw [prod_zero]

    -- Total degree of Q is ∑ c_i. Aristotle proved the extract lemma wrong, why?
    have hQ_total_deg : Q.totalDegree = ∑ i, c i := by sorry

    -- The target monomial has nonzero coefficient in Q
    have hQ_coeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) Q ≠ 0 := by
      rw [hQ_def]
      rw [← @monomial_zero']
      rw [← @cons_zero_zero]
      rw [hsumX_def]
      rw [@Finset.sum_fin_eq_sum_range]
      -- Need to show that multiplying by ∏ (sumX - e) doesn't kill the target coefficient
      -- This requires detailed coefficient analysis
      sorry

    -- Step 1c: Define elimination polynomials g_i(x_i) = ∏_{a ∈ A_i} (x_i - a)
    set g : Fin (k + 1) → MvPolynomial (Fin (k + 1)) (ZMod p) :=
      fun i => ∏ a ∈ A i, (MvPolynomial.X i - C a) with hg_def

    -- Step 1d: Construct Q̅ by replacing x_i^{c_i+1} terms with lower degree expressions
    set Q_bar : MvPolynomial (Fin (k + 1)) (ZMod p) :=
      -- Implementation of polynomial replacement algorithm needed here.
      -- Can `reduce_polynomial_degrees` used?
      sorry with hQ_bar_def

    -- Q̅ still vanishes on the Cartesian product of A_i
    have hQ_bar_zero : ∀ (x : Fin (k + 1) → ZMod p), (∀ i, x i ∈ A i) → eval x Q_bar = 0 := by
      intro x hx
      -- For each i, g_i(x_i) = 0 when x_i ∈ A_i
      have hg_zero : ∀ i, eval x (g i) = 0 := by
        intro i
        rw [hg_def, eval_prod]
        apply Finset.prod_eq_zero (hx i)
        simp
      sorry  -- Need to show the replacement preserves vanishing property

    -- Each variable in Q̅ has degree ≤ c_i
    have hQ_bar_deg : ∀ i, Q_bar.degreeOf i ≤ c i := by
      intro i
      -- The replacement process ensures we never exceed degree c_i in variable i
      sorry

    -- Step 1e: Apply Lemma 2.2 to show Q̅ ≡ 0
    have hQ_bar_zero_poly : Q_bar = 0 := sorry

    -- Step 1f: Contradiction - target monomial has nonzero coefficient in Q̅
    have hQ_bar_coeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) Q_bar ≠ 0 := by
      -- The replacement process doesn't affect the coefficient of ∏ x_i^{c_i}
      sorry

    rw [hQ_bar_zero_poly] at hQ_bar_coeff
    simp at hQ_bar_coeff

  -- Step 2: Prove m < p first (this is needed for the main argument)
  have hmp : m < p := by
    by_contra! H  -- H: m ≥ p
    -- If m ≥ p, use the Frobenius endomorphism property in characteristic p
    have frobenius_identity : ((∑ i : Fin (k + 1), MvPolynomial.X i) ^ p :
    MvPolynomial (Fin (k + 1)) (ZMod p)) = ∑ i, MvPolynomial.X i ^ p := by
      subst hm
      simp_all only [ne_eq, ge_iff_le, S]
      exact sum_pow_char p Finset.univ X

    -- This changes the structure of (∑ X_i)^m when m ≥ p, leading to contradiction with h_coeff
    subst hm
    simp_all only [ne_eq, ge_iff_le, S]
    sorry  -- Detailed argument needed here


  exact ⟨hS_card, hmp⟩

open Finset Function Monoid MulOpposite Subgroup
open scoped Pointwise

variable {G α : Type*}

variable [Group α] [DecidableEq α] {x y : Finset α × Finset α} {s t : Finset α}

/-- A generalization of the Cauchy-Davenport Theorem (Theorem 1.1) to  ZMod p. -/
theorem cauchy_davenport {p : ℕ} (hp : Nat.Prime p)
{s t : Finset (ZMod p)} (hs : s.Nonempty) (ht : t.Nonempty) :
  min p (#s + #t - 1) ≤ #(s + t) := by exact ZMod.cauchy_davenport hp hs ht
