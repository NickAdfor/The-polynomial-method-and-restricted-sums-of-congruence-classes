import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Prime.Factorial

open Finsupp
open scoped Finset
open MvPolynomial
open BigOperators


-- 背景与定理2.1
variable {R : Type*} [CommRing R]
-- variable {p : ℕ} [Fact p.Prime]

lemma eq_zero_of_eval_zero_at_prod_finset {σ : Type*} [Finite σ] [IsDomain R]
    (P : MvPolynomial σ R) (S : σ → Finset R)
    (Hdeg : ∀ i, P.degreeOf i < #(S i))
    (Heval : ∀ (x : σ → R), (∀ i, x i ∈ S i) → eval x P = 0) :
    P = 0 := by
      exact MvPolynomial.eq_zero_of_eval_zero_at_prod_finset P S Hdeg Heval

variable {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}

theorem ANR_polynomial_method (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (A : Fin (k + 1) → Finset (ZMod p))
    (c : Fin (k + 1) → ℕ)
    (hA : ∀ i, (A i).card = c i + 1)
    (m : ℕ) (hm : m + h.totalDegree = ∑ i, c i)
    (h_coeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c)
    ((∑ i : Fin (k + 1), MvPolynomial.X i) ^ m * h) ≠ 0) :
    let S : Finset (ZMod p) :=
      (Fintype.piFinset A).filter (fun f => h.eval f ≠ 0) |>.image (fun f => ∑ i, f i)
    S.card ≥ m + 1 ∧ m < p := by
    -- 这里省略定理2.1本身的证明过程
    sorry

-- 辅助引理：
-- 1. 将 Fin 2 上的和转化为二元和
lemma sum_fin_two {M : Type*} [AddCommMonoid M] (f : Fin 2 → M) :
    ∑ i, f i = f 0 + f 1 := by
  rw [Fin.sum_univ_two]



-- 2. 二项式系数在 ZMod p 中非零的条件
lemma binomial_coeff_ne_zero_mod_p (n k : ℕ) (hp : p.Prime) (h_k : k ≤ n) (h_n : n < p) :
    (Nat.choose n k : ZMod p) ≠ 0 := by
  -- 1. 将 ≠ 重写为 ¬ ... = ...
  rw [ne_eq]
  -- 2. 将 ZMod p 中的 = 0 转化为整除关系 (p ∣ n.choose k)
  rw [CharP.cast_eq_zero_iff (ZMod p) p]
  -- 3. 使用反证法：假设 p 能整除 n.choose k
  intro h_dvd
  -- 4. 利用二项式系数整除阶乘的性质： p ∣ n.choose k → p ∣ n!
  have key : n.choose k ∣ n.factorial := by
    have h_eq := Nat.choose_mul_factorial_mul_factorial h_k
    rw [mul_assoc] at h_eq
    rw [mul_comm] at h_eq
    rw [← h_eq]
    exact Nat.dvd_mul_left _ _
  have h_dvd_fact : p ∣ n.factorial := dvd_trans h_dvd key
  -- 5. 利用素数整除阶乘的性质： p ∣ n! ↔ p ≤ n
  rw [Nat.Prime.dvd_factorial] at h_dvd_fact
  · linarith
  exact hp



def sumset {α : Type*} [Add α] [DecidableEq α] (A B : Finset α) : Finset α :=
  (A ×ˢ B).image (fun x => x.1 + x.2)

variable {A B : Finset (ZMod p)}
#check sumset A B


set_option linter.style.longLine false
-- 3. 证明论文中的 "Case 1" (和较小的情况)
lemma cauchy_davenport_small_sum (A B S : Finset (ZMod p)) (hp : p.Prime) (hA : A.Nonempty) (hB : B.Nonempty)
    (h_sum : A.card + B.card ≤ p + 1) (hS : S = sumset A B) : S.card ≥ A.card + B.card - 1 := by
  let k_val := 1 --k=1
  let As : Fin 2 → Finset (ZMod p) := ![A, B]  --Fin 2 表示索引集合 {0,1}，对应 A0,A1​​
  let cs : Fin 2 → ℕ := ![A.card - 1, B.card - 1]
  let h_poly : MvPolynomial (Fin 2) (ZMod p) := 1
  let m := A.card + B.card - 2
  have h_card : ∀ i, (As i).card = cs i + 1 := by -- 证明|Ai|是等于ci+1
    intro i; fin_cases i
    · simp [As, cs]; rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hA.card_pos)]
    · simp [As, cs]; rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hB.card_pos)]
  have h_deg : m + h_poly.totalDegree = ∑ i, cs i := by -- 验证m真的等于∑ci−deg(h)
    simp [h_poly,m,cs]
    rw [show 2 = 1 + 1 by rfl]
    rw [Nat.sub_add_eq]-- 减法分配律x - (y + z) = x - y - z
    have h_A_neg_zero : 1 ≤ A.card := by exact Finset.one_le_card.mpr hA
    have h_B_neg_zero : 1 ≤ B.card := by exact Finset.one_le_card.mpr hB
    rw [Nat.add_comm, Nat.add_sub_assoc h_A_neg_zero, add_comm,← Nat.add_sub_assoc h_B_neg_zero]
  have h_coeff_ne_zero : coeff (equivFunOnFinite.symm cs) ((∑ i : Fin 2, X i) ^ m * h_poly) ≠ 0 := by
    simp [h_poly]
    rw [add_pow]
    rw [coeff_sum]
    rw [Finset.sum_eq_single (cs 0)] -- 锁定唯一非零项 (m_1 = cs 0)
    · -- 【分支 1】 证明主项非零 (你原来的代码逻辑放在这里)
      have h_exp : m - cs 0 = cs 1 := by
        dsimp [m, cs]
        aesop
      rw [h_exp] -- 将指数 m - cs 0 替换为 cs 1
      rw [mul_comm]
      rw [show (↑(m.choose (cs 0)) : MvPolynomial (Fin 2) (ZMod p)) = C (m.choose (cs 0) : ZMod p) by simp]
      rw [MvPolynomial.coeff_C_mul]
      apply mul_ne_zero
      · apply binomial_coeff_ne_zero_mod_p
        · exact hp
        · dsimp [m, cs]; aesop -- 证明 cs 0 ≤ m
        · -- 证明 m < p
          dsimp [m]
          have : A.card + B.card ≤ p + 1 := h_sum
          have h1 : A.card + B.card - 2 ≤ p - 1 := by omega
          have h2 : 0 < p := hp.pos
          have h3 : p - 1 < p := by exact Nat.sub_lt (h2) (Nat.zero_lt_one)
          exact lt_of_le_of_lt h1 h3
      · simp only [X, monomial_pow, monomial_mul]
        rw [coeff_monomial]
        rw [if_pos]
        · rw [one_pow, one_pow, one_mul]; exact one_ne_zero
        · -- 验证索引相等
          ext i; fin_cases i
          · simp [cs]
          · simp [cs]
    · -- 【分支 2】 证明其他项 (b ≠ cs 0) 的系数为 0
      intro b hb_range h_ne
      rw [show (↑(m.choose b) : MvPolynomial (Fin 2) (ZMod p)) = C (m.choose b : ZMod p) by simp]
      rw [mul_comm, coeff_C_mul]
      simp only [X, monomial_pow, monomial_mul]
      rw [coeff_monomial]
      rw [if_neg]
      · simp -- 0 * 任意数 = 0
      · -- 证明：如果索引相等，则 b = cs 0，这将导致矛盾
        intro h_eq
        rw [Finsupp.ext_iff] at h_eq
        specialize h_eq 0
        simp only [Finsupp.add_apply] at h_eq
        simp [cs] at h_eq
        contradiction
    · -- 【分支 3】 证明 cs 0 在范围内 (cs 0 < m + 1)
      intro h_notin
      exfalso -- 既然我们知道它一定在范围内，假设它不在就会导出假
      apply h_notin
      rw [Finset.mem_range]
      dsimp [m, cs]
      have hA_pos : 1 ≤ A.card := Finset.one_le_card.mpr hA
      have hB_pos : 1 ≤ B.card := Finset.one_le_card.mpr hB
      omega
  have h_ANR := ANR_polynomial_method h_poly As cs h_card m h_deg h_coeff_ne_zero
  let S_ANR := (Fintype.piFinset As).filter (fun f => h_poly.eval f ≠ 0) |>.image (fun f => ∑ i, f i)
  have h_card_ge : S_ANR.card ≥ m + 1 := h_ANR.1
  have h_set_eq : S = S_ANR := by
    rw [hS]
    dsimp [S_ANR, sumset]
    have h_eval_ne_zero : ∀ f ∈ Fintype.piFinset As, h_poly.eval f ≠ 0 := by
      intro f _
      simp [h_poly]
    ext z
    simp only [Finset.mem_image, Finset.mem_product]
    constructor
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      let f : Fin 2 → ZMod p := ![a, b]
      refine ⟨f, ?_, ?_⟩
      · rw [Finset.mem_filter, Fintype.mem_piFinset]
        constructor
        · intro i
          fin_cases i
          · simp [f, As]; exact ha
          · simp [f, As]; exact hb
        · simp [h_poly] -- h_poly 是 1
      · rw [sum_fin_two]
        simp [f]
    · -- 方向 2: z ∈ S_ANR → z ∈ sumset A B
      rintro ⟨f, hf, rfl⟩
      rw [Finset.mem_filter, Fintype.mem_piFinset] at hf
      use (f 0, f 1)
      constructor
      · -- 子目标 1: 证明 (f 0, f 1) ∈ A × B
        dsimp
        constructor
        · -- 证明 f 0 ∈ A
          have hf0 := hf.1 0
          simp [As] at hf0
          exact hf0
        · -- 证明 f 1 ∈ B
          have hf1 := hf.1 1
          simp [As] at hf1
          exact hf1
      · -- 子目标 2: 证明 (f 0) + (f 1) = z
        rw [sum_fin_two] -- 利用引理 ∑ f i = f 0 + f 1
  rw [h_set_eq]
  dsimp [m] at h_card_ge
  have hA_ge_1 : 1 ≤ A.card := Finset.one_le_card.mpr hA
  have hB_ge_1 : 1 ≤ B.card := Finset.one_le_card.mpr hB
  omega


-- 4. 完整证明 (包含论文的 Case 2 归约逻辑)
theorem cauchy_davenport (A B S : Finset (ZMod p)) (hp : p.Prime) (hA : A.Nonempty) (hB : B.Nonempty) (hS : S = sumset A B) :
    min p (A.card + B.card - 1) ≤ S.card := by
  by_cases h : A.card + B.card ≤ p + 1
  {
    -- === Case 1: 直接应用上面的引理 ===
    rw [min_eq_right (Nat.sub_le_iff_le_add.mpr h)]
    apply cauchy_davenport_small_sum
    · exact hp
    · exact hA
    · exact hB
    · exact h
    · omega
  }
  {
    -- === Case 2: (Subset Reduction) ===
    rw [not_le] at h -- h : A.card + B.card > p + 1
    rw [min_eq_left]
    · let target := p + 1 - A.card
      -- 验证 target ≤ |B|，这样才能从 B 中取出子集 B'
      have h_target_le_B : target ≤ B.card := by omega
      -- 验证 B' 非空 (需要 |A| ≤ p，这总是成立的)
      have h_target_pos : target > 0 := by
         apply Nat.sub_pos_of_lt
         apply Nat.lt_succ_of_le
         have h_le : A.card ≤ Fintype.card (ZMod p) := Finset.card_le_univ A
         rw [ZMod.card p] at h_le
         exact h_le
      obtain ⟨B', hB'_sub, hB'_card⟩ := Finset.exists_subset_card_eq h_target_le_B
      have hB'_ne : B'.Nonempty := by rw [←Finset.card_pos, hB'_card]; exact h_target_pos
      have h_sum_exact : A.card + B'.card = p + 1 := by
        rw [hB'_card]
        dsimp [target]
        omega

      have h_new_sum_le : A.card + B'.card ≤ p + 1 := le_of_eq h_sum_exact
      have h_lower_bound : (sumset A B').card ≥ p := by
        have step1 := cauchy_davenport_small_sum A B' (sumset A B') Fact.out hA hB'_ne h_new_sum_le rfl
        rw [h_sum_exact] at step1
        norm_num at step1
        exact step1
      have h_subset_sum : sumset A B' ⊆ sumset A B := Finset.add_subset_add_left hB'_sub
      apply Nat.le_trans h_lower_bound
      simp [hS]
      apply Finset.card_le_card h_subset_sum
    · omega
  }
