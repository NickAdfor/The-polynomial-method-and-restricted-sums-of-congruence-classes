import Mathlib

open scoped Finset

variable {R : Type*} [CommRing R]

open MvPolynomial
open Finsupp

/-- Lemma 2.2 :
A multivariate polynomial that vanishes on a large product finset is the zero polynomial. -/
lemma eq_zero_of_eval_zero_at_prod_finset {σ : Type*} [Finite σ] [IsDomain R]
    (P : MvPolynomial σ R) (S : σ → Finset R)
    (Hdeg : ∀ i, P.degreeOf i < #(S i))
    (Heval : ∀ (x : σ → R), (∀ i, x i ∈ S i) → eval x P = 0) :
    P = 0 := by
      exact MvPolynomial.eq_zero_of_eval_zero_at_prod_finset P S Hdeg Heval

variable {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}

/-- Definition of elimination polynomials g_i -/
noncomputable def elimination_polynomials (A : Fin (k + 1) → Finset (ZMod p)) :
    Fin (k + 1) → MvPolynomial (Fin (k + 1)) (ZMod p) :=
  fun i => ∏ a ∈ A i, (MvPolynomial.X i - C a)

noncomputable def reduce_polynomial_degrees (P : MvPolynomial (Fin (k + 1)) (ZMod p))
    (g : Fin (k + 1) → MvPolynomial (Fin (k + 1)) (ZMod p))
    (c : Fin (k + 1) → ℕ) : MvPolynomial (Fin (k + 1)) (ZMod p) :=

  P.support.sum fun m =>
    let coeff := P.coeff m
    let needs_replacement : Finset (Fin (k + 1)) :=
      Finset.filter (fun i => m i > c i) Finset.univ
    if h : needs_replacement.Nonempty then
      let i : Fin (k + 1) := needs_replacement.min' h
      let new_m : (Fin (k + 1)) →₀ ℕ :=
        Finsupp.update m i (m i - (c i + 1))
      coeff • (MvPolynomial.monomial new_m 1) * (MvPolynomial.X i ^ (c i + 1) - g i)
    else
      coeff • MvPolynomial.monomial m 1

lemma reduce_polynomial_degrees_eq (P : MvPolynomial (Fin (k + 1)) (ZMod p))
  (g : Fin (k + 1) → MvPolynomial (Fin (k + 1)) (ZMod p))
  (c : Fin (k + 1) → ℕ) :
  reduce_polynomial_degrees P g c =
    P.support.sum (fun m =>
      let coeff := P.coeff m
      let needs_replacement := Finset.filter (fun i => m i > c i) Finset.univ
      if h : needs_replacement.Nonempty then
        let i := needs_replacement.min' h
        let new_m := Finsupp.update m i (m i - (c i + 1))
        coeff • MvPolynomial.monomial new_m 1 * (MvPolynomial.X i ^ (c i + 1) - g i)
      else
        coeff • MvPolynomial.monomial m 1) := rfl


set_option maxHeartbeats 2000000 in
/-- **Alon-Nathanson-Ruzsa Theorem** (Theorem 2.1)
Proof strategy: Use Lemma 2.2 (eq_zero_of_eval_zero_at_prod_finset) to prove Theorem 2.1

Proof outline:
1. Assume the conclusion is false, i.e., there exists a set E subset Z_p with |E| = m such that restricted sumset subset E
2. Construct the polynomial Q(x_0,...,x_k) = h(x_0,...,x_k) * prod_{e in E} (x_0+...+x_k - e)
   - deg(Q) = deg(h) + m = sum c_i
   - For all (a_0,...,a_k) in prod A_i, we have Q(a_0,...,a_k) = 0
   - The coefficient of monomial prod x_i^{c_i} in Q is nonzero

3. For each i, define g_i(x_i) = prod_{a in A_i} (x_i - a) = x_i^{c_i+1} - sum_j b_ij x_i^j
4. Construct polynomial Q_bar by replacing all occurrences of x_i^{c_i+1} in Q with sum_j b_ij x_i^j
   - For each a_i in A_i, g_i(a_i) = 0, so Q_bar still vanishes on prod A_i
   - deg_{x_i}(Q_bar) <= c_i

5. Apply Lemma 2.2:
   - Q_bar vanishes on prod A_i
   - Degree in each variable <= c_i
   - Therefore Q_bar = 0

6. But the coefficient of prod x_i^{c_i} in Q_bar is the same as in Q:
   - The replacement process doesn't affect this specific monomial
   - By assumption, this coefficient is nonzero in Q
   - Therefore it's nonzero in Q_bar, contradicting Q_bar = 0

Key points:
- Use polynomial replacement technique to reduce degrees to satisfy Lemma 2.2 conditions
- The replacement process preserves the coefficient of the target monomial
- Proof by contradiction
-/
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
  -- Define the restricted sumset S
  set S : Finset (ZMod p) :=
  ((Fintype.piFinset A).filter (fun f => h.eval f ≠ 0)).image (fun f => ∑ i, f i) with hS_def

  -- Step 1: Prove |S| >= m + 1 by contradiction
  have hS_card : S.card ≥ m + 1 := by
    by_contra! H

    have hS_size : S.card ≤ m := by omega
    obtain ⟨E, hE_sub, hE_card⟩ : ∃ E : Multiset (ZMod p), S.val ⊆ E ∧ E.card = m := by
      refine ⟨S.val + Multiset.replicate (m - S.card) (0 : ZMod p),
              Multiset.subset_of_le (by simp), ?_⟩
      simp [hS_size]

    -- Define the polynomial Q
    set sumX : MvPolynomial (Fin (k + 1)) (ZMod p) := ∑ i, MvPolynomial.X i with hsumX_def
    set Q : MvPolynomial (Fin (k + 1)) (ZMod p) :=
      h * (E.map (fun e => sumX - C e)).prod with hQ_def

    -- Q vanishes on prod A_i
    have hQ_zero : ∀ (x : Fin (k + 1) → ZMod p), (∀ i, x i ∈ A i) → eval x Q = 0 := by
      intro x hx
      rw [hQ_def, eval_mul]
      by_cases hh : eval x h = 0
      · simp [hh]
      · have h_sum_in_S : (∑ i, x i) ∈ S := by
          simp [S, Fintype.mem_piFinset]
          refine ⟨x, ⟨hx, hh⟩, rfl⟩
        have h_sum_in_E : (∑ i, x i) ∈ E := hE_sub h_sum_in_S
        have : eval x ((E.map (fun e => sumX - C e)).prod) = 0 := by
          have mem : (sumX - C (∑ i, x i)) ∈ Multiset.map (fun e => sumX - C e) E :=
            Multiset.mem_map.mpr ⟨∑ i, x i, h_sum_in_E, rfl⟩
          have zero_eval : eval x (sumX - C (∑ i, x i)) = 0 := by
            simp [hsumX_def]
          have hprod_eq_zero : (MvPolynomial.eval x) (sumX - C (∑ i, x i)) = 0 := by exact
            zero_eval
          have eval_factor_zero : eval x (sumX - C (∑ i, x i)) = 0 := by exact zero_eval
          have prod_zero :
          (MvPolynomial.eval x) (Multiset.map (fun e => sumX - C e) E).prod = 0 := by
            have : (MvPolynomial.eval x) ((Multiset.map (fun e => sumX - C e) E).prod) =
                  (Multiset.map (fun e => (MvPolynomial.eval x) (sumX - C e)) E).prod := by
                  exact Eq.symm (Multiset.prod_hom' E (MvPolynomial.eval x) fun i ↦ sumX - C i)
            rw [this]
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
          simp_all [S, sumX, Q]
        simp only [this, mul_zero]

    have hQ_total_deg : Q.totalDegree = ∑ i, c i := by
      rw [hQ_def, hsumX_def]
      have h_prod_deg : ((E.map (fun e => sumX - C e)).prod).totalDegree = m := by
        rw [hsumX_def]
        have degree_of_each : ∀ e : ZMod p, (sumX - C e).totalDegree = 1 := by
          intro e
          rw [hsumX_def]
          have : (∑ i : Fin (k + 1), X i - C e) = (∑ i, X i) + (-C e) := by rw [sub_eq_add_neg]
          rw [MvPolynomial.totalDegree]
          apply le_antisymm
          · refine Finset.sup_le fun d hd => ?_
            simp [this] at hd
            have : (d.sum fun x e ↦ e) ≤ 1 := by
              -- Step 1: Coefficient decomposition of sum X_i - C e
              have coeff_sub_eq :
              coeff d (∑ i, X i - C e) = coeff d (∑ i, X i) + -coeff d (C e) := by
                simp [MvPolynomial.coeff_sub]
                exact sub_eq_add_neg (coeff d (∑ i, X i)) (if 0 = d then e else 0)
              have coeff_C_eq : coeff d (C e) = if d = 0 then e else 0 := by
                simp [MvPolynomial.coeff_C]
                simp_all [S, sumX, Q]
                split
                next h_1 =>
                  subst h_1
                  simp_all only [↓reduceIte]
                next h_1 =>
                  simp_all only [↓reduceIte, neg_zero, add_zero, right_eq_ite_iff]
                  intro a
                  subst a
                  simp_all only [not_true_eq_false]
              rw [coeff_C_eq] at coeff_sub_eq
              -- Step 2: d is in the support since its coefficient != 0
              have mem_support : d ∈ (∑ i, X i - C e).support := by
                rw [MvPolynomial.mem_support_iff, coeff_sub_eq]
                simp_all [S, sumX, Q]
              have support_subset :
              (∑ i, X i - C e).support ⊆
                  (Finset.biUnion Finset.univ fun i : Fin (k + 1) => {Finsupp.single i 1})
                  ∪ {0} := by
                intro x hx
                rw [MvPolynomial.mem_support_iff] at hx
                have coeff_eq : coeff x (∑ i, X i - C e) = coeff x (∑ i, X i) - coeff x (C e) := by
                  simp [MvPolynomial.coeff_sub]
                rw [coeff_eq] at hx
                have coeff_sum_eq :
                coeff x (∑ i, X i) = if ∃ i, x = Finsupp.single i 1 then 1 else 0 := by
                  simp [MvPolynomial.coeff_sum]
                  have h :
                  ∑ x_1, coeff x (X x_1) = if ∃ i, x = Finsupp.single i 1 then 1 else 0 := by
                    by_cases h : ∃ i, x = Finsupp.single i 1
                    · rcases h with ⟨i, hi⟩
                      have :
                      ∀ j, (if x = Finsupp.single j 1
                      then (1 : ZMod p) else 0) = if i = j then 1 else 0
                      :=
                      by
                        intro j
                        rw [hi]
                        by_cases h : i = j
                        · subst h
                          simp only [↓reduceIte]
                        · simp [h]
                          rw [@Finsupp.single_eq_single_iff]
                          ring_nf
                          simp_all
                      aesop --run very slow
                    · push_neg at h
                      simp [h]
                      have : ∀ i, coeff x (X i) = 0 := by
                        intro i
                        simp [MvPolynomial.coeff_X']
                        exact fun a ↦ h i (id (Eq.symm a))
                      exact fun i => this i
                  subst hE_card
                  simp_all [S, sumX, Q]
                have coeff_C_eq : coeff x (C e) = if x = 0 then e else 0 := by
                  simp [MvPolynomial.coeff_C]
                  simp_all [S, sumX, Q]
                  split
                  next h_1 =>
                    subst h_1
                    simp_all only [↓reduceIte]
                  next h_1 =>
                    simp_all only [↓reduceIte, sub_zero, neg_zero, add_zero, right_eq_ite_iff]
                    intro a
                    subst a
                    simp_all only [not_true_eq_false]
                by_cases h : ∃ i, x = Finsupp.single i 1
                · rcases h with ⟨i, hi⟩
                  apply Finset.mem_union_left
                  simp [hi]
                  use i
                · rw [Finset.mem_union, Finset.mem_singleton]
                  right
                  have h1 : coeff x (∑ i, X i) = (0 : ZMod p) := by
                    have no_single : ¬∃ i, x = Finsupp.single i 1 := h
                    rw [MvPolynomial.coeff_sum]
                    apply Finset.sum_eq_zero
                    intro i
                    rw [MvPolynomial.coeff_X']
                    split_ifs with h_eq
                    · exfalso
                      have h_eq_symm : x = Finsupp.single i 1 := h_eq.symm
                      exact no_single ⟨i, h_eq_symm⟩
                    · intro a
                      simp_all [S, sumX, Q]
                  rw [h1] at hx
                  rw [coeff_C_eq] at hx
                  by_cases h2 : x = 0
                  · exact h2
                  · simp [h2] at hx
              have :
              d ∈ (Finset.biUnion Finset.univ fun i : Fin (k + 1) => {Finsupp.single i 1}) ∪ {0} :=
                support_subset mem_support
              simp at this
              simp_all only [S, sumX, Q]
              cases this with
              | inl h_1 =>
                subst h_1
                simp_all only [↓reduceIte, sum_zero_index, zero_le]
              | inr h_2 =>
                obtain ⟨w, h_1⟩ := h_2
                subst h_1
                simp_all only [single_eq_zero, one_ne_zero, ↓reduceIte, neg_zero, add_zero,
                  sum_single_index, le_refl]
            exact this
          simp
          let b : (Fin (k + 1)) →₀ ℕ := Finsupp.single (0 : Fin (k + 1)) 1
          refine ⟨b, ?_, ?_⟩
          · have coeff_eq : coeff (Finsupp.single (0 : Fin (k + 1)) 1) (∑ i, X i) = 1 := by
              simp [coeff_sum, coeff_X', Finsupp.single_eq_single_iff]
            rw [show b = Finsupp.single (0 : Fin (k + 1)) 1 by rfl] at *
            have : b = Finsupp.single (0 : Fin (k + 1)) 1 := rfl
            rw [← this]
            have b_ne_zero : b ≠ 0 := by
              intro H
              simp_all [S, sumX, Q, b]
            have : ¬(0 = b) := Ne.symm b_ne_zero
            simp [this]
            change coeff b (∑ i, X i) ≠ 0
            have h1 : (1 : ℕ) ≠ (0 : ZMod p) := by
              simp
            have h : coeff b (∑ i, X i) = (1 : ℕ) := by
              dsimp [b]
              exact coeff_eq
            have : (coeff b (∑ i, X i) : ZMod p) = (1 : ZMod p) := by
              rw [← Nat.cast_one (R := ZMod p)]
              have : (coeff b (∑ i, X i) : ZMod p) = ((coeff b (∑ i, X i) : ℕ) : ZMod p) := by
                simp [coeff_sum, b]
              rw [this, h]
            simp_all
          · simp only [sum_single_index, le_refl, b]
        have h_prod_deg : ((Multiset.map (fun e ↦ ∑ i : Fin (k + 1), X i - C e) E).prod).totalDegree = m := by
          have h1 : ∀ e : ZMod p, (∑ i : Fin (k + 1), X i - C e).totalDegree = 1 := by
            intro e
            simp_all [S, sumX, Q]
          have h2 : (sumX ^ m).totalDegree = m := by
            rw [hsumX_def]
            sorry
          sorry
        exact h_prod_deg
      have h_h_deg : h.totalDegree = (∑ i, c i) - m := by
        exact Nat.eq_sub_of_add_eq' hm
      sorry
    have hQ_coeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) Q ≠ 0 := by
      rw [hQ_def, coeff_mul]
      -- 1. 证明 ∏_{e∈E}(∑X_i - C e) 的最高次项是 (∑X_i)^m
      have leading_term :
          coeff (Finsupp.equivFunOnFinite.symm c) ((Multiset.map (fun e ↦ ∑ i, X i - C e) E).prod) =
          coeff (Finsupp.equivFunOnFinite.symm c) ((∑ i, X i) ^ m) := by
        -- 因为乘积的总次数是 m，且目标单项式的次数是 ∑c_i = m + deg(h)
        -- 所以只有最高次项能贡献到这个单项式
        sorry  -- 需要详细证明这个系数相等

      -- 2. 证明当 d ≠ 0 时，coeff d h = 0 或者 coeff (c-d) (∏...) = 0
      have other_terms_zero : ∀ (d : (Fin (k+1)) →₀ ℕ),
          d ≠ 0 → coeff d h * coeff (Finsupp.equivFunOnFinite.symm c - d)
            ((Multiset.map (fun e ↦ ∑ i, X i - C e) E).prod) = 0 := by
        intro d hd
        -- 如果 deg(d) > 0，那么 deg(c-d) < deg(c) = m + deg(h)
        -- 但 ∏_{e∈E}(∑X_i - C e) 的最高次数是 m，所以 coeff (c-d) (...) = 0
        sorry  -- 需要详细证明

      -- 3. 现在求和简化为只有 d = 0 这一项
      rw [Finset.sum_eq_single (0, Finsupp.equivFunOnFinite.symm c)]
      ·
        have h_const : coeff 0 h = 1 := by
          -- 需要证明 h 的常数项为 1
          sorry

        rw [h_const, one_mul, leading_term, ← hsumX_def]
        -- 现在目标：coeff (equivFunOnFinite.symm c) (sumX ^ m) ≠ 0

        -- 从 h_coeff: coeff c (sumX^m * h) ≠ 0 推出 coeff c (sumX^m) ≠ 0
        rw [coeff_mul] at h_coeff
        have key : coeff 0 h * coeff (equivFunOnFinite.symm c) (sumX ^ m) ≠ 0 := by
          contrapose! h_coeff
          apply Finset.sum_eq_zero
          intro x hx
          rcases x with ⟨d1, d2⟩
          have hx_ne : d1 ≠ 0 := by
            intro h
            sorry
          have hx_zero := other_terms_zero d1 hx_ne
          sorry
        rw [h_const, one_mul] at key
        exact key
      · intro x hx hx'
        rcases x with ⟨d1, d2⟩
        have : d1 + d2 = Finsupp.equivFunOnFinite.symm c :=
          (Finset.mem_antidiagonal.mp hx)
        have hzero :
          coeff d1 h *
            coeff (Finsupp.equivFunOnFinite.symm c - d1)
              ((Multiset.map (fun e ↦ ∑ i, X i - C e) E).prod) = 0 :=
        by
          have hd1 : d1 ≠ 0 := by
            intro h
            apply hx'
            simp [h]
            rw [h, zero_add] at this
            exact this
          exact other_terms_zero d1 hd1
        have hd2 :
          d2 = (Finsupp.equivFunOnFinite.symm c - d1) :=
          by
            rw [tsub_eq_of_eq_add_rev (id (Eq.symm this))]
        have hz := hzero
        simpa [hd2, mul_eq_zero] using hz
      · intro h
        simp [Finset.mem_antidiagonal] at h

    -- Define elimination polynomials g_i
    set g : Fin (k + 1) → MvPolynomial (Fin (k + 1)) (ZMod p) :=
      elimination_polynomials A with hg_def

    -- Construct Q_bar by reducing degrees
    set Q_bar : MvPolynomial (Fin (k + 1)) (ZMod p) :=
      reduce_polynomial_degrees Q g c with hQ_bar_def

    let target := Finsupp.equivFunOnFinite.symm c
    let P := (E.map (fun e => sumX - C e)).prod
    have hQ_bar_zero : ∀ (x : Fin (k + 1) → ZMod p), (∀ i, x i ∈ A i) → eval x Q_bar = 0 := by sorry

    have hQ_bar_deg : ∀ i, Q_bar.degreeOf i ≤ c i := by
      sorry
    have hQ_bar_zero_poly : Q_bar = 0 :=
      _root_.eq_zero_of_eval_zero_at_prod_finset Q_bar A (fun i => by
        have := hQ_bar_deg i
        grind) hQ_bar_zero

    -- But the coefficient of the target monomial in Q_bar is nonzero
    have hQ_bar_coeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) Q_bar ≠ 0 := by
      let target := Finsupp.equivFunOnFinite.symm c
      have h_target_not_replaced : ∀ i, (target i) ≤ c i := by
        intro i
        exact Nat.le_refl (c i)

      have h_coeff_eq : MvPolynomial.coeff target Q_bar = MvPolynomial.coeff target Q := by
        have h_ite : ∀ m ∈ Q.support, m = target →
          (let needs_replacement := Finset.filter (fun i => m i > c i) Finset.univ
          if h : needs_replacement.Nonempty then
            let i := needs_replacement.min' h
            let new_m := Finsupp.update m i (m i - (c i + 1))
            Q.coeff m • MvPolynomial.monomial new_m 1 * (MvPolynomial.X i ^ (c i + 1) - g i)
          else
            Q.coeff m • MvPolynomial.monomial m 1) = Q.coeff m • MvPolynomial.monomial m 1 := by
          intro m hm
          intro a
          subst hE_card a
          simp_all [S, sumX, Q, g, Q_bar, target]

        -- 将 sum 展开，只有 m = target 的贡献才涉及目标单项式
        have sum_eq : MvPolynomial.coeff target Q_bar =
                      Finset.sum Q.support (fun m => if m = target then Q.coeff m else 0) := by
          simp only [Q_bar]
          unfold reduce_polynomial_degrees
          rw [coeff_sum]
          apply Finset.sum_congr rfl
          intros m hm
          let needs_replacement := Finset.filter (fun i => m i > c i) Finset.univ
          by_cases hnr : needs_replacement.Nonempty
          · rw [if_pos]
            rw [MvPolynomial.coeff_mul]
            have target_not_in_branch : ∀ i, target i ≤ c i := h_target_not_replaced
            sorry -- too long
            sorry
          · -- else 分支 monomial = m
            by_cases h_eq : m = target
            · simp [h_eq]
              sorry
            · simp [h_eq, MvPolynomial.coeff_monomial, MulZeroClass.zero_mul]
              sorry


        -- 现在 sum 只剩下 target 自身
        rw [sum_eq]
        simp
        exact fun a ↦ id (Eq.symm a)

      -- Q 中 target 的系数非零，这是假设 h_coeff
      exact h_coeff_eq.symm ▸ hQ_coeff

    -- Contradiction
    rw [hQ_bar_zero_poly] at hQ_bar_coeff
    simp at hQ_bar_coeff

  -- Step 2: Prove m < p first (this is needed for the main argument)
  have hmp : m < p := by
    by_contra! H  -- H: m >= p
    -- If m >= p, use the Frobenius endomorphism property in characteristic p
    have frobenius_identity : ((∑ i : Fin (k + 1), MvPolynomial.X i) ^ p :
    MvPolynomial (Fin (k + 1)) (ZMod p)) = ∑ i, MvPolynomial.X i ^ p := by
      sorry
    sorry
  exact ⟨hS_card, hmp⟩
