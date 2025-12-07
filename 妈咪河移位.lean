-- One cannot use #min_imports. I don't know why. Something happens in `bound`.
import Mathlib

open scoped Finset

variable {R : Type*} [CommRing R]
variable {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}

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

/-- Definition of elimination polynomials g_i -/
noncomputable def elimination_polynomials (A : Fin (k + 1) → Finset (ZMod p)) :
    Fin (k + 1) → MvPolynomial (Fin (k + 1)) (ZMod p) :=
  fun i => ∏ a ∈ A i, (MvPolynomial.X i - C a)

/-- Reduction of polynomial degrees -/
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

/-- The sum of variables polynomial -/
noncomputable def sumX_polynomial : MvPolynomial (Fin (k + 1)) (ZMod p) :=
  ∑ i, MvPolynomial.X i

/-- The restricted sumset S from the ANR theorem -/
def restricted_sumset (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (A : Fin (k + 1) → Finset (ZMod p)) : Finset (ZMod p) :=
  ((Fintype.piFinset A).filter (fun f => h.eval f ≠ 0)).image (fun f => ∑ i, f i)

/-- The polynomial Q = h * ∏_{e∈E} (∑X_i - e) -/
noncomputable def construction_polynomial
    (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (E : Multiset (ZMod p)) :
    MvPolynomial (Fin (k + 1)) (ZMod p) :=
  h * (E.map (fun e => sumX_polynomial - C e)).prod

/-- The construction of E from S when |S| ≤ m -/
def extend_to_size (S : Finset (ZMod p)) (m : ℕ):
    Multiset (ZMod p) :=
  S.val + Multiset.replicate (m - S.card) (0 : ZMod p)

/-- Alternative name for clarity. Here use k explicitly. -/
noncomputable def product_polynomial (k : ℕ) (E : Multiset (ZMod p)) :
    MvPolynomial (Fin (k + 1)) (ZMod p) :=
  (E.map (fun e => sumX_polynomial - C e)).prod

/-- Lemma: construction_polynomial vanishes on ∏ A_i -/
lemma construction_polynomial_vanishes
    (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (A : Fin (k + 1) → Finset (ZMod p))
    (E : Multiset (ZMod p))
    (hE_sub : (restricted_sumset h A).val ⊆ E) :
    ∀ (x : Fin (k + 1) → ZMod p), (∀ i, x i ∈ A i) →
      eval x (h * (E.map (fun e => sumX_polynomial - C e)).prod) = 0 := by
  intro x hx
  rw [eval_mul]
  by_cases hh : eval x h = 0
  · simp [hh]
  · have h_sum_in_S : (∑ i, x i) ∈ restricted_sumset h A := by
      dsimp [restricted_sumset]
      simp_all only [Finset.mem_image, Finset.mem_filter, Fintype.mem_piFinset]
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {rfl}
        · simp_all only [implies_true, not_false_eq_true, and_self]
    have h_sum_in_E : (∑ i, x i) ∈ E := hE_sub h_sum_in_S
    have h_prod_zero : eval x ((E.map (fun e => sumX_polynomial - C e)).prod) = 0 := by
      have factor_zero : eval x (sumX_polynomial - C (∑ i, x i)) = 0 := by
        simp [sumX_polynomial]
      have mem : sumX_polynomial - C (∑ i, x i) ∈
          (show Multiset (MvPolynomial (Fin (k + 1)) (ZMod p)) from
            E.map (fun e => sumX_polynomial - C e)) :=
        Multiset.mem_map.mpr ⟨∑ i, x i, h_sum_in_E, rfl⟩
      -- Apply the lemma that states if a multiset contains a zero element, then its product is zero.
      have h_prod_zero : ∀ {m : Multiset (MvPolynomial (Fin (k + 1)) (ZMod p))}, (∃ f ∈ m, MvPolynomial.eval x f = 0) → MvPolynomial.eval x (Multiset.prod m) = 0 := by
        -- If there exists an element in the multiset that evaluates to zero at x, then the product of the multiset also evaluates to zero at x.
        intros m hm
        obtain ⟨f, hf_mem, hf_zero⟩ := hm
        have h_prod_zero : MvPolynomial.eval x (Multiset.prod m) = MvPolynomial.eval x f * MvPolynomial.eval x (Multiset.prod (Multiset.erase m f)) := by
          simp only [← eval_mul, Multiset.prod_erase hf_mem]
        rw [h_prod_zero, hf_zero, MulZeroClass.zero_mul]
      exact h_prod_zero ⟨_, mem, factor_zero⟩
    simp [h_prod_zero]

/-- The product polynomial ∏_{e∈E} (∑X_i - C e) is always nonzero -/
lemma product_polynomial_ne_zero (k : ℕ) (E : Multiset (ZMod p)) :
    product_polynomial k E ≠ 0 := by
      by_contra h
      by_cases hE : E.card = 0 <;> simp_all +decide [product_polynomial]
      obtain ⟨a, haE, ha⟩ := h
      replace ha := congr_arg (MvPolynomial.eval (fun i => if i = 0 then a + 1 else 0)) ha
      norm_num [sumX_polynomial] at ha

/-- Lemmas about total degree of sumX -/
lemma totalDegree_sumX_sub_C_first {p k : ℕ} [Fact (Nat.Prime p)] (a : ZMod p) :
    (sumX_polynomial - C a : MvPolynomial (Fin (k + 1)) (ZMod p)).totalDegree = 1 := by
      refine' le_antisymm _ _
      · refine' le_trans (MvPolynomial.totalDegree_sub _ _) _
        -- The total degree of a sum of polynomials is less than or equal to the maximum of the total degrees of the summands.
        have h_total_degree_sum : ∀ (s : Finset (Fin (k + 1))), (∑ i ∈ s, MvPolynomial.X i : MvPolynomial (Fin (k + 1)) (ZMod p)).totalDegree ≤ 1 := by
          -- The total degree of a sum of polynomials is less than or equal to the maximum of their total degrees.
          have h_sum_deg : ∀ (s : Finset (Fin (k + 1))), (∑ i ∈ s, MvPolynomial.X i : MvPolynomial (Fin (k + 1)) (ZMod p)).totalDegree ≤ Finset.sup s (fun i => (MvPolynomial.X i : MvPolynomial (Fin (k + 1)) (ZMod p)).totalDegree) := by
            exact fun s => totalDegree_finset_sum s fun i => X i
          intro s
          simp_all only [totalDegree_X]
          exact le_trans (h_sum_deg s) (Finset.sup_le fun i hi => le_rfl)
        simp_all only [totalDegree_C, zero_le, sup_of_le_left, ge_iff_le]
        apply h_total_degree_sum
      · refine' le_trans _ (Finset.le_sup <| show Finsupp.single 0 1 ∈ (∑ i : Fin (k + 1), MvPolynomial.X i - MvPolynomial.C a |> MvPolynomial.support) from _) <;> norm_num
        rw [MvPolynomial.coeff_sum] ;
        simp_all only [coeff_single_X, true_and, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        split at a_1
        next h => simpa using congr_arg (fun f => f 0) h.symm
        next h => simp_all only [sub_zero, one_ne_zero]

/-- Another version of the previous lemma -/
lemma totalDegree_sumX_sub_C_second (e : ZMod p) :
    totalDegree (∑ i : Fin (k + 1), X i - C e) = 1 := by
  have : (∑ i : Fin (k + 1), X i - C e) = (sumX_polynomial : MvPolynomial (Fin (k + 1)) (ZMod p)) - C e := by
    simp [sumX_polynomial]
  rw [this]
  exact totalDegree_sumX_sub_C_first e

/-- The total degree of the product polynomial ∏_{e∈E} (∑X_i - C e) is equal to |E| （Induction steps from J.J. Zhang) -/
lemma totalDegree_prod_sumX_sub_C_eq_card (E : Multiset (ZMod p)) :
    ((Multiset.map (fun e ↦ ∑ i : Fin (k + 1), X i - C e) E).prod).totalDegree = E.card := by
  induction E using Multiset.induction_on with
  | empty => simp
  | cons x E ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    rw [totalDegree_mul_of_isDomain]
    · have foo : ∀ e : ZMod p, (∑ i : Fin (k + 1), X i - C e).totalDegree = 1 := fun e => totalDegree_sumX_sub_C_second e
      rw [ih, foo, add_comm]
    · simp only [ne_eq, sub_eq_zero]
      intro rid
      have := congr($(rid).coeff (fun₀ | 0 => 1))
      simp only [coeff_sum, coeff_single_X, true_and, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, coeff_C] at this
      rw [if_neg] at this
      · norm_num at this
      · rw [eq_comm, Finsupp.single_eq_zero]
        norm_num
    · intro rid
      rw [Multiset.prod_eq_zero_iff] at rid
      simp only [Multiset.mem_map] at rid
      obtain ⟨a, a_mem, rid⟩ := rid
      have := congr($(rid).coeff (fun₀ | 0 => 1))
      simp only [coeff_sub, coeff_sum, coeff_single_X, true_and, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, coeff_C, coeff_zero] at this
      rw [if_neg] at this
      · norm_num at this
      · rw [eq_comm, Finsupp.single_eq_zero]
        norm_num

-- How can one lower the maxHeartbeats?
set_option maxHeartbeats 2000000 in
/-- The total degree of the construction polynomial is equal to the sum of c_i -/
lemma construction_polynomial_totalDegree
    (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (h_ne_zero : h ≠ 0)
    (c : Fin (k + 1) → ℕ)
    (m : ℕ)
    (E : Multiset (ZMod p))
    (hm : m + h.totalDegree = ∑ i, c i)
    (hE_card : E.card = m)
    (h_prod_ne_zero : product_polynomial k E ≠ 0) :
    (construction_polynomial h E).totalDegree = ∑ i, c i := by
  have h_prod_deg :
      (show MvPolynomial (Fin (k + 1)) (ZMod p) from
        (E.map (fun e => sumX_polynomial - C e)).prod).totalDegree = m := by
    dsimp [sumX_polynomial]
    have degree_of_each : ∀ e : ZMod p,
        (sumX_polynomial - C e : MvPolynomial (Fin (k + 1)) (ZMod p)).totalDegree = 1 := by
      intro e
      dsimp [sumX_polynomial]
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
            simp only [coeff_C]
            simp_all only [ne_eq, coeff_add, coeff_neg, coeff_C]
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
            simp_all only [ne_eq, coeff_add, coeff_neg, coeff_C, not_false_eq_true]
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
                  aesop
                · push_neg at h
                  simp [h]
                  have : ∀ i, coeff x (X i) = 0 := by
                    intro i
                    simp [MvPolynomial.coeff_X']
                    exact fun a ↦ h i (id (Eq.symm a))
                  exact fun i => this i
              simp_all only [ne_eq, coeff_add, coeff_neg, coeff_C, MvPolynomial.mem_support_iff]
            have coeff_C_eq : coeff x (C e) = if x = 0 then e else 0 := by
              simp only [coeff_C]
              simp_all only [ne_eq, coeff_add, coeff_neg, coeff_C, MvPolynomial.mem_support_iff, not_false_eq_true]
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
                  simp_all only [ne_eq, coeff_add, coeff_neg, coeff_C, MvPolynomial.mem_support_iff, ↓reduceIte,
                    not_false_eq_true, not_exists, Finset.mem_univ]
              rw [h1] at hx
              rw [coeff_C_eq] at hx
              by_cases h2 : x = 0
              · exact h2
              · simp [h2] at hx
          have :
          d ∈ (Finset.biUnion Finset.univ fun i : Fin (k + 1) => {Finsupp.single i 1}) ∪ {0} :=
            support_subset mem_support
          simp at this
          simp_all only [ne_eq, coeff_add, coeff_neg, coeff_C, MvPolynomial.mem_support_iff, Finset.union_singleton,
            ge_iff_le, not_false_eq_true]
          cases this with
          | inl h_1 =>
            subst h_1
            simp_all only [↓reduceIte, sum_zero_index, zero_le]
          | inr h_2 =>
            obtain ⟨w, h_1⟩ := h_2
            subst h_1
            simp_all only [single_eq_zero, one_ne_zero, ↓reduceIte, ite_eq_right_iff, neg_zero, add_zero,
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
          simp_all only [ne_eq, single_eq_zero, one_ne_zero, b]
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
        simp_all only [ne_eq]
        apply degree_of_each
      -- Apply the lemma that the total degree of a product is the sum of the total degrees.
      have h_total_degree : ∀ (s : Multiset (MvPolynomial (Fin (k + 1)) (ZMod p))), (∀ p ∈ s, p.totalDegree = 1) → s.prod.totalDegree = s.card := by
        bound
        induction s using Multiset.induction <;> aesop
        -- Apply the lemma that the total degree of a product is the sum of the total degrees, given that both factors are non-zero.
        have h_total_degree_mul : ∀ (f g : MvPolynomial (Fin (k + 1)) (ZMod p)), f ≠ 0 → g ≠ 0 → (f * g).totalDegree = f.totalDegree + g.totalDegree := by
          exact fun f g a a_3 => totalDegree_mul_of_isDomain a a_3
        by_cases h : a_1 = 0 <;> by_cases h' : s.prod = 0 <;> simp_all +decide [add_comm]
        rw [eq_comm] at a_2
        simp_all only [Multiset.card_eq_zero, Multiset.notMem_zero, IsEmpty.forall_iff, implies_true]
      rw [h_total_degree] <;> aesop
    exact h_prod_deg
  have h_h_deg : h.totalDegree = (∑ i, c i) - m := by
    exact Nat.eq_sub_of_add_eq' hm
  -- By definition of construction_polynomial, we have construction_polynomial h E = h * product_polynomial k E.
  have h_construction_eq : construction_polynomial h E = h * product_polynomial k E := by
    exact rfl
  -- Apply the property that the total degree of a product of two polynomials is the sum of their total degrees.
  have h_total_deg : (h * product_polynomial k E).totalDegree = h.totalDegree + (product_polynomial k E).totalDegree := by
    exact totalDegree_mul_of_isDomain h_ne_zero h_prod_ne_zero
  subst h_prod_deg
  simp_all only [ne_eq]
  -- Apply the hypothesis `hm` directly to conclude the proof.
  convert hm using 1
  exact
    Nat.add_comm (∑ i, c i - (Multiset.map (fun e => sumX_polynomial - C e) E).prod.totalDegree)
      (product_polynomial k E).totalDegree

open MvPolynomial Finsupp
open scoped BigOperators

/-- The coefficient of a term of maximal degree in the product $\prod (S - e)$ is the same as in $S^{|E|}$. -/
lemma coeff_prod_sumX_minus_C_eq_coeff_sumX_pow_of_degree_eq
    {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}
    (E : Multiset (ZMod p)) (x : (Fin (k+1)) →₀ ℕ) (hx : ∑ i, x i = Multiset.card E) :
    MvPolynomial.coeff x ((E.map (fun e => (∑ i : Fin (k+1), MvPolynomial.X i) - MvPolynomial.C e)).prod) =
    MvPolynomial.coeff x ((∑ i : Fin (k+1), MvPolynomial.X i) ^ Multiset.card E) := by
  revert x
  induction' E using Multiset.induction with a E ih <;> aesop
  rw [pow_succ']
  simp +decide [sub_mul, mul_assoc, MvPolynomial.coeff_mul]
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl] ; aesop
  · rw [MvPolynomial.coeff_sum]
    simp_all only [coeff_zero_X, Finset.sum_const_zero, zero_mul, zero_sub, neg_eq_zero, mul_eq_zero]
    refine' Or.inr (_)
    rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt]
    refine' lt_of_le_of_lt (MvPolynomial.totalDegree_multiset_prod _) _
    refine' lt_of_le_of_lt (Multiset.sum_le_card_nsmul _ _ _) _
    exact 1
    · intro x a_1
      simp_all only [Multiset.map_map, Function.comp_apply, Multiset.mem_map]
      obtain ⟨w, h⟩ := a_1
      obtain ⟨left, right⟩ := h
      subst right
      norm_num [MvPolynomial.totalDegree]
      intro b hb; contrapose! hb; simp_all +decide [MvPolynomial.coeff_sum, MvPolynomial.coeff_X']
      rw [Finset.card_eq_zero.mpr] <;> aesop
    · rw [Finset.sum_subset (Finset.subset_univ snd.support)] <;> aesop
  · simp_all +decide [Finset.sum_add_distrib]
    by_cases h_snd : ∑ i, snd i = E.card
    · exact Or.inl <| ih snd h_snd
    · right
      rw [MvPolynomial.coeff_sum, Finset.sum_eq_zero]
      intro x a_1
      simp_all only [Finset.mem_univ]
      -- Since $fst \neq Finsupp.single x 1$, the coefficient of $fst$ in $X x$ is zero.
      have h_coeff_zero : fst ≠ Finsupp.single x 1 := by
        intro H; simp_all +decide [Finsupp.single_apply]
        exact h_snd (by linarith)
      rw [MvPolynomial.coeff_X']
      simp_all only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false]
      apply Aesop.BuiltinRules.not_intro
      intro a_1
      subst a_1
      simp_all only [univ_sum_single_apply, not_true_eq_false]

-- Also, lower the maxHeartbeats!!!
set_option maxHeartbeats 2000000 in
/-- The coefficient of a specific term in the construction polynomial is non-zero under certain conditions. -/
lemma construction_polynomial_coeff_target_generalized
    (h : MvPolynomial (Fin (k + 1)) (ZMod p))
    (c : Fin (k + 1) → ℕ) (m : ℕ) (hm : m + h.totalDegree = ∑ i, c i)
    (h_coeff : coeff (Finsupp.equivFunOnFinite.symm c) ((∑ i, X i) ^ m * h) ≠ 0)
    (E : Multiset (ZMod p)) (hE_card : E.card = m)
    (coeff_prod_sumX_minus_C_target :
      coeff (Finsupp.equivFunOnFinite.symm c) ((E.map (fun e => (∑ i, X i) - C e)).prod) =
      coeff (Finsupp.equivFunOnFinite.symm c) ((∑ i, X i) ^ m))
    (other_terms_vanish : ∀ (d : (Fin (k + 1)) →₀ ℕ), d ≠ 0 →
      coeff d h * coeff (Finsupp.equivFunOnFinite.symm c - d)
        ((E.map (fun e => (∑ i, X i) - C e)).prod) = 0)
    (h_constant_term_nonzero : coeff 0 h ≠ 0) :
    coeff (Finsupp.equivFunOnFinite.symm c) (construction_polynomial h E) ≠ 0 := by
      -- By combining the results from `coeff_prod_sumX_minus_C_target` and `other_terms_vanish`, we can conclude that the coefficient of $c$ in the product is equal to the coefficient of $c$ in $S^m$ times the constant term of $h$.
      have h_final : MvPolynomial.coeff ((Finsupp.equivFunOnFinite.symm : (Fin (k + 1) → ℕ) → Fin (k + 1) →₀ ℕ) c) (construction_polynomial h E) = MvPolynomial.coeff ((Finsupp.equivFunOnFinite.symm : (Fin (k + 1) → ℕ) → Fin (k + 1) →₀ ℕ) c) (Multiset.prod (Multiset.map (fun e => (∑ i, MvPolynomial.X i) - MvPolynomial.C e) E)) * MvPolynomial.coeff 0 h := by
        rw [construction_polynomial, MvPolynomial.coeff_mul]
        rw [Finset.sum_eq_single (0, (Finsupp.equivFunOnFinite.symm c))] <;> aesop
        · rw [mul_comm, ← coeff_prod_sumX_minus_C_target]
          rfl
        · by_cases h : fst = 0 <;> specialize other_terms_vanish fst <;> aesop
          rw [← a, add_tsub_cancel_left] at h_3 ; aesop
      contrapose! h_coeff; simp_all +decide [mul_comm]
      rw [MvPolynomial.coeff_mul]
      rw [Finset.sum_eq_single (0, (Finsupp.equivFunOnFinite.symm c))] <;> aesop
      by_cases h_fst : fst = 0 <;> specialize other_terms_vanish fst <;> aesop
      contrapose! h_2
      convert h_2.2 using 1
      rw [← a, add_tsub_cancel_left]
      convert coeff_prod_sumX_minus_C_eq_coeff_sumX_pow_of_degree_eq E snd _ using 1
      replace a := congr_arg (fun x => ∑ i, x i) a ; aesop
      simp_all +decide [Finset.sum_add_distrib]
      have h_deg_snd : ∑ i, snd i ≤ E.card := by
        contrapose! right
        rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt]
        refine' lt_of_le_of_lt _ (lt_of_lt_of_le right _)
        · induction' E.card with n ih <;> simp_all +decide [pow_succ]
          refine' le_trans (MvPolynomial.totalDegree_mul _ _) (add_le_add ih _)
          norm_num [MvPolynomial.totalDegree]
          -- Since the sum of X_i's is just the polynomial where each term is X_i, any non-zero coefficient of this polynomial must be one of the X_i's.
          intro b hb_nonzero
          have hb_X : ∃ i, b = Finsupp.single i 1 := by
            simp_all +decide [MvPolynomial.coeff_sum, MvPolynomial.coeff_X']
            obtain ⟨i, hi⟩ := Finset.nonempty_of_ne_empty (by aesop_cat : (Finset.filter (fun x => (Finsupp.single x 1) = b) Finset.univ) ≠ ∅) ; use i; simp_all only [Finset.mem_filter,
              Finset.mem_univ, true_and]
          simp_all only [ge_iff_le]
          obtain ⟨w, h_1⟩ := hb_X
          subst h_1
          simp_all only [sum_single_index, le_refl]
        · rw [Finset.sum_subset (show snd.support ⊆ Finset.univ from Finset.subset_univ _)] ;
          intro x a_1 a_2
          simp_all only [Finset.mem_univ, Finsupp.mem_support_iff, ne_eq, Decidable.not_not]
      linarith [show h.totalDegree ≥ ∑ i, fst i from Finset.le_sup (f := fun s => s.sum fun x e => e) (Finsupp.mem_support_iff.mpr left) |> le_trans (by simp +decide [Finsupp.sum_fintype])]

noncomputable section AristotleLemmas

set_option maxHeartbeats 2000000 in
/-- The elimination polynomial $g_i$ for a given index $i$ and set $A_i$ -/
lemma elimination_polynomial_properties (A : Fin (k + 1) → Finset (ZMod p)) (i : Fin (k + 1))
    (h_card : (A i).card > 0) :
    let g := elimination_polynomials A i
    g.degreeOf i = (A i).card ∧
    coeff (Finsupp.single i ((A i).card)) g = 1 ∧
    (∀ x, x i ∈ A i → eval x g = 0) ∧
    (g - X i ^ (A i).card).totalDegree < (A i).card := by
      -- The degree of $g_i$ is $|A_i|$ because it is a product of $|A_i|$ linear terms.
      have h_deg : (elimination_polynomials A i).degreeOf i = #(A i) := by
        unfold elimination_polynomials
        rw [MvPolynomial.degreeOf_eq_sup]
        -- The leading coefficient of the product of linear factors is 1.
        have h_leading_coeff : (MvPolynomial.coeff (Finsupp.single i #(A i)) (∏ a ∈ A i, (MvPolynomial.X i - MvPolynomial.C a))) = 1 := by
          induction' (A i) using Finset.induction <;> aesop
          norm_num [sub_mul, MvPolynomial.coeff_mul]
          rw [Finset.sum_eq_single (Finsupp.single i 1, Finsupp.single i (Finset.card s))]
          · rw [Finset.sum_eq_single (0, Finsupp.single i (Finset.card s) + Finsupp.single i 1)] <;> aesop
            erw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt] ; aesop
            -- The total degree of the product of linear terms is the sum of the degrees of the individual terms.
            have h_total_degree : (∏ a ∈ s, (MvPolynomial.X i - MvPolynomial.C a)).totalDegree ≤ s.card := by
              have h_total_degree : ∀ a ∈ s, (MvPolynomial.X i - MvPolynomial.C a).totalDegree ≤ 1 := by
                intro a ha; rw [MvPolynomial.totalDegree]
                simp_all only [Finset.sup_le_iff, MvPolynomial.mem_support_iff, coeff_sub, coeff_C, ne_eq]
                intro b a_4
                split at a_4
                next h =>
                  subst h
                  simp_all only [coeff_zero_X, zero_sub, neg_eq_zero, sum_zero_index, zero_le]
                next h =>
                  simp_all only [sub_zero]
                  rw [MvPolynomial.coeff_X'] at a_4
                  simp_all only [ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not]
                  subst a_4
                  simp_all only [sum_single_index, le_refl]
              have h_total_degree : ∀ {S : Finset (ZMod p)}, (∀ a ∈ S, (MvPolynomial.X i - MvPolynomial.C a).totalDegree ≤ 1) → (∏ a ∈ S, (MvPolynomial.X i - MvPolynomial.C a)).totalDegree ≤ S.card := by
                intros S hS; induction S using Finset.induction <;> aesop
                exact le_trans (MvPolynomial.totalDegree_mul _ _) (by linarith)
              exact h_total_degree ‹_›
            refine' lt_of_le_of_lt h_total_degree _
            rw [Finset.sum_eq_single i] <;> aesop
          · intro b a_3 a_4
            simp_all only [Finset.mem_antidiagonal, ne_eq, mul_eq_zero]
            obtain ⟨fst, snd⟩ := b
            simp_all only [Prod.mk.injEq, not_and]
            rw [MvPolynomial.coeff_X']
            simp_all only [ite_eq_right_iff, one_ne_zero, imp_false]
            contrapose! a_4
            simp_all only [ne_eq, true_and]
            obtain ⟨left, right⟩ := a_4
            subst left
            ext j; replace a_3 := congr_arg (fun f => f j) a_3
            simp_all only [Finsupp.coe_add, Pi.add_apply]
            rw [add_comm] at a_3
            simp_all only [Nat.add_right_cancel_iff]
          · simp +decide [add_comm, Finsupp.single_apply]
        refine' le_antisymm _ _
        · simp_all +decide
          intro b hb
          contrapose! hb
          rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt]
          refine' lt_of_le_of_lt _ _
          exact (A i |> Finset.card)
          · induction' (A i) using Finset.induction <;> aesop
            refine' le_trans (MvPolynomial.totalDegree_mul _ _) _
            refine' le_trans (add_le_add (MvPolynomial.totalDegree_sub _ _) a_2) _
            norm_num [add_comm, MvPolynomial.totalDegree_X]
          · exact lt_of_lt_of_le hb (Finset.single_le_sum (fun a _ => Nat.zero_le (b a)) (by
          simp_all only [Finsupp.mem_support_iff, ne_eq]
          apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [not_lt_zero']))
        · refine' le_trans _ (Finset.le_sup <| show Finsupp.single i (# (A i)) ∈ _ from _) <;> aesop
      refine' ⟨h_deg, _, _, _⟩
      · -- The leading coefficient of $g_i$ is 1 because it is a product of linear terms with leading coefficient 1.
        have h_leading_coeff : ∀ (s : Finset (ZMod p)), (∏ a ∈ s, (MvPolynomial.X i - MvPolynomial.C a)).coeff (Finsupp.single i (s.card)) = 1 := by
          intro s
          induction' s using Finset.induction with a s ha ih
          · simp +decide [MvPolynomial.coeff_one]
          · simp_all +decide [Finset.prod_insert ha, MvPolynomial.coeff_mul]
            -- The only non-zero term in the sum is when $x = (fun₀ | i => 1)$ and $y = (fun₀ | i => #s)$.
            have h_nonzero_term : ∀ x y : (Fin (k + 1)) →₀ ℕ, x + y = (fun₀ | i => #s) + (fun₀ | i => 1) → (MvPolynomial.coeff x (MvPolynomial.X i) - if 0 = x then a else 0) * MvPolynomial.coeff y (∏ a ∈ s, (MvPolynomial.X i - MvPolynomial.C a)) = if x = (fun₀ | i => 1) ∧ y = (fun₀ | i => #s) then 1 else 0 := by
              intro x y hxy
              by_cases hx : x = (fun₀ | i => 1)
              · rw [eq_comm] at hxy ; aesop
                · simpa using congr_arg (fun f => f i) h.symm
                · simpa using congr_arg (fun f => f i) h.symm
                · rw [Finsupp.ext_iff] at hxy ;
                  simp_all only [Finsupp.coe_add, Pi.add_apply]
                  contrapose! h_1; ext j; specialize hxy j; by_cases hj : j = i <;> aesop
                  linarith
              · rw [MvPolynomial.coeff_X'] ;
                simp_all only [false_and, ↓reduceIte, mul_eq_zero]
                split
                next h =>
                  subst h
                  simp_all only [not_true_eq_false]
                next h =>
                  simp_all only [zero_sub, neg_eq_zero, ite_eq_right_iff]
                  contrapose! hx
                  simp_all only [ne_eq]
                  obtain ⟨left, right⟩ := hx
                  obtain ⟨left, right_1⟩ := left
                  subst left
                  simp_all only [zero_add, single_eq_zero, one_ne_zero, not_false_eq_true]
                  subst hxy
                  -- The degree of the product of (X_i - C a) over s is #s, so any term with a higher degree than #s must have a coefficient of zero.
                  have h_deg : (∏ a ∈ s, (MvPolynomial.X i - MvPolynomial.C a)).totalDegree ≤ #s := by
                    have h_total_degree : ∀ (s : Finset (ZMod p)), (∏ a ∈ s, (MvPolynomial.X i - MvPolynomial.C a)).totalDegree ≤ s.card := by
                      intro s; induction s using Finset.induction <;> aesop
                      refine' le_trans (MvPolynomial.totalDegree_mul _ _) _
                      refine' le_trans (add_le_add (MvPolynomial.totalDegree_sub _ _) a_3) _ ; norm_num [add_comm]
                    exact h_total_degree s
                  rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt] at right <;> aesop
                  refine' lt_of_le_of_lt h_deg _
                  rw [Finset.sum_eq_single i] <;> aesop
            rw [Finset.sum_congr rfl fun x hx => h_nonzero_term _ _ <| by simpa using hx]
            simp_all only [Finset.sum_boole]
            rw [Finset.card_eq_one.mpr]
            simp_all only [Nat.cast_one]
            use ((fun₀ | i => 1), (fun₀ | i => #s)) ; ext
            rename_i a_1
            simp_all only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_singleton]
            obtain ⟨fst, snd⟩ := a_1
            simp_all only [Prod.mk.injEq, and_iff_right_iff_imp, and_imp]
            intro a_1 a_2
            subst a_1 a_2
            exact add_comm _ _
        exact h_leading_coeff _
      · unfold elimination_polynomials
        exact fun x hx => by rw [MvPolynomial.eval_prod] ; exact Finset.prod_eq_zero hx (by simp +decide)
      · -- Since $g_i(x_i)$ is a monic polynomial of degree $|A_i|$ in $x_i$, subtracting $x_i^{|A_i|}$ from $g_i(x_i)$ results in a polynomial of degree less than $|A_i|$ in $x_i$.
        have h_deg_sub : (elimination_polynomials A i - (MvPolynomial.X i) ^ #(A i)).totalDegree < #(A i) := by
          have h_deg_mono : (elimination_polynomials A i - (MvPolynomial.X i) ^ #(A i)).degreeOf i < #(A i) := by
            have h_deg_sub : (elimination_polynomials A i).coeff (Finsupp.single i #(A i)) = 1 := by
              -- The leading coefficient of the product of linear terms is 1.
              have h_leading_coeff : ∀ (s : Finset (ZMod p)), (∏ a ∈ s, (MvPolynomial.X i - MvPolynomial.C a)).coeff (Finsupp.single i s.card) = 1 := by
                intro s
                induction' s using Finset.induction with a s ha ih
                · simp +decide [MvPolynomial.coeff_one]
                · simp_all +decide [Finset.prod_insert ha, MvPolynomial.coeff_mul]
                  -- The only non-zero term in the sum is when $x = (fun₀ | i => 1)$ and $y = (fun₀ | i => #s)$.
                  have h_nonzero_term : ∀ x y : (Fin (k + 1)) →₀ ℕ, x + y = (fun₀ | i => #s) + (fun₀ | i => 1) → (MvPolynomial.coeff x (MvPolynomial.X i) - if 0 = x then a else 0) * MvPolynomial.coeff y (∏ a ∈ s, (MvPolynomial.X i - MvPolynomial.C a)) = if x = (fun₀ | i => 1) ∧ y = (fun₀ | i => #s) then 1 else 0 := by
                    intro x y hxy
                    by_cases hx : x = (fun₀ | i => 1)
                    · rw [eq_comm] at hxy ; aesop
                      · simpa using congr_arg (fun f => f i) h.symm
                      · simpa using congr_arg (fun f => f i) h.symm
                      · rw [Finsupp.ext_iff] at hxy
                        simp_all only [Finsupp.coe_add, Pi.add_apply]
                        contrapose! h_1; ext j; specialize hxy j; by_cases hj : j = i <;> aesop
                        linarith
                    · rw [MvPolynomial.coeff_X'] ;
                      simp_all only [false_and, ↓reduceIte, mul_eq_zero]
                      split
                      next h =>
                        subst h
                        simp_all only [not_true_eq_false]
                      next h =>
                        simp_all only [zero_sub, neg_eq_zero, ite_eq_right_iff]
                        contrapose! hx
                        simp_all only [ne_eq]
                        obtain ⟨left, right⟩ := hx
                        obtain ⟨left, right_1⟩ := left
                        subst left
                        simp_all only [zero_add, single_eq_zero, one_ne_zero, not_false_eq_true]
                        subst hxy
                        -- The degree of the product of (X_i - C a) over s is #s, so any term with a higher degree than #s must have a coefficient of zero.
                        have h_deg : (∏ a ∈ s, (MvPolynomial.X i - MvPolynomial.C a)).totalDegree ≤ #s := by
                          have h_total_degree : ∀ (s : Finset (ZMod p)), (∏ a ∈ s, (MvPolynomial.X i - MvPolynomial.C a)).totalDegree ≤ s.card := by
                            intro s; induction s using Finset.induction <;> aesop
                            refine' le_trans (MvPolynomial.totalDegree_mul _ _) _
                            refine' le_trans (add_le_add (MvPolynomial.totalDegree_sub _ _) a_3) _ ; norm_num [add_comm]
                          exact h_total_degree s
                        rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt] at right <;> aesop
                        refine' lt_of_le_of_lt h_deg _
                        rw [Finset.sum_eq_single i] <;> aesop
                  rw [Finset.sum_congr rfl fun x hx => h_nonzero_term _ _ <| by simpa using hx]
                  simp_all only [Finset.sum_boole]
                  rw [Finset.card_eq_one.mpr]
                  simp_all only [Nat.cast_one]
                  use ((fun₀ | i => 1), (fun₀ | i => #s)) ; ext
                  rename_i a_1
                  simp_all only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_singleton]
                  obtain ⟨fst, snd⟩ := a_1
                  simp_all only [Prod.mk.injEq, and_iff_right_iff_imp, and_imp]
                  intro a_1 a_2
                  subst a_1 a_2
                  exact add_comm _ _
              exact h_leading_coeff _
            rw [MvPolynomial.degreeOf_eq_sup] at * ;
            simp_all only [gt_iff_lt, Finset.card_pos, Nat.bot_eq_zero, Finset.sup_lt_iff,
              MvPolynomial.mem_support_iff, coeff_sub, ne_eq]
            intro b a
            by_cases hb : b i = #(A i)
            · simp_all +decide [MvPolynomial.coeff_X_pow]
              bound
              · simp_all only [single_eq_same, sub_self, not_true_eq_false]
              · contrapose! h; ext j; by_cases hj : j = i <;> aesop
                have h_deg_sub : ∀ m ∈ (elimination_polynomials A i).support, m j = 0 := by
                  unfold elimination_polynomials
                  intro m a_1
                  simp_all only [MvPolynomial.mem_support_iff, ne_eq]
                  rw [Finset.prod_congr rfl fun x hx => sub_eq_add_neg _ _] at a_1
                  rw [Finset.prod_add] at a_1
                  rw [MvPolynomial.coeff_sum] at a_1
                  obtain ⟨x, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero a_1
                  simp_all only [Finset.prod_const, Finset.mem_powerset, ne_eq]
                  obtain ⟨left, right⟩ := hx
                  rw [MvPolynomial.coeff_mul] at right
                  obtain ⟨y, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero right
                  simp_all only [Finset.mem_antidiagonal, ne_eq, mul_eq_zero, not_or]
                  obtain ⟨fst, snd⟩ := y
                  obtain ⟨left_1, right_1⟩ := hy
                  obtain ⟨left_2, right_1⟩ := right_1
                  subst left_1
                  simp_all only [Finsupp.coe_add, Pi.add_apply, Nat.add_eq_zero_iff]
                  apply And.intro
                  · rw [MvPolynomial.coeff_X_pow] at left_2
                    simp_all only [ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not]
                    subst left_2
                    simp_all only [ne_eq, not_false_eq_true, single_eq_of_ne]
                  · rw [Finset.prod_congr rfl fun _ _ => neg_eq_neg_one_mul _, Finset.prod_mul_distrib] at right_1
                    simp_all only [Finset.prod_const]
                    -- Since the product is over elements of A i \ x, and each element is a constant, the only way for the product to have a non-zero coefficient is if snd is the zero function. Otherwise, there would be a term in the product that's a constant, which can't contribute to the coefficient of snd unless snd is zero.
                    have h_snd_zero : ∀ (c : ZMod p), MvPolynomial.coeff snd (MvPolynomial.C c) = if snd = 0 then c else 0 := by
                      intro c; rw [MvPolynomial.coeff_C]
                      split
                      next h =>
                        subst h
                        simp_all only [add_zero, ↓reduceIte]
                      next h =>
                        simp_all only [right_eq_ite_iff]
                        intro a_2
                        subst a_2
                        simp_all only [add_zero, not_true_eq_false]
                    specialize h_snd_zero ((-1) ^ # (A i \ x) * ∏ x ∈ A i \ x, x) ; simp_all
                exact Eq.symm (h_deg_sub b (by simp_all only [MvPolynomial.mem_support_iff, ne_eq, not_false_eq_true]))
            · contrapose! a; simp_all +decide [MvPolynomial.coeff_X_pow]
              rw [if_neg (by intro h; replace h := congr_arg (fun f => f i) h; aesop)]
              simp_all only [sub_zero]
              exact Classical.not_not.1 fun h => hb <| le_antisymm (h_deg ▸ Finset.le_sup (f := fun m => m i) (MvPolynomial.mem_support_iff.2 h)) a
          have h_total_deg : ∀ j ≠ i, (elimination_polynomials A i - (MvPolynomial.X i) ^ #(A i)).degreeOf j ≤ 0 := by
            intros j hj_ne_i
            have h_deg_j : (elimination_polynomials A i).degreeOf j = 0 := by
              unfold elimination_polynomials
              induction' (A i) using Finset.induction <;> aesop
              · norm_num [MvPolynomial.degreeOf]
              · -- Since $j \neq i$, the degree of $X_i - C a$ in $j$ is zero.
                have h_deg_j_zero : MvPolynomial.degreeOf j (MvPolynomial.X i - MvPolynomial.C a) = 0 := by
                  simp +decide [MvPolynomial.degreeOf_eq_sup]
                  intro m hm; rw [MvPolynomial.coeff_X'] at hm
                  split at hm
                  next h =>
                    split at hm
                    next h_1 =>
                      subst h
                      simp_all only [ne_eq, not_false_eq_true, single_eq_of_ne]
                    next h_1 =>
                      subst h
                      simp_all only [sub_zero, one_ne_zero, not_false_eq_true, ne_eq, single_eq_of_ne]
                  next h =>
                    split at hm
                    next h_1 =>
                      subst h_1
                      simp_all only [zero_sub, neg_eq_zero, single_eq_zero, one_ne_zero, not_false_eq_true,
                        Finsupp.coe_zero, Pi.zero_apply]
                    next h_1 => simp_all only [sub_self, not_true_eq_false]
                exact le_antisymm (le_trans (MvPolynomial.degreeOf_mul_le _ _ _) (by simp_all only [add_zero, le_refl])) (Nat.zero_le _)
            simp_all +decide [MvPolynomial.degreeOf_eq_sup]
            intro m hm; specialize h_deg_j m; rw [MvPolynomial.coeff_X_pow] at hm
            split at hm
            next h =>
              subst h
              simp_all only [ne_eq, not_false_eq_true, single_eq_of_ne, implies_true]
            next h => simp_all only [sub_zero, not_false_eq_true]
          rw [MvPolynomial.totalDegree]
          simp_all +decide [MvPolynomial.degreeOf_eq_sup]
          intro b hb; specialize h_deg_mono b hb; specialize h_total_deg; simp_all +decide [Finsupp.sum_fintype]
          rw [Finset.sum_eq_single i] <;> aesop
        exact h_deg_sub

/-- A single step in the monomial reduction process, reducing the degree in variable `i`. -/
lemma monomial_reduction_step (m : Fin (k + 1) →₀ ℕ) (i : Fin (k + 1))
    (A : Fin (k + 1) → Finset (ZMod p))
    (c : Fin (k + 1) → ℕ)
    (hA : ∀ j, (A j).card = c j + 1)
    (hi : m i > c i) :
    ∃ Q : MvPolynomial (Fin (k + 1)) (ZMod p),
      Q.totalDegree < m.sum (fun _ n => n) ∧
      (∀ x, (∀ j, x j ∈ A j) → eval x Q = eval x (monomial m 1)) ∧
      (m.sum (fun _ n => n) ≤ ∑ j, c j →
        coeff (Finsupp.equivFunOnFinite.symm c) Q = coeff (Finsupp.equivFunOnFinite.symm c) (monomial m 1)) := by
          -- Define Q as X^{m'} * (X_i^{c_i+1} - g_i).
          set Q : MvPolynomial (Fin (k + 1)) (ZMod p) := MvPolynomial.monomial (m - Finsupp.single i (c i + 1)) 1 * (MvPolynomial.X i ^ (c i + 1) - elimination_polynomials A i)
          -- Show that the total degree of Q is less than the total degree of m.
          have hQ_totalDegree : Q.totalDegree < m.sum (fun _ n => n) := by
            have hQ_totalDegree : (MvPolynomial.X i ^ (c i + 1) - elimination_polynomials A i).totalDegree < c i + 1 := by
              have := elimination_polynomial_properties A i
              rw [← neg_sub, MvPolynomial.totalDegree_neg]
              simp_all
            have hQ_totalDegree : Q.totalDegree ≤ (m - Finsupp.single i (c i + 1)).sum (fun x n => n) + (MvPolynomial.X i ^ (c i + 1) - elimination_polynomials A i).totalDegree := by
              convert MvPolynomial.totalDegree_mul _ _ using 1
              norm_num [MvPolynomial.totalDegree_monomial]
            have hQ_totalDegree : (m - Finsupp.single i (c i + 1)).sum (fun x n => n) + (MvPolynomial.X i ^ (c i + 1) - elimination_polynomials A i).totalDegree < m.sum (fun x n => n) := by
              simp_all +decide [Finsupp.sum_fintype]
              simp_all +decide [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i), Finsupp.single_apply]
              rw [Finset.sum_congr rfl fun x hx => by rw [if_neg (Ne.symm <| Finset.mem_singleton.not.mp <| Finset.mem_sdiff.mp hx |>.2), if_neg (Ne.symm <| Finset.mem_singleton.not.mp <| Finset.mem_sdiff.mp hx |>.2)]] ; simp +arith +decide [*]
              omega
            linarith
          refine' ⟨Q, _, _, _⟩ <;> aesop
          · -- By definition of $g_i$, we know that $g_i(x) = 0$ for all $x \in A_i$.
            have h_gi_zero : ∀ x : Fin (k + 1) → ZMod p, (∀ j, x j ∈ A j) → (MvPolynomial.eval x (elimination_polynomials A i)) = 0 := by
              intro x hx; unfold elimination_polynomials; simp +decide [Finset.prod_eq_zero_iff, sub_eq_zero, hx]
            rw [h_gi_zero x a, sub_zero] ; simp +decide [MvPolynomial.eval_monomial] ; ring_nf
            simp +decide [Finsupp.single_apply, Finset.prod_eq_prod_diff_singleton_mul (Finset.mem_univ i), mul_assoc, ← pow_succ']
            rw [← pow_add, Nat.sub_add_cancel (by linarith)]
            exact congrArg₂ _ (Finset.prod_congr rfl fun j hj => by
            simp_all only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
            split
            next h =>
              subst h
              simp_all only [not_true_eq_false]
            next h => simp_all only [add_zero, tsub_zero]) rfl
          · rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt]
            simp_all
            exact lt_of_lt_of_le hQ_totalDegree (le_trans a (by rw [Finset.sum_filter_of_ne] ; aesop))

/-- Existence of a remainder polynomial R with bounded degrees matching Q on specified points. -/
lemma exists_remainder (Q : MvPolynomial (Fin (k + 1)) (ZMod p))
    (A : Fin (k + 1) → Finset (ZMod p))
    (c : Fin (k + 1) → ℕ)
    (hA : ∀ i, (A i).card = c i + 1)
    (hQ_deg : Q.totalDegree ≤ ∑ i, c i) :
    ∃ R : MvPolynomial (Fin (k + 1)) (ZMod p),
      (∀ i, R.degreeOf i ≤ c i) ∧
      (∀ x, (∀ i, x i ∈ A i) → eval x R = eval x Q) ∧
      (coeff (Finsupp.equivFunOnFinite.symm c) R = coeff (Finsupp.equivFunOnFinite.symm c) Q) := by
        by_contra h_contra
        -- Apply induction on the total degree of Q.
        induction' hQ_deg : Q.totalDegree using Nat.strong_induction_on with d ih generalizing Q
        -- Apply the induction hypothesis to each term in the sum.
        have h_induction : ∀ m ∈ Q.support, (∃ R : MvPolynomial (Fin (k + 1)) (ZMod p), (∀ i, R.degreeOf i ≤ c i) ∧ (∀ x : Fin (k + 1) → ZMod p, (∀ i, x i ∈ A i) → R.eval x = (MvPolynomial.monomial m 1).eval x) ∧ R.coeff (Finsupp.equivFunOnFinite.symm c) = (MvPolynomial.monomial m 1).coeff (Finsupp.equivFunOnFinite.symm c)) := by
          intro m hm
          by_cases hm_deg : m.sum (fun _ n => n) ≤ ∑ i, c i
          · by_cases hm_deg : ∃ i, m i > c i
            · obtain ⟨i, hi⟩ : ∃ i, m i > c i := hm_deg
              obtain ⟨Q', hQ'_deg, hQ'_eval, hQ'_coeff⟩ : ∃ Q' : MvPolynomial (Fin (k + 1)) (ZMod p), Q'.totalDegree < m.sum (fun _ n => n) ∧ (∀ x : Fin (k + 1) → ZMod p, (∀ i, x i ∈ A i) → Q'.eval x = (MvPolynomial.monomial m 1).eval x) ∧ Q'.coeff (Finsupp.equivFunOnFinite.symm c) = (MvPolynomial.monomial m 1).coeff (Finsupp.equivFunOnFinite.symm c) := by
                -- Apply the monomial_reduction_step lemma to get Q'.
                obtain ⟨Q', hQ'_deg, hQ'_eval, hQ'_coeff⟩ : ∃ Q' : MvPolynomial (Fin (k + 1)) (ZMod p), Q'.totalDegree < m.sum (fun _ n => n) ∧ (∀ x : Fin (k + 1) → ZMod p, (∀ i, x i ∈ A i) → Q'.eval x = (MvPolynomial.monomial m 1).eval x) ∧ Q'.coeff (Finsupp.equivFunOnFinite.symm c) = (MvPolynomial.monomial m 1).coeff (Finsupp.equivFunOnFinite.symm c) := by
                  have := monomial_reduction_step m i A c hA hi
                  grind
                use Q'
              specialize ih (Q'.totalDegree) (by
                refine' lt_of_lt_of_le hQ'_deg _
                exact hQ_deg ▸ Finset.le_sup (f := fun s => s.sum fun x n => n) hm) Q' (by
                linarith)
              subst hQ_deg
              simp_all
            · use MvPolynomial.monomial m 1
              simp_all (config := {decide := Bool.true}) only [degreeOf_eq_sup, Finset.sup_le_iff,
                MvPolynomial.mem_support_iff, ne_eq, not_exists, not_and, imp_false, gt_iff_lt,
                not_lt, coeff_monomial, ite_eq_right_iff, one_ne_zero, Decidable.not_not,
                forall_eq', implies_true, and_self]
          · refine' False.elim (hm_deg <| le_trans _ ‹Q.totalDegree ≤ ∑ i, c i›)
            exact Finset.le_sup (f := fun m => m.sum fun _ n => n) hm
        choose! R hR₁ hR₂ hR₃ using h_induction
        refine' h_contra ⟨∑ m ∈ Q.support, Q.coeff m • R m, _, _, _⟩
        · intro i
          refine' le_trans (MvPolynomial.degreeOf_sum_le _ _ _) _
          simp +zetaDelta at *
          intro m hm; specialize hR₁ m hm i; rw [MvPolynomial.degreeOf_eq_sup] at *;
          simp_all only [Finset.sup_le_iff, MvPolynomial.mem_support_iff, ne_eq, not_false_eq_true,
            MvPolynomial.support_smul_eq, implies_true]
        · simp only [map_sum, smul_eval]
          intro x hx; rw [MvPolynomial.eval_eq']
          exact Finset.sum_congr rfl fun m hm => by rw [hR₂ m hm x hx] ; simp only [eval_monomial,
            prod_pow, one_mul]
        · rw [MvPolynomial.coeff_sum]
          rw [Finset.sum_congr rfl fun m hm => by rw [MvPolynomial.coeff_smul, hR₃ m hm]]
          simp only [coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
            MvPolynomial.mem_support_iff, ne_eq, ite_not, ite_eq_right_iff]
          exact fun h => h.symm

/-- If a polynomial Q vanishes on a grid defined by sets A_i and has total degree at most the sum of the sizes of these sets minus one, then the coefficient of the monomial defined by these sizes is zero. -/
lemma coeff_target_eq_zero_of_vanishes_on_grid
    (Q : MvPolynomial (Fin (k + 1)) (ZMod p))
    (A : Fin (k + 1) → Finset (ZMod p))
    (c : Fin (k + 1) → ℕ)
    (hA : ∀ i, (A i).card = c i + 1)
    (hQ_deg : Q.totalDegree ≤ ∑ i, c i)
    (hQ_vanishes : ∀ x, (∀ i, x i ∈ A i) → eval x Q = 0) :
    coeff (Finsupp.equivFunOnFinite.symm c) Q = 0 := by
      -- Apply `exists_remainder` to $Q$ to get $R$.
      obtain ⟨R, hR⟩ := exists_remainder Q A c hA hQ_deg
      -- By `eq_zero_of_eval_zero_at_prod_finset`, $R = 0$.
      have hR_zero : R = 0 := by
        -- Apply the fact that if a polynomial vanishes on a product of finite sets and its degree in each variable is less than the size of the corresponding set, then the polynomial must be zero.
        have hR_zero : ∀ (P : MvPolynomial (Fin (k + 1)) (ZMod p)), (∀ i, P.degreeOf i < #(A i)) → (∀ x : Fin (k + 1) → ZMod p, (∀ i, x i ∈ A i) → MvPolynomial.eval x P = 0) → P = 0 := by
          exact fun P a a_1 => _root_.eq_zero_of_eval_zero_at_prod_finset P A a a_1
        exact hR_zero R (fun i => by linarith [hR.1 i, hA i]) fun x hx => by simp [hR.2.1 x hx, hQ_vanishes x hx]
      aesop

/-- If two polynomials P and Q are equal or their difference has a total degree less than m, then the coefficients of the monomial defined by c in h * P and h * Q are equal, given that h.totalDegree + m equals the sum of c_i. -/
lemma coeff_mul_eq_of_degree_bound
    (h P Q : MvPolynomial (Fin (k + 1)) (ZMod p))
    (c : Fin (k + 1) → ℕ)
    (m : ℕ)
    (h_deg : h.totalDegree + m = ∑ i, c i)
    (h_diff : P = Q ∨ (P - Q).totalDegree < m) :
    coeff (Finsupp.equivFunOnFinite.symm c) (h * P) =
    coeff (Finsupp.equivFunOnFinite.symm c) (h * Q) := by
      aesop
      -- Since $P - Q$ has a total degree less than $m$, $h * (P - Q)$ has a total degree less than $h.totalDegree + m$.
      have h_total_degree : (h * (P - Q)).totalDegree < h.totalDegree + m := by
        -- The total degree of a product of two polynomials is less than or equal to the sum of their total degrees.
        have h_total_degree_mul : (h * (P - Q)).totalDegree ≤ h.totalDegree + (P - Q).totalDegree := by
          exact totalDegree_mul h (P - Q)
        linarith
      -- Since the total degree of $h * (P - Q)$ is less than the sum of $c_i$, the coefficient of the monomial $c$ in $h * (P - Q)$ must be zero.
      have h_coeff_zero : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) (h * (P - Q)) = 0 := by
        rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt] ; aesop
        exact h_total_degree.trans_le (by rw [Finset.sum_filter_of_ne] ; aesop)
      simp_all +decide [mul_sub]
      exact eq_of_sub_eq_zero h_coeff_zero

/-- The total degree of the difference between the product of linear terms and the corresponding power of the sum polynomial is less than the size of the multiset. -/
lemma degree_product_minus_pow_lt {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ} (E : Multiset (ZMod p)) (hE : E.card > 0) :
    ((E.map (fun e => (sumX_polynomial : MvPolynomial (Fin (k + 1)) (ZMod p)) - C e)).prod - (sumX_polynomial : MvPolynomial (Fin (k + 1)) (ZMod p)) ^ E.card).totalDegree < E.card := by
      -- Since every monomial of degree $|E|$ in $P$ has the same coefficient as in $Q$, the difference $P - Q$ has no terms of degree $|E|$.
      have h_coeff_eq : ∀ x : (Fin (k + 1)) →₀ ℕ, x.sum (fun _ n => n) = E.card →
          MvPolynomial.coeff x ((E.map (fun e => (∑ i : Fin (k+1), MvPolynomial.X i) - MvPolynomial.C e)).prod - (∑ i : Fin (k+1), MvPolynomial.X i) ^ E.card) = 0 := by
            -- Apply the lemma that states the coefficients of monomials of degree $|E|$ in $P$ and $Q$ are equal.
            intros x hx
            have h_coeff_eq : MvPolynomial.coeff x ((E.map (fun e => (∑ i : Fin (k+1), MvPolynomial.X i) - MvPolynomial.C e)).prod) = MvPolynomial.coeff x ((∑ i : Fin (k+1), MvPolynomial.X i) ^ E.card) := by
              convert coeff_prod_sumX_minus_C_eq_coeff_sumX_pow_of_degree_eq E x _
              simpa [Finsupp.sum_fintype] using hx
            aesop
      -- Since there are no terms of degree $|E|$ in $P - Q$, the total degree of $P - Q$ must be strictly less than $|E|$.
      have h_total_degree_lt : ∀ x : (Fin (k + 1)) →₀ ℕ, x.sum (fun _ n => n) ≥ E.card → MvPolynomial.coeff x ((E.map (fun e => (∑ i : Fin (k+1), MvPolynomial.X i) - MvPolynomial.C e)).prod - (∑ i : Fin (k+1), MvPolynomial.X i) ^ E.card) = 0 := by
        -- If x has degree greater than E.card, then since P and Q both have total degree E.card, their difference P - Q can't have any terms of degree higher than E.card. Therefore, the coefficient of x in P - Q must be zero because there are no such terms.
        intros x hx
        by_cases hx_eq : x.sum (fun _ n => n) = E.card
        · exact h_coeff_eq x hx_eq
        · -- Since $x$ has degree greater than $E.card$, it cannot be in the support of $P$ or $Q$, hence its coefficient in $P - Q$ is zero.
          have h_support : ∀ (P : MvPolynomial (Fin (k + 1)) (ZMod p)), P.totalDegree ≤ E.card → ∀ x : (Fin (k + 1)) →₀ ℕ, x.sum (fun _ n => n) > E.card → MvPolynomial.coeff x P = 0 := by
            intro P hP x hx; rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt] ; exact lt_of_le_of_lt hP hx
          rw [MvPolynomial.coeff_sub, h_support _ _ _ (lt_of_le_of_ne hx (Ne.symm hx_eq)), h_support _ _ _ (lt_of_le_of_ne hx (Ne.symm hx_eq)), sub_self]
          · refine' le_trans (MvPolynomial.totalDegree_pow _ _) _
            refine' mul_le_of_le_one_right hE.le _
            refine' le_trans (Finset.sup_le _) _
            exact 1
            · simp +decide [MvPolynomial.coeff_sum, MvPolynomial.coeff_X']
              intro b hb; contrapose! hb; simp_all +decide
              rw [Finset.card_eq_zero.mpr] <;> aesop
            · norm_num
          · convert totalDegree_prod_sumX_sub_C_eq_card E |> le_of_eq
      -- If the total degree were at least E.card, there would be a monomial in the support of P - Q with degree exactly E.card.
      by_contra h_contra
      obtain ⟨x, hx⟩ : ∃ x : (Fin (k + 1)) →₀ ℕ, x ∈ (MvPolynomial.support ((E.map (fun e => (∑ i : Fin (k+1), MvPolynomial.X i) - MvPolynomial.C e)).prod - (∑ i : Fin (k+1), MvPolynomial.X i) ^ E.card)) ∧ x.sum (fun _ n => n) = E.card := by
        have h_total_degree_lt : ∃ x ∈ MvPolynomial.support ((E.map (fun e => (∑ i : Fin (k+1), MvPolynomial.X i) - MvPolynomial.C e)).prod - (∑ i : Fin (k+1), MvPolynomial.X i) ^ E.card), x.sum (fun _ n => n) ≥ E.card := by
          contrapose! h_contra; aesop
          rw [MvPolynomial.totalDegree] ; aesop
        obtain ⟨x, hx₁, hx₂⟩ := h_total_degree_lt; use x; aesop
      exact absurd (h_coeff_eq x hx.2) (by aesop)

end AristotleLemmas

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
  intro S
  have h_ne_zero : h ≠ 0 := by
    intro h_zero
    rw [h_zero, mul_zero, coeff_zero] at h_coeff
    exact h_coeff rfl

  -- Step 1: Prove |S| >= m + 1 by contradiction
  have hS_card : S.card ≥ m + 1 := by
    by_contra! H
    have hS_size : S.card ≤ m := by omega
    set E := extend_to_size S m with hE_def
    have extend_to_size_properties :
    S.val ⊆ extend_to_size S m ∧ (extend_to_size S m).card = m := by
      refine ⟨Multiset.subset_of_le (by simp [extend_to_size]), ?_⟩
      dsimp [extend_to_size]
      simp [hS_size]
    have hE_props : S.val ⊆ E ∧ E.card = m := by exact extend_to_size_properties
    obtain ⟨hE_sub, hE_card⟩ := hE_props

    set Q := construction_polynomial h E with hQ_def

    -- Q vanishes on prod A_i
    have hQ_zero : ∀ (x : Fin (k + 1) → ZMod p), (∀ i, x i ∈ A i) → eval x Q = 0 := fun x a => construction_polynomial_vanishes h A E hE_sub x a
    have h_prod_ne_zero : product_polynomial k E ≠ 0 := by exact product_polynomial_ne_zero k E
    have hQ_total_deg : Q.totalDegree = ∑ i, c i := by
      exact construction_polynomial_totalDegree h h_ne_zero c m E hm hE_card h_prod_ne_zero
    have hQ_coeff : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) Q ≠ 0 := by
      rw [hQ_def]
      apply construction_polynomial_coeff_target_generalized h c m hm h_coeff E hE_card
      · -- The product of (sumX - e) over E is equal to (sumX)^m plus a polynomial of degree less than m.
        have h_prod_eq : (E.map (fun e => (∑ i : Fin (k + 1), MvPolynomial.X i) - MvPolynomial.C e)).prod = (∑ i : Fin (k + 1), MvPolynomial.X i) ^ m + (E.map (fun e => (∑ i : Fin (k + 1), MvPolynomial.X i) - MvPolynomial.C e)).prod - (∑ i : Fin (k + 1), MvPolynomial.X i) ^ m := by
          ring
        -- The degree of the difference between the product and (sumX)^m is less than m.
        have h_diff_deg : (E.map (fun e => (∑ i : Fin (k + 1), MvPolynomial.X i) - MvPolynomial.C e)).prod - (∑ i : Fin (k + 1), MvPolynomial.X i) ^ m ≠ 0 →
          (E.map (fun e => (∑ i : Fin (k + 1), MvPolynomial.X i) - MvPolynomial.C e)).prod - (∑ i : Fin (k + 1), MvPolynomial.X i) ^ m ≠ 0 →
          ((E.map (fun e => (∑ i : Fin (k + 1), MvPolynomial.X i) - MvPolynomial.C e)).prod - (∑ i : Fin (k + 1), MvPolynomial.X i) ^ m).totalDegree < m := by
            intro h1 h2
            convert degree_product_minus_pow_lt E _
            · exact hE_card.symm
            · exact hE_card.symm
            · contrapose! h1; simp_all (config := { singlePass := Bool.true })
        by_cases h_diff_zero : (E.map (fun e => (∑ i : Fin (k + 1), MvPolynomial.X i) - MvPolynomial.C e)).prod - (∑ i : Fin (k + 1), MvPolynomial.X i) ^ m = 0
        · rw [sub_eq_zero.mp h_diff_zero]
        · -- Since the difference has a lower degree, the coefficient of the term with degree m in the product must be equal to the coefficient of the term with degree m in (sumX)^m.
          have h_coeff_eq : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) ((E.map (fun e => (∑ i : Fin (k + 1), MvPolynomial.X i) - MvPolynomial.C e)).prod - (∑ i : Fin (k + 1), MvPolynomial.X i) ^ m) = 0 := by
            -- Since the total degree of the difference is less than m, any term with degree m must have a coefficient of zero.
            have h_coeff_zero : ∀ (P : MvPolynomial (Fin (k + 1)) (ZMod p)), P.totalDegree < m → MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) P = 0 := by
              intros P hP_deg
              have h_coeff_zero : ∀ (m : (Fin (k + 1)) →₀ ℕ), m.sum (fun _ n => n) > P.totalDegree → MvPolynomial.coeff m P = 0 := by
                exact fun m a => coeff_eq_zero_of_totalDegree_lt a
              exact h_coeff_zero _ (by simpa [Finsupp.sum_fintype] using by linarith [show h.totalDegree ≥ 0 from Nat.zero_le _])
            exact h_coeff_zero _ (h_diff_deg h_diff_zero h_diff_zero)
          simp +zetaDelta at *
          exact eq_of_sub_eq_zero h_coeff_eq
      · intro d hd_ne_zero
        by_contra h_contra
        -- Apply the lemma `coeff_target_eq_zero_of_vanishes_on_grid` to $Q$.
        have h_coeff_zero : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) Q = 0 := by
          apply coeff_target_eq_zero_of_vanishes_on_grid
          any_goals tauto
          linarith
        -- Apply the lemma `coeff_mul_eq_of_degree_bound` with $h, P, P_{lead}, c, m$.
        have h_coeff_mul_eq : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) (h * (E.map (fun e => ∑ i : Fin (k + 1), MvPolynomial.X i - MvPolynomial.C e)).prod) = MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) (h * (∑ i : Fin (k + 1), MvPolynomial.X i) ^ m) := by
          apply coeff_mul_eq_of_degree_bound
          any_goals exact m
          · linarith
          · norm_num +zetaDelta at *
            by_cases hm : m = 0
            · subst hm
              simp_all
            · -- Apply the lemma `degree_product_minus_pow_lt` with the hypothesis `hm` (which states that m is not zero).
              apply Or.inr; exact (by
              convert degree_product_minus_pow_lt _ _
              · exact hE_card.symm
              · exact hE_card.symm
              · exact hE_card.symm ▸ Nat.pos_of_ne_zero hm)
        exact h_coeff (by simpa only [mul_comm] using h_coeff_mul_eq.symm.trans h_coeff_zero)
      · -- By contradiction, assume the constant term of h is zero.
        by_contra h_const_zero
        -- If the constant term of h is zero, then the constant term of h * (∑ i, X i)^m is also zero.
        have h_const_zero_prod : MvPolynomial.coeff 0 (h * (∑ i, MvPolynomial.X i) ^ m) = 0 := by
          rw [MvPolynomial.coeff_mul, Finset.sum_eq_zero] ; aesop
        -- By the properties of the product of polynomials, we can show that the coefficient of the target term in h * (∑ i, X i)^m is equal to the coefficient of the target term in h * P_{lead}.
        have h_coeff_eq : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) (h * (∑ i, MvPolynomial.X i) ^ m) = MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) (h * (product_polynomial k E)) := by
          -- By the properties of polynomial multiplication, if the difference between two polynomials has a lower total degree, then their coefficients for the highest-degree term are equal.
          have h_diff_deg : (product_polynomial k E - (∑ i, MvPolynomial.X i) ^ m).totalDegree < m := by
            convert degree_product_minus_pow_lt E _
            · linarith
            · linarith
            · simp_all (config := { decide := Bool.true }) [product_polynomial]
              contrapose! h_coeff; aesop
              convert coeff_target_eq_zero_of_vanishes_on_grid h A c hA _ _
              · linarith
              · exact H
          have h_coeff_eq : ∀ (P Q : MvPolynomial (Fin (k + 1)) (ZMod p)), (P - Q).totalDegree < m → MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) (h * P) = MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm c) (h * Q) := by
            intros P Q h_diff_deg
            apply coeff_mul_eq_of_degree_bound
            all_goals norm_cast
            · linarith
            · exact Or.inr h_diff_deg
          exact h_coeff_eq _ _ h_diff_deg |> Eq.symm
        apply h_coeff
        rw [mul_comm, h_coeff_eq]
        apply_rules [coeff_target_eq_zero_of_vanishes_on_grid]
        exact hQ_total_deg.le
    -- Define elimination polynomials g_i
    set g : Fin (k + 1) → MvPolynomial (Fin (k + 1)) (ZMod p) :=
      elimination_polynomials A with hg_def

    -- Construct Q_bar by reducing degrees
    set Q_bar : MvPolynomial (Fin (k + 1)) (ZMod p) :=
      reduce_polynomial_degrees Q g c with hQ_bar_def

    let target := Finsupp.equivFunOnFinite.symm c
    -- Apply the lemma that states if a polynomial vanishes on a grid, then the coefficient of the target monomial is zero.
    have hQ_coeff_zero : MvPolynomial.coeff target Q = 0 := by
      -- Apply the lemma that states if a polynomial vanishes on a grid, then the coefficient of the target monomial is zero. Use hQ_zero to satisfy the condition.
      apply coeff_target_eq_zero_of_vanishes_on_grid Q A c hA hQ_total_deg.le hQ_zero
    contradiction

  -- Step 2: Prove m < p first (this is needed for the main argument)
  have hmp : m < p := by
    exact lt_of_lt_of_le (Nat.lt_of_succ_le hS_card) (le_trans (Finset.card_le_univ _) (by norm_num))
  exact ⟨hS_card, hmp⟩
