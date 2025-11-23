import Mathlib

open Polynomial Finset

-- 定义基础环境：F 是一个域
variable {F : Type*} [Field F] [DecidableEq F]
-- 定义A和B是F的有限非空集合
variable {A B : Finset F} (hA : A.Nonempty) (hB : B.Nonempty)
-- 定义具体的双变量多项式f(x,y)
variable (f : Polynomial (Polynomial F))-- 这里 f 视为 (F[y])[x]，即系数为 F[y] 的 x 的多项式


lemma alon_tarsi (hA : A.Nonempty) (hB : B.Nonempty)
  (f_deg_x : f.natDegree < A.card) (f_deg_y : ∀ i ∈ f.support, (f.coeff i).natDegree < B.card)
  (f_roots : ∀ a ∈ A, ∀ b ∈ B, (f.map (evalRingHom b)).eval a = 0) :f = 0 := by
  ext i
  -- 令 f 的系数 F[y] 为 v
  let v := f.coeff i
  -- 【步骤 1】：先证明 v(b) = 0 对所有 b ∈ B 成立
  have h_root_v : ∀ b ∈ B, v.eval b = 0 := by
    intro b hb
    -- 定义 u(x) = f(x, b)
    let u := f.map (evalRingHom b)
    -- 1.1 证明 u 在 A 上全为 0
    -- 对应论文：u(a) = 0 for all a ∈ A
    have h_u_roots : ∀ a ∈ A, u.eval a = 0 :=
      fun a ha ↦ f_roots a ha b hb
    -- 1.2 证明 u 的次数 < |A|
    -- map 不会增加次数，所以 deg(u) ≤ deg(f) < |A|
    have h_u_deg : u.natDegree < A.card := by
      -- 显式指明 φ 是把系数 F[y] 映射到 F 的求值同态
      let φ : Polynomial F →+* F := evalRingHom b
      calc u.natDegree
        _ = (f.map φ).natDegree := rfl
        _ ≤ f.natDegree         := natDegree_map_le
        _ < A.card              := f_deg_x
    -- 1.3 应用核心引理：u 必须是零多项式
    have h_u_zero : u = 0 := sorry
      -- 原本的想法是这样：eq_zero_of_natDegree_lt_card_of_eval_eq_zero u _ h_u_roots h_u_deg

    -- 1.4 推导 v(b) = 0
    -- 关键点：u 的第 i 个系数，就是 v 在 b 点的求值
    -- Mathlib 引理：coeff (map φ p) n = φ (coeff p n)
    have h_val : v.eval b = u.coeff i := by
      rw [coeff_map (evalRingHom b) i]
      rfl
     -- 因为 u = 0，所以它的系数 u.coeff i 必须是 0
    rw [h_val, h_u_zero, coeff_zero]


  -- 【步骤 2】：证明 v(y) 本身是零多项式
    -- 2.1 准备次数条件：v 的次数 < |B|
  have h_v_deg : v.natDegree < B.card := by
    -- 分情况讨论：如果 i 在 f 的支持集中，直接用假设；如果不在，v就是0
    by_cases hi : i ∈ f.support
    · exact f_deg_y i hi
    · rw [mem_support_iff, not_not] at hi
      have hv_zero : v = 0 := hi
      -- 现在 hv_zero 是 "v = 0"，目标里也有 "v"，rw 就能匹配上了
      rw [hv_zero, natDegree_zero]
      -- 因为 B 非空，所以 card > 0，0 < card 成立
      exact Finset.card_pos.mpr hB

  -- 2.2 再次应用核心引理，跟上面那个sorry的问题如出一辙
  -- 因为 v 在 B 上全是 0，且次数 < |B|，所以 v = 0
  -- exact eq_zero_of_natDegree_lt_card_of_eval_eq_zero B h_root_v h_v_deg
  sorry



lemma Combo_Null (m : ℕ) (hm : A.card ≤ m) :
    ∃ g : Polynomial F, g.degree < A.card ∧ ∀ a ∈ A, g.eval a = a ^ m := by
  -- 【步骤 1】 Let A = {a_0, ..., a_{k-1}}
  -- 通过将 A 等价于 Fin k 来给 A 中的元素编号
  let k := A.card
  let ISO := A.equivFin -- ISO : {x // x ∈ A} ≃ Fin k接收一个集合中的元素映射到索引
  -- 定义 v i = a_i。因为是从集合建立的映射，v 是单射 (injective)
  let v : Fin k → F := fun i => ISO.symm i -- 使用 .symm (逆映射) 从索引 i 获取元素 a_i
  -- 证明 v 是单射 (用于证明 Vandermonde 行列式非零)
  have v_injective : Function.Injective v := by
    intro i j h_eq
    -- h_eq 是 v i = v j (在 F 中相等)
    -- 因为 A 是集合，值相等意味着它们在子类型 {x // x ∈ A} 中也是同一个元素
    apply ISO.symm.injective
    apply Subtype.ext h_eq

  -- 【步骤 2】 构造线性方程组 M * u = y
  -- M 是 Vandermonde 矩阵的转置
  let M := (Matrix.vandermonde v).transpose
  let y : Fin k → F := fun i => (v i) ^ m

  -- 【步骤 3】 证明行列式非零
  have h_det_ne_zero : M.det ≠ 0 := by
    rw [Matrix.det_transpose]
    rw [Matrix.det_vandermonde v]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have h_rt : i < j := Finset.mem_Ioi.mp hj
    have h_neq : i ≠ j := (ne_of_lt h_rt)
    simp only [sub_ne_zero]
    exact v_injective.ne h_neq.symm

  have h_def_unit : IsUnit M.det := isUnit_iff_ne_zero.mpr h_det_ne_zero

  -- 【步骤 4】 解方程组
  -- 1. 将 M 提升为可逆元结构 (Units (Matrix ...))
  let M_unit := M.nonsingInvUnit h_def_unit
  -- 2. 取出逆矩阵 (M_unit.inv) 并计算 u
  let u := Matrix.mulVec M_unit.inv y
  let g := ∑ i : Fin k, C (u i) * X ^ (i : ℕ)
  use g
  constructor
  · -- 验证性质 1: degree < k
    apply (degree_sum_le _ _).trans_lt
    rw [Finset.sup_lt_iff]
    · intro b _
      apply (degree_C_mul_X_pow_le _ _).trans_lt
      exact WithBot.coe_lt_coe.mpr b.is_lt
    · -- 处理空集的情况 (A 非空，所以 card > 0)
      -- simp only [WithBot.bot_lt_coe]
      sorry
  · -- 验证性质 2: g(a) = a^m (这部分保持不变)
    intro a ha
    let i := ISO ⟨a, ha⟩
    have hi : v i = a := by
      dsimp [v]
      rw [Equiv.symm_apply_apply]
     -- 将目标 a 替换为 v i
    rw [← hi]
    -- 展开多项式求值: g(v i) = ∑ u_j * (v i)^j
    dsimp [g]
    rw [eval_finset_sum]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    -- 利用矩阵方程 M * u = y
    have h_mat_eq : M.mulVec u = y := by
      dsimp [u]
      -- M * (M⁻¹ * y) = y
      rw [Matrix.mulVec_mulVec]
      have h_inv : M * ((M_unit⁻¹ : Units (Matrix (Fin k) (Fin k) F)) : Matrix (Fin k) (Fin k) F) = 1 :=
        Units.mul_inv M_unit
      rw [h_inv,Matrix.one_mulVec]
    have h_row := congr_fun h_mat_eq i
    simp only [Matrix.mulVec] at h_row
    simp [M, Matrix.vandermonde, y] at h_row
    -- 将目标 (∑ u_j * v_i^j) 转换为矩阵方程的形式 (∑ v_i^j * u_j)
    trans
    · apply Finset.sum_congr rfl
      intro j _
      apply mul_comm -- 交换乘法顺序
    · sorry
    done
