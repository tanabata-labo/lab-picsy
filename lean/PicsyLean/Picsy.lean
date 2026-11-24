/-
PICSY 仮想中央銀行法の形式化（docs/spec.md §5 の性質）。

状態は有理数の正方行列 `E : Mat n`。メンバーの型 `n` は有限型。
式番号は鈴木健の博士論文（2009）第3章のもの。
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset

namespace Picsy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- 評価行列。Mathlib の `Matrix` ではなく素の関数型で持つ（成分の計算しかしないため）。 -/
abbrev Mat (n : Type*) := n → n → ℚ

/-- 不変条件 I1（非負）と I2（行和1）。 -/
def IsStochastic (E : Mat n) : Prop :=
  (∀ i j, 0 ≤ E i j) ∧ ∀ i, ∑ j, E i j = 1

/-- 仮想中央銀行を配った行列 E'（論文 (3.63)）。各人の予算を自分以外の N-1 人へ均等に配る。 -/
def vcb (E : Mat n) : Mat n :=
  fun i j => if i = j then 0 else E i j + E i i / (Fintype.card n - 1)

/-- 全員が自分以外の全員を均等に評価する行列 J = D/(N-1)。 -/
def J : Mat n :=
  fun i j => if i = j then 0 else 1 / (Fintype.card n - 1)

/-- 取引（論文 (3.65)(3.66)）。買い手 b の予算から α を売り手 s への評価へ移す。 -/
def transact (E : Mat n) (b s : n) (α : ℚ) : Mat n :=
  fun i j =>
    if i = b then
      (if j = b then E i j - α else if j = s then E i j + α else E i j)
    else E i j

/-- 自然回収（論文 (3.67)(3.68)）。E ← (1-γ)E + γI。 -/
def recover (E : Mat n) (γ : ℚ) : Mat n :=
  fun i j => (1 - γ) * E i j + if i = j then γ else 0

/-! ### 補題 -/

/-- 対角だけ別扱いした和。 -/
lemma sum_split_diag (f : n → ℚ) (i : n) :
    ∑ j, f j = f i + ∑ j ∈ univ.erase i, f j := by
  rw [← add_sum_erase _ _ (mem_univ i)]

/-! ### P1: E' は非負・行確率・対角0 -/

theorem vcb_diag (E : Mat n) (i : n) : vcb E i i = 0 := by
  simp [vcb]

theorem vcb_stochastic (hN : 2 ≤ Fintype.card n) (E : Mat n) (hE : IsStochastic E) :
    IsStochastic (vcb E) := by
  obtain ⟨hnn, hrow⟩ := hE
  have hpos : (0 : ℚ) < (Fintype.card n : ℚ) - 1 := by
    have : (2 : ℚ) ≤ Fintype.card n := by exact_mod_cast hN
    linarith
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · unfold vcb
    split_ifs
    · exact le_refl 0
    · exact add_nonneg (hnn i j) (div_nonneg (hnn i i) hpos.le)
  · -- 対角の0と、それ以外の N-1 個の和に分ける
    rw [sum_split_diag _ i]
    have hrow' := hrow i
    rw [sum_split_diag _ i] at hrow'
    have hcard : ((univ.erase i).card : ℚ) = Fintype.card n - 1 := by
      rw [card_erase_of_mem (mem_univ i), card_univ, Nat.cast_sub (by omega)]
      simp
    have hsum : ∑ j ∈ univ.erase i, vcb E i j
        = ∑ j ∈ univ.erase i, (E i j + E i i / (Fintype.card n - 1)) := by
      refine sum_congr rfl fun j hj => ?_
      have : i ≠ j := fun h => (ne_of_mem_erase hj) h.symm
      simp [vcb, this]
    rw [hsum, sum_add_distrib, sum_const, nsmul_eq_mul, hcard, vcb_diag,
      mul_div_cancel₀ _ hpos.ne']
    linarith

/-! ### P3: 取引は前提 b ≠ s, 0 ≤ α ≤ E_bb のもとで不変条件を保つ -/

theorem transact_stochastic (E : Mat n) (hE : IsStochastic E) (b s : n) (α : ℚ)
    (hbs : b ≠ s) (hα0 : 0 ≤ α) (hα : α ≤ E b b) :
    IsStochastic (transact E b s α) := by
  obtain ⟨hnn, hrow⟩ := hE
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · unfold transact
    split_ifs with h1 h2 h3
    · subst h1; subst h2; linarith
    · exact add_nonneg (hnn i j) hα0
    · exact hnn i j
    · exact hnn i j
  · by_cases hi : i = b
    · subst hi
      -- 行 b: E_bb - α と E_bs + α 以外は変わらない
      have : ∀ j, transact E i s α i j = E i j + (if j = s then α else 0) - (if j = i then α else 0) := by
        intro j
        unfold transact
        by_cases hj : j = i
        · subst hj; simp [hbs]
        · by_cases hjs : j = s
          · subst hjs; simp [hj]
          · simp [hj, hjs]
      simp only [this, sum_sub_distrib, sum_add_distrib, sum_ite_eq', mem_univ,
        ite_true, hrow i]
      ring
    · simp [transact, hi, hrow i]

/-! ### P4: 自然回収は不変条件を保ち、予算を γ 以上にし、E' を (1-γ)E' + γJ へ写す -/

theorem recover_stochastic (E : Mat n) (hE : IsStochastic E) (γ : ℚ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    IsStochastic (recover E γ) := by
  obtain ⟨hnn, hrow⟩ := hE
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · unfold recover
    have := mul_nonneg (sub_nonneg.mpr hγ1) (hnn i j)
    split_ifs <;> linarith
  · simp only [recover, sum_add_distrib, ← mul_sum, hrow i, sum_ite_eq, mem_univ,
      ite_true]
    ring

theorem recover_budget (E : Mat n) (hE : IsStochastic E) (γ : ℚ) (hγ1 : γ ≤ 1) (i : n) :
    γ ≤ recover E γ i i := by
  have := mul_nonneg (sub_nonneg.mpr hγ1) (hE.1 i i)
  simp [recover]
  linarith

theorem vcb_recover (hN : 2 ≤ Fintype.card n) (E : Mat n) (γ : ℚ) :
    vcb (recover E γ) = fun i j => (1 - γ) * vcb E i j + γ * J i j := by
  have hpos : (Fintype.card n : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ Fintype.card n := by exact_mod_cast hN
    linarith
  funext i j
  by_cases h : i = j
  · simp [vcb, J, h]
  · simp only [vcb, J, recover, h, ite_false, ite_true]
    field_simp
    ring

/-! ### P6: 除去（決定 D9 の第2段）は不変条件を保つ -/

/-- 離脱者 d の除去。他のメンバーが d に付けていた評価 E_id を、本人の予算 E_ii へ戻してから
d の行と列を消す。結果はメンバーの型が `{j // j ≠ d}` の行列になる。 -/
def remove (E : Mat n) (d : n) : Mat {j : n // j ≠ d} :=
  fun i j => E i.1 j.1 + if i = j then E i.1 d else 0

theorem remove_stochastic (E : Mat n) (hE : IsStochastic E) (d : n) :
    IsStochastic (remove E d) := by
  obtain ⟨hnn, hrow⟩ := hE
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · have h1 := hnn i.1 j.1
    have h2 := hnn i.1 d
    unfold remove
    split_ifs <;> linarith
  · have h := hrow i.1
    rw [Fintype.sum_eq_add_sum_subtype_ne _ d] at h
    simp only [remove, sum_add_distrib, sum_ite_eq, mem_univ, ite_true]
    linarith

/-! ### P7: link farm は吸収集合になる

予算を使い切った人（E_ii = 0）だけからなり、組の外を評価しない組 S があるとする。
このとき定常な貢献度 c（c E' = c、c ≥ 0）では、組の外で予算が正の人の貢献度はすべて0になる。

証明は流れの収支による。組の外にある貢献度の総量は、組の外から組へ流れ出る分
（予算の社会的最低限 E_ii/(N-1) を通じて必ず正）と、組から外へ戻る分（0）が釣り合うときしか
保存されない。 -/

theorem farm_absorbs (hN : 2 ≤ Fintype.card n) (E : Mat n) (hE : IsStochastic E)
    (S : Finset n) (hS : S.Nonempty)
    (hbroke : ∀ i ∈ S, E i i = 0) (hclosed : ∀ i ∈ S, ∀ j ∉ S, E i j = 0)
    (c : n → ℚ) (hc0 : ∀ i, 0 ≤ c i) (hc : ∀ j, ∑ i, c i * vcb E i j = c j)
    (i : n) (hi : i ∉ S) (hbudget : 0 < E i i) : c i = 0 := by
  have hpos : (0 : ℚ) < (Fintype.card n : ℚ) - 1 := by
    have : (2 : ℚ) ≤ Fintype.card n := by exact_mod_cast hN
    linarith
  have hV := vcb_stochastic hN E hE
  -- 組から外への E' の成分は0
  have hzero : ∀ k ∈ S, ∀ j ∈ Sᶜ, vcb E k j = 0 := by
    intro k hk j hj
    have hj' : j ∉ S := mem_compl.mp hj
    have hkj : k ≠ j := fun h => hj' (h ▸ hk)
    simp [vcb, hkj, hclosed k hk j hj', hbroke k hk]
  -- 各人について、外への行和 = 1 - 組への行和
  have hrowc : ∀ k, ∑ j ∈ Sᶜ, vcb E k j = 1 - ∑ j ∈ S, vcb E k j := by
    intro k
    have := sum_add_sum_compl S (vcb E k)
    rw [hV.2 k] at this
    linarith
  -- 外の総量の収支
  have key : ∑ k ∈ Sᶜ, c k * ∑ j ∈ S, vcb E k j = 0 := by
    have hT : ∑ j ∈ Sᶜ, c j = ∑ k, c k * ∑ j ∈ Sᶜ, vcb E k j := by
      calc ∑ j ∈ Sᶜ, c j = ∑ j ∈ Sᶜ, ∑ k, c k * vcb E k j :=
            sum_congr rfl fun j _ => (hc j).symm
        _ = ∑ k, ∑ j ∈ Sᶜ, c k * vcb E k j := sum_comm
        _ = ∑ k, c k * ∑ j ∈ Sᶜ, vcb E k j := by simp_rw [mul_sum]
    have hsplit := sum_add_sum_compl S (fun k => c k * ∑ j ∈ Sᶜ, vcb E k j)
    have hS' : ∑ k ∈ S, c k * ∑ j ∈ Sᶜ, vcb E k j = 0 :=
      sum_eq_zero fun k hk => by rw [sum_eq_zero (hzero k hk), mul_zero]
    have hC : ∑ k ∈ Sᶜ, c k * ∑ j ∈ Sᶜ, vcb E k j
        = ∑ k ∈ Sᶜ, c k - ∑ k ∈ Sᶜ, c k * ∑ j ∈ S, vcb E k j := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun k _ => by rw [hrowc k]; ring
    linarith
  have hterm : c i * ∑ j ∈ S, vcb E i j = 0 :=
    (sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hc0 k) (sum_nonneg fun j _ => hV.1 k j)).mp
      key i (mem_compl.mpr hi)
  obtain ⟨s, hs⟩ := hS
  have hsi : i ≠ s := fun h => hi (h ▸ hs)
  have hflow : 0 < ∑ j ∈ S, vcb E i j := by
    have h1 : vcb E i s ≤ ∑ j ∈ S, vcb E i j := single_le_sum (fun j _ => hV.1 i j) hs
    have h2 : 0 < vcb E i s := by
      simp only [vcb, hsi, ite_false]
      exact add_pos_of_nonneg_of_pos (hE.1 i s) (div_pos hbudget hpos)
    linarith
  rcases mul_eq_zero.mp hterm with h | h
  · exact h
  · linarith

/-! ### P8: 予算の下限 ε があれば、どの組の占有にも上限がある

P7 の量的な強化。行確率行列 M と定常な c について、組 S から外への流れと外から S への流れは
釣り合う（`flow_balance`）。S の全員が予算 ε 以上を持つなら、E' の行から外へ少なくとも
ε·|Sᶜ|/(N-1) が漏れる。外の各人から S への流れが β 以下なら、S の貢献度の合計は
c(S)·(ε|Sᶜ|/(N-1) + β) ≤ β·N で抑えられる。β = 1 は常に成り立つので、上限は必ずある。 -/

/-- 流れの収支: 定常な c について、組 S から外へ流れ出る量と外から S へ流れ込む量は等しい。
c の非負性は要らない。 -/
theorem flow_balance (M : Mat n) (hM : ∀ i, ∑ j, M i j = 1) (S : Finset n) (c : n → ℚ)
    (hc : ∀ j, ∑ i, c i * M i j = c j) :
    ∑ k ∈ S, c k * ∑ j ∈ Sᶜ, M k j = ∑ k ∈ Sᶜ, c k * ∑ j ∈ S, M k j := by
  have hrowc : ∀ k, ∑ j ∈ Sᶜ, M k j = 1 - ∑ j ∈ S, M k j := by
    intro k
    have := sum_add_sum_compl S (M k)
    rw [hM k] at this
    linarith
  have hT : ∑ j ∈ Sᶜ, c j = ∑ k, c k * ∑ j ∈ Sᶜ, M k j := by
    calc ∑ j ∈ Sᶜ, c j = ∑ j ∈ Sᶜ, ∑ k, c k * M k j :=
          sum_congr rfl fun j _ => (hc j).symm
      _ = ∑ k, ∑ j ∈ Sᶜ, c k * M k j := sum_comm
      _ = ∑ k, c k * ∑ j ∈ Sᶜ, M k j := by simp_rw [mul_sum]
  have hsplit := sum_add_sum_compl S (fun k => c k * ∑ j ∈ Sᶜ, M k j)
  have hC : ∑ k ∈ Sᶜ, c k * ∑ j ∈ Sᶜ, M k j
      = ∑ k ∈ Sᶜ, c k - ∑ k ∈ Sᶜ, c k * ∑ j ∈ S, M k j := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by rw [hrowc k]; ring
  linarith

/-- 組 S の全員の予算が ε 以上で、外の各人から S への E' の流れが β 以下なら、
c(S) · ε|Sᶜ|/(N-1) ≤ β · c(Sᶜ)。 -/
theorem farm_bound (hN : 2 ≤ Fintype.card n) (E : Mat n) (hE : IsStochastic E)
    (S : Finset n) (ε β : ℚ) (hfloor : ∀ i ∈ S, ε ≤ E i i)
    (hinflow : ∀ k ∉ S, ∑ j ∈ S, vcb E k j ≤ β)
    (c : n → ℚ) (hc0 : ∀ i, 0 ≤ c i) (hc : ∀ j, ∑ i, c i * vcb E i j = c j) :
    (∑ i ∈ S, c i) * (ε * (Sᶜ.card : ℚ) / (Fintype.card n - 1)) ≤ β * ∑ k ∈ Sᶜ, c k := by
  have hpos : (0 : ℚ) < (Fintype.card n : ℚ) - 1 := by
    have : (2 : ℚ) ≤ Fintype.card n := by exact_mod_cast hN
    linarith
  have hV := vcb_stochastic hN E hE
  have hbal := flow_balance (vcb E) hV.2 S c hc
  -- S の各人の行から、外へ少なくとも ε|Sᶜ|/(N-1) が漏れる
  have hleak : ∀ i ∈ S,
      ε * (Sᶜ.card : ℚ) / (Fintype.card n - 1) ≤ ∑ j ∈ Sᶜ, vcb E i j := by
    intro i hi
    have hj : ∀ j ∈ Sᶜ, ε / (Fintype.card n - 1) ≤ vcb E i j := by
      intro j hj
      have hij : i ≠ j := fun h => (mem_compl.mp hj) (h ▸ hi)
      simp only [vcb, hij, ite_false]
      have h1 : ε / (Fintype.card n - 1) ≤ E i i / (Fintype.card n - 1) :=
        div_le_div_of_nonneg_right (hfloor i hi) hpos.le
      linarith [hE.1 i j]
    calc ε * (Sᶜ.card : ℚ) / (Fintype.card n - 1)
        = ∑ j ∈ Sᶜ, ε / (Fintype.card n - 1) := by
          rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ j ∈ Sᶜ, vcb E i j := sum_le_sum hj
  calc (∑ i ∈ S, c i) * (ε * (Sᶜ.card : ℚ) / (Fintype.card n - 1))
      = ∑ i ∈ S, c i * (ε * (Sᶜ.card : ℚ) / (Fintype.card n - 1)) := by rw [sum_mul]
    _ ≤ ∑ i ∈ S, c i * ∑ j ∈ Sᶜ, vcb E i j :=
        sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hleak i hi) (hc0 i)
    _ = ∑ k ∈ Sᶜ, c k * ∑ j ∈ S, vcb E k j := hbal
    _ ≤ ∑ k ∈ Sᶜ, c k * β :=
        sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hinflow k (mem_compl.mp hk)) (hc0 k)
    _ = β * ∑ k ∈ Sᶜ, c k := by rw [← sum_mul]; ring

/-- 占有の形: Σc = N なら c(S) · (ε|Sᶜ|/(N-1) + β) ≤ β·N。
つまり組の占有 c(S)/N は β / (β + ε|Sᶜ|/(N-1)) 以下。 -/
theorem farm_share_bound (hN : 2 ≤ Fintype.card n) (E : Mat n) (hE : IsStochastic E)
    (S : Finset n) (ε β : ℚ) (hfloor : ∀ i ∈ S, ε ≤ E i i)
    (hinflow : ∀ k ∉ S, ∑ j ∈ S, vcb E k j ≤ β)
    (c : n → ℚ) (hc0 : ∀ i, 0 ≤ c i) (hc : ∀ j, ∑ i, c i * vcb E i j = c j)
    (hsum : ∑ i, c i = Fintype.card n) :
    (∑ i ∈ S, c i) * (ε * (Sᶜ.card : ℚ) / (Fintype.card n - 1) + β)
      ≤ β * Fintype.card n := by
  have h := farm_bound hN E hE S ε β hfloor hinflow c hc0 hc
  have hs := sum_add_sum_compl S c
  calc (∑ i ∈ S, c i) * (ε * (Sᶜ.card : ℚ) / (Fintype.card n - 1) + β)
      = (∑ i ∈ S, c i) * (ε * (Sᶜ.card : ℚ) / (Fintype.card n - 1)) + β * ∑ i ∈ S, c i := by
        ring
    _ ≤ β * ∑ k ∈ Sᶜ, c k + β * ∑ i ∈ S, c i := by linarith
    _ = β * (∑ i ∈ S, c i + ∑ k ∈ Sᶜ, c k) := by ring
    _ = β * Fintype.card n := by rw [hs, hsum]

/-! ### P2: 全員の予算が正なら、貢献度は一意に決まる

ペロン＝フロベニウスの定理は使わない。2つの定常解の差 d も定常（成分の和は0）なので、
d が正の人の組 S に `flow_balance` を当てはめる。S から外への流れは非負、外から S への流れは
非正なので、どちらも0。E' の非対角が正なら、S が空でも全体でもない限り S から外への流れは正になり、
矛盾する。S が全体なら和が正になって矛盾する。よって d ≤ 0。-d にも同じ議論を当てて d = 0。

既約性・非周期性は経由しない（非周期性は、べき乗法を使わない決定 D3 のもとでは要らない）。
解の存在は扱わない。 -/

/-- P2 の前半: 全員の予算が正なら、E' の非対角はすべて正。 -/
theorem vcb_offdiag_pos (hN : 2 ≤ Fintype.card n) (E : Mat n) (hE : IsStochastic E)
    (hpos : ∀ i, 0 < E i i) (i j : n) (hij : i ≠ j) : 0 < vcb E i j := by
  have hden : (0 : ℚ) < (Fintype.card n : ℚ) - 1 := by
    have : (2 : ℚ) ≤ Fintype.card n := by exact_mod_cast hN
    linarith
  simp only [vcb, hij, ite_false]
  exact add_pos_of_nonneg_of_pos (hE.1 i j) (div_pos (hpos i) hden)

/-- 非対角が正の行確率行列では、和が0の定常ベクトルは非正。 -/
theorem stationary_nonpos (M : Mat n) (hM0 : ∀ i j, 0 ≤ M i j) (hM : ∀ i, ∑ j, M i j = 1)
    (hoff : ∀ i j, i ≠ j → 0 < M i j)
    (d : n → ℚ) (hd : ∀ j, ∑ i, d i * M i j = d j) (hsum : ∑ i, d i = 0) :
    ∀ i, d i ≤ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨i, hi⟩ := h
  set S := univ.filter (fun k => 0 < d k) with hSdef
  have hiS : i ∈ S := by simp [hSdef, hi]
  have hbal := flow_balance M hM S d hd
  have hout : 0 ≤ ∑ k ∈ S, d k * ∑ j ∈ Sᶜ, M k j :=
    sum_nonneg fun k hk => by
      have : 0 < d k := by simpa [hSdef] using hk
      exact mul_nonneg this.le (sum_nonneg fun j _ => hM0 k j)
  have hin : ∑ k ∈ Sᶜ, d k * ∑ j ∈ S, M k j ≤ 0 :=
    sum_nonpos fun k hk => by
      have : d k ≤ 0 := by
        have : ¬ 0 < d k := by simpa [hSdef] using hk
        linarith
      nlinarith [mul_nonneg (neg_nonneg.mpr this) (sum_nonneg fun j (_ : j ∈ S) => hM0 k j)]
  have hzero : ∑ k ∈ S, d k * ∑ j ∈ Sᶜ, M k j = 0 := by linarith
  by_cases hall : ∀ k, 0 < d k
  · have : 0 < ∑ k, d k := sum_pos (fun k _ => hall k) ⟨i, mem_univ i⟩
    linarith
  · push_neg at hall
    obtain ⟨j, hj⟩ := hall
    have hjS : j ∈ Sᶜ := by simp [hSdef]; linarith
    have hij : i ≠ j := fun h => by rw [h] at hi; linarith
    have hterm : d i * ∑ j ∈ Sᶜ, M i j = 0 :=
      (sum_eq_zero_iff_of_nonneg fun k hk => by
          have : 0 < d k := by simpa [hSdef] using hk
          exact mul_nonneg this.le (sum_nonneg fun j _ => hM0 k j)).mp hzero i hiS
    have hflow : 0 < ∑ j ∈ Sᶜ, M i j :=
      lt_of_lt_of_le (hoff i j hij) (single_le_sum (fun k _ => hM0 i k) hjS)
    have : 0 < d i * ∑ j ∈ Sᶜ, M i j := mul_pos hi hflow
    linarith

/-- 非対角が正の行確率行列では、和が等しい定常ベクトルは一致する。 -/
theorem stationary_unique (M : Mat n) (hM0 : ∀ i j, 0 ≤ M i j) (hM : ∀ i, ∑ j, M i j = 1)
    (hoff : ∀ i j, i ≠ j → 0 < M i j)
    (c c' : n → ℚ) (hc : ∀ j, ∑ i, c i * M i j = c j) (hc' : ∀ j, ∑ i, c' i * M i j = c' j)
    (hsum : ∑ i, c i = ∑ i, c' i) : c = c' := by
  have hd : ∀ j, ∑ i, (c i - c' i) * M i j = c j - c' j := by
    intro j; simp only [sub_mul, sum_sub_distrib, hc j, hc' j]
  have hd' : ∀ j, ∑ i, (c' i - c i) * M i j = c' j - c j := by
    intro j; simp only [sub_mul, sum_sub_distrib, hc j, hc' j]
  have hs : ∑ i, (c i - c' i) = 0 := by rw [sum_sub_distrib]; linarith
  have hs' : ∑ i, (c' i - c i) = 0 := by rw [sum_sub_distrib]; linarith
  have h1 := stationary_nonpos M hM0 hM hoff _ hd hs
  have h2 := stationary_nonpos M hM0 hM hoff _ hd' hs'
  funext i
  linarith [h1 i, h2 i]

/-- P2: 全員の予算が正なら、c E' = c かつ Σc = N を満たす c はただ1つ。 -/
theorem contributions_unique (hN : 2 ≤ Fintype.card n) (E : Mat n) (hE : IsStochastic E)
    (hpos : ∀ i, 0 < E i i) (c c' : n → ℚ)
    (hc : ∀ j, ∑ i, c i * vcb E i j = c j) (hc' : ∀ j, ∑ i, c' i * vcb E i j = c' j)
    (hsum : ∑ i, c i = ∑ i, c' i) : c = c' :=
  have hV := vcb_stochastic hN E hE
  stationary_unique (vcb E) hV.1 hV.2 (vcb_offdiag_pos hN E hE hpos) c c' hc hc' hsum

/-- 自然回収（0 < γ ≤ 1）の直後は、予算制約の下限 D12 が無くても貢献度は一意に決まる。
一意性が崩れうるのは、自然回収と自然回収のあいだに予算を使い切った人が出たときだけである。 -/
theorem contributions_unique_after_recover (hN : 2 ≤ Fintype.card n) (E : Mat n)
    (hE : IsStochastic E) (γ : ℚ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (c c' : n → ℚ)
    (hc : ∀ j, ∑ i, c i * vcb (recover E γ) i j = c j)
    (hc' : ∀ j, ∑ i, c' i * vcb (recover E γ) i j = c' j)
    (hsum : ∑ i, c i = ∑ i, c' i) : c = c' :=
  contributions_unique hN (recover E γ) (recover_stochastic E hE γ hγ0.le hγ1)
    (fun i => lt_of_lt_of_le hγ0 (recover_budget E hE γ hγ1 i)) c c' hc hc' hsum

/-! ### P5: 加入（論文 (3.69)）は不変条件を保ち、既存メンバーの貢献度を変えない

新メンバーを `none`、既存メンバー i を `some i` で表す。 -/

/-- N+1 人目の加入。c は加入直前の貢献度（決定 D8）。 -/
def join (E : Mat n) (c : n → ℚ) : Mat (Option n) :=
  fun i j =>
    match i, j with
    | some i, some j => if i = j then E i i else (Fintype.card n - 1) / Fintype.card n * E i j
    | some i, none => (1 - E i i) / Fintype.card n
    | none, some j => c j / Fintype.card n
    | none, none => 0

/-- 加入後の貢献度: 既存メンバーは据え置き、新メンバーは1。 -/
def joinC (c : n → ℚ) : Option n → ℚ
  | some i => c i
  | none => 1

section join
variable (hN : 2 ≤ Fintype.card n)
include hN

omit hN in
lemma card_option_sub_one : ((Fintype.card (Option n) : ℚ) - 1) = Fintype.card n := by
  simp [Fintype.card_option]

lemma cardQ_pos : (0 : ℚ) < Fintype.card n := by
  have : (2 : ℚ) ≤ Fintype.card n := by exact_mod_cast hN
  linarith

lemma cardQ_sub_one_pos : (0 : ℚ) < Fintype.card n - 1 := by
  have : (2 : ℚ) ≤ Fintype.card n := by exact_mod_cast hN
  linarith

theorem join_stochastic (E : Mat n) (hE : IsStochastic E) (c : n → ℚ)
    (hc0 : ∀ i, 0 ≤ c i) (hcs : ∑ i, c i = Fintype.card n) :
    IsStochastic (join E c) := by
  obtain ⟨hnn, hrow⟩ := hE
  have hNpos := cardQ_pos hN
  have h1 := cardQ_sub_one_pos hN
  have hle : ∀ i, E i i ≤ 1 := fun i => by
    have := single_le_sum (fun j _ => hnn i j) (mem_univ i)
    rw [hrow i] at this
    exact this
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · rcases i with _ | i <;> rcases j with _ | j <;> simp only [join]
    · exact le_refl 0
    · exact div_nonneg (hc0 j) hNpos.le
    · exact div_nonneg (sub_nonneg.mpr (hle i)) hNpos.le
    · split_ifs
      · exact hnn i i
      · exact mul_nonneg (div_nonneg h1.le hNpos.le) (hnn i j)
  · rw [Fintype.sum_option]
    rcases i with _ | i
    · simp only [join, div_eq_mul_inv]
      rw [← sum_mul, hcs, mul_inv_cancel₀ hNpos.ne']
      ring
    · simp only [join]
      have h := hrow i
      rw [sum_split_diag _ i] at h
      rw [sum_split_diag _ i, if_pos rfl]
      have : ∑ j ∈ univ.erase i, (if i = j then E i i else
          (Fintype.card n - 1) / Fintype.card n * E i j)
          = (Fintype.card n - 1) / Fintype.card n * ∑ j ∈ univ.erase i, E i j := by
        rw [mul_sum]
        refine sum_congr rfl fun j hj => ?_
        rw [if_neg (fun h => (ne_of_mem_erase hj) h.symm)]
      have hs : ∑ j ∈ univ.erase i, E i j = 1 - E i i := by linarith
      rw [this, hs]
      field_simp
      ring

/-- 加入後の E' の成分。既存メンバーどうしは加入前の E' の (N-1)/N 倍にそろう。 -/
lemma vcb_join_some_some (E : Mat n) (c : n → ℚ) (i j : n) :
    vcb (join E c) (some i) (some j) = (Fintype.card n - 1) / Fintype.card n * vcb E i j := by
  have hNpos := cardQ_pos hN
  have h1 := cardQ_sub_one_pos hN
  by_cases h : i = j
  · subst h; simp [vcb]
  · simp only [vcb, join, Option.some.injEq, h, ite_false, card_option_sub_one, ite_true]
    field_simp

omit hN in
lemma vcb_join_none_some (E : Mat n) (c : n → ℚ) (j : n) :
    vcb (join E c) none (some j) = c j / Fintype.card n := by
  simp [vcb, join]

theorem join_fixed_point (E : Mat n) (c : n → ℚ) (hcs : ∑ i, c i = Fintype.card n)
    (hc : ∀ j, ∑ i, c i * vcb E i j = c j) :
    ∀ j, ∑ i, joinC c i * vcb (join E c) i j = joinC c j := by
  have hNpos := cardQ_pos hN
  intro j
  rw [Fintype.sum_option]
  rcases j with _ | j
  · -- 新メンバーの列: Σ c_i * (1/N) = 1
    have hcol : ∀ i, vcb (join E c) (some i) none = 1 / Fintype.card n := by
      intro i
      simp only [vcb, join, reduceCtorEq, ite_false, card_option_sub_one, ite_true]
      field_simp
      ring
    simp only [joinC, hcol, vcb_diag, mul_zero, zero_add]
    rw [← sum_mul, hcs]
    field_simp
  · simp only [joinC, vcb_join_some_some hN, vcb_join_none_some]
    have : ∑ i, c i * ((Fintype.card n - 1) / Fintype.card n * vcb E i j)
        = (Fintype.card n - 1) / Fintype.card n * c j := by
      rw [← hc j, mul_sum]
      exact sum_congr rfl fun i _ => by ring
    rw [this]
    field_simp
    ring

end join

end Picsy
