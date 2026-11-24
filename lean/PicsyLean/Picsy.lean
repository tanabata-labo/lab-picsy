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

end Picsy
