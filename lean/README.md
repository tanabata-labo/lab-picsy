# PicsyLean

`docs/spec.md` §5 の性質を Lean 4 + Mathlib で証明する。状態は有理数の行列（`Mat n := n → n → ℚ`）。

| 性質 | 定理 | 状態 |
|---|---|---|
| P1 | `vcb_stochastic`, `vcb_diag` | 証明済み |
| P2 | — | 未着手 |
| P3 | `transact_stochastic` | 証明済み |
| P4 | `recover_stochastic`, `recover_budget`, `vcb_recover` | 証明済み |
| P5 | `join_stochastic`, `join_fixed_point` | 証明済み。新メンバーを `none` とする `Option n` 上で、加入前の固定点 c に1を足したものが加入後も固定点 |
| P6 | `remove_stochastic` | 証明済み。除去後の型は `{j // j ≠ d}` |
| P7 | `farm_absorbs` | 証明済み。予算0で組の外を評価しない組 S があれば、組の外で予算が正の人の貢献度は0（link farm が吸収集合になる） |
| P8 | `flow_balance`, `farm_bound`, `farm_share_bound` | 証明済み。組 S の全員の予算が ε 以上で、外から S への流れが β 以下なら c(S)·(ε·#Sᶜ/(N-1) + β) ≤ β·N |

ビルド: `lake exe cache get` → `lake build`。`import Mathlib` は読み込みに20分以上かかったので、必要なモジュールだけを import している。
