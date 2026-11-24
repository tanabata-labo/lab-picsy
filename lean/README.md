# PicsyLean

`docs/spec.md` §5 の性質を Lean 4 + Mathlib で証明する。状態は有理数の行列（`Mat n := n → n → ℚ`）。

| 性質 | 定理 | 状態 |
|---|---|---|
| P1 | `vcb_stochastic`, `vcb_diag` | 証明済み |
| P2 | — | 未着手 |
| P3 | `transact_stochastic` | 証明済み |
| P4 | `recover_stochastic`, `recover_budget`, `vcb_recover` | 証明済み |
| P5 | — | 未着手（加入。型が `n` から `Option n` 等に変わる） |
| P6 | — | 未着手（除去） |

ビルド: `lake exe cache get` → `lake build`。`import Mathlib` は読み込みに20分以上かかったので、必要なモジュールだけを import している。
