# lab-picsy

鈴木健「伝播投資貨幣 PICSY」を、曖昧さの無い仕様に落とし、実装して、壊れないことをある程度まで示すための七夕研の社内小研究です。Lean による形式化の勉強も兼ねています。

## ねらい

1. **仕様の確定**: 博士論文の定義を正本にして、論文が決めていない箇所をこちらで決め、決めたことを明記する（[docs/spec.md](docs/spec.md)）。
2. **形式化**: 保存されるべき性質（行確率性・非負性・加入で既存メンバーの貢献度が動かないこと等）を Lean で証明する。
3. **シミュレーション**: n=100 程度の系で取引・自然回収・加入・離脱を回し、不変量が崩れないか、発散するパラメータが無いかを測る。

## 一次資料

Ken Suzuki, *Propagational Investment Currency SYstem (PICSY): Proposing a New Currency System Using Social Computing*, 博士論文, 東京大学大学院総合文化研究科, 2009年3月.

公式に公開された版が見当たらないため、PDF はリポジトリに含めていません（`docs/resources/` は `.gitignore` 対象）。本リポジトリでは章・節・式番号で参照します。

## 構成

| パス | 中身 |
|---|---|
| `docs/spec.md` | 仕様書（仮想中央銀行法）。論文の式番号との対応、未定義箇所の決定 |
| `docs/related-work.md` | 先行研究と新規性の判定 |
| `docs/experiments/` | シミュレーションの実験記録 |
| `docs/resources/` | 一次資料の置き場（ローカルのみ） |
| `lean/` | Lean 4 + Mathlib による性質の証明（P1〜P9 済み）。`lake exe cache get` → `lake build` |
| `python/` | 参照実装（`picsy.core`）、シミュレータ（`picsy.sim`）、性質テスト。`uv sync` → `uv run pytest` |
