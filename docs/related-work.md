# 先行研究と新規性の判定（2026-11-24 調査）

本研究の主張（[spec.md](spec.md) §5 の P2・P7・P8、決定 D12 の予算の下限 ε）が、先行研究でどこまで言われているかを調べた。英語文献は Semantic Scholar・Crossref・OpenAlex・arXiv・DBLP・Google Scholar、日本語文献は NDL・CiNii Research・IRDB・東大リポジトリ・国会会議録で探した。J-STAGE は接続できず未確認。

## 結論

| 主張 | 先行研究での扱い | 判定 |
|---|---|---|
| P7（予算を使い切った組が吸収集合になる） | 閉じた組が吸収し外が0になるのはマルコフ連鎖の標準的な事実。PageRank の減衰なしの場合（Bianchini ら 2.3節）、EigenTrust の考察（事前に信頼されたピアが無いと共謀集団から抜け出せない）にある | 数学は既知。**PICSY の予算の使い切りがこの吸収を生み、論文5.1節の主張と逆になる**という指摘は先行が見つからない |
| P8（予算の下限による占有の上限） | 「強制的な流出の下限」と「流入 = 流出」で組を抑える論法は Zhang ら 2004 の定理1と Bianchini らのエネルギー収支にある | 証明法と上限の形は先行あり。予算を $N-1$ 人へ均等に配る規則から出る式 $c(S)/N \leq \beta / (\beta + \varepsilon \lvert S^c \rvert / (N-1))$ そのものは見つからない |
| ε と η の比較 | η は PageRank のテレポート、EigenTrust の $(1-a)C + ap$ と同じ形。節点ごとの最低流出の近縁は Zhang らの personalized-ε と Hopcroft–Sheldon のリスタート確率の制限 | **下限は貢献度の定義を変えないので副作用（定価の近似・加入時のずれ）が小さい**という比較は先行が見つからない |
| P2（全員の予算が正なら一意） | 1段で既約になれば定常分布が一意なのは教科書的事実。EigenTrust もテレポートで既約になることを明記 | 結果は既知。新しいのはペロン＝フロベニウスを使わない流れの収支による証明と、Lean での形式化 |

PICSY を第三者が実装・シミュレーション・数理分析した文献は、日本語でも英語でも見つからなかった。見つかった PICSY の文献は鈴木健本人のものに限られる。

したがって本研究の新しさは「新しい定理」ではなく、次の点に置く。

1. PageRank・評判システムで知られた吸収と上限の議論を PICSY の仮想中央銀行法に当てはめ、論文5.1節の主張が成り立たないことを示したこと
2. 貢献度の定義を変えない対策（予算の下限 ε）の設計と、η 正則化との副作用の比較
3. 論文が決めていない箇所の明文化（D1〜D12）と、Lean による形式化

## 文献

確認の度合いは「本文確認」（全文か該当箇所を読んだ）、「書誌確認」（DB で実在を確認、本文は未読）で示す。

### PICSY

| 文献 | 確認 | 関係 |
|---|---|---|
| 鈴木健「PICSY（伝播投資貨幣）のデモソフト」IPA 未踏ソフトウェア創造事業 2002年度 成果報告（テーマ「伝播貨幣のデモンストレーションソフトの実装」）。https://www.ipa.go.jp/archive/files/000005742.pdf | 本文確認（年度は IPA の修了生ページで確認） | Java のエージェントシミュレータ。大規模シミュレーションは対象外と本人が記す |
| K. Suzuki, "How does propagational investment currency system change the world?", SAINT 2004 Workshops, IEEE. DOI 10.1109/SAINTW.2004.1268559 | 書誌確認 | 自己評価法の出典 |
| Ken Suzuki, *Propagational Investment Currency SYstem (PICSY): Proposing a New Currency System Using Social Computing*, 博士論文, 東京大学, 2009（甲第24286号、NDL 請求記号 UT51-2009-Q326） | 書誌確認。オンラインの公開版は見つからない（NDL は紙のみ、東大リポジトリに登録なし） | 本研究の正本 |
| 鈴木健「伝播投資貨幣PICSY」人工知能学会全国大会論文集 JSAI2009, 3E3-NFC2-10. DOI 10.11517/pjsai.jsai2009.0_3e3nfc210 | 本文確認（全2頁） | 仮想中央銀行法・取引・自然回収の式が載る、公開されて読める典拠。一意性・共謀・予算の下限には触れない |
| 鈴木健『なめらかな社会とその敵』勁草書房, 2013（筑摩書房版 2022） | 書誌確認 | 一般向けの解説。PICSY の章で共謀をどう扱うかは未確認 |
| E. G. Weyl, A. Tang ほか *Plurality*、5-7 "Social Markets" の脚注 | 本文確認 | PICSY を1段落で紹介するのみ |

### PageRank の link spam・共謀

| 文献 | 確認 | 関係 |
|---|---|---|
| M. Bianchini, M. Gori, F. Scarselli, "Inside PageRank", ACM TOIT 5(1), 92–128, 2005. DOI 10.1145/1052934.1052938 | 本文確認（写しで読んだ。引用前に ACM 版と照合） | P7・P8。定理4.2のエネルギー収支で組の得点を流入で抑える。2.3節に減衰なしでの吸収 |
| Z. Gyöngyi, H. Garcia-Molina, "Link Spam Alliances", VLDB 2005, p. 517– | 本文確認 | P8。最適なファームの得点の式。同盟は組の合計を増やさない |
| H. Zhang, A. Goel, R. Govindan, K. Mason, B. Van Roy, "Making Eigenvector-Based Reputation Systems Robust to Collusion", WAW 2004, LNCS 3243, 92–104. DOI 10.1007/978-3-540-30216-2_8 | 予稿で本文確認（出版版との一致は未確認） | P8 に最も近い。リセット確率 ε による強制流出と流入 = 流出から、共謀の増幅率が $O(1/\varepsilon)$ |
| J. Hopcroft, D. Sheldon, "Manipulation-Resistant Reputations Using Hitting Time", WAW 2007. DOI 10.1007/978-3-540-77004-6_6 | 本文確認 | 新規節点のリスタート確率を制限すれば sybil を抑えられる。加入時の扱いに関係 |
| R. Andersen ほか, "Robust PageRank and locally computable spam detection features", AIRWeb 2008. DOI 10.1145/1451983.1452000 | 本文確認 | 対策の別系統（寄与の上限） |
| R. Baeza-Yates, C. Castillo, V. López, "PageRank Increase under Different Collusion Topologies", AIRWeb 2005 | 書誌確認 | 本文未入手。引く前に読む |

### 評判・信用システム

| 文献 | 確認 | 関係 |
|---|---|---|
| S. D. Kamvar, M. T. Schlosser, H. Garcia-Molina, "The EigenTrust algorithm for reputation management in P2P networks", WWW 2003. DOI 10.1145/775152.775242 | 本文確認 | P7 を言葉で述べた考察と、全員が事前の信頼先へ最低限を流す仕組み（η に近い） |
| Z. Gyöngyi, H. Garcia-Molina, J. Pedersen, "Combating Web Spam with TrustRank", VLDB 2004 | 書誌確認 | テレポートを信頼された種に寄せる系統 |
| A. Cheng, E. Friedman, "Sybilproof reputation mechanisms", P2PECON 2005. DOI 10.1145/1080192.1080202 | 書誌確認（抄録のみ） | 対称な評判関数は sybilproof になれない。PICSY の c は対称型なので、上限で抑える緩和が要る理由になる |

## 残っている確認

- 博士論文5.1節の原文は、手元の PDF で照合してから引用する
- Zhang ら・Bianchini らは出版版との照合、Baeza-Yates らは本文の入手
- J-STAGE の全文検索（地域通貨研究などで PICSY に触れた論文）
- 『なめらかな社会とその敵』の PICSY の章
