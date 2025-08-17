** ただし、いま流行の「巨大SFT＋反復収集（expert iteration）で miniF2F の Pass\@k を少し伸ばす」だけだと**競争が激しく差別化が難い**。新規性は**評価設計・データ品質・検索/計画・転移**に寄せると出しやすい。

# いま何が“埋まってきた”のか

* **大規模SFT＋反復収集の路線**は、Goedel-Proverが「自然文→Lean4 の大量自動形式化（約164万件）＋Lean検証での反復収集」だけでSOTA級を達成し、既存RL系（DeepSeek-Prover-V1.5）をPass\@32で上回ることを示しました。つまり“正攻法のスケール”はもう強力な土台になっています。([arXiv][1])
* \*\*RL＋探索（MCTS等）\*\*は既にDeepSeek側が重厚にやっており、同じ土俵での僅差更新は計算資源勝負になりがちです。([arXiv][2])

# それでも“新規”にしやすい領域（具体テーマ）

1. **自動形式化（NL→Lean）の“正しさ”を測る仕組み**

   * 形式化の忠実度評価（statement semantics の保持）や、対訳の系統誤りを検出するメトリクス・治具の提案。Lean4向けの**オートフォーマライゼーション評価ベンチ**も動き始めていますが、尺度は発展途上です。([arXiv][3])

2. **分布ずれへの強さ（miniF2F↔ProofNet↔Lean-Workbook）**

   * ベンチの性質が違うと伸び方が変わる（高校数学中心の miniF2F と大学教科書系の ProofNet は内容分布が異なる）。**一般化能力**を“転移スコア”や“性能落差”で系統評価→**ドメイン適応**の手法を載せるのは新規性が出ます。([GitHub][4], [arXiv][5])

3. **RAG/検索×証明（LeanDojo系の活用）**

   * ライブラリ（mathlib）からの**定理・補題の検索**を一段深く設計（前提選択・段階的引用・キャッシュ最適化）。LeanDojo は基盤を提供しており、**探索+検索**の結合や**証明途中での動的RAG**に攻めどころがあります。([arXiv][6], [Leandojo][7], [NeurIPS Papers][8])

4. **新しい評価指標（Pass\@k だけじゃない）**

   * 例：**公理依存の最小化**（`#print axioms`でクラシカル依存を低減）、**証明長/検証時間/再現率**、**証明圧縮率**、**lemma再利用率**、**constructiveモードでの成功率**など。こうした“品質”と“頑健性”の評価設計は未開拓です。

5. **証明の“修復・圧縮・正規化”**

   * 生成証明の**自動修理（proof repair）**や**短縮（compression）**の学習器はニッチで新規性が高い。Pass\@k を上げるだけでなく**検証時間短縮**や**可読性**を指標化できます。

6. **ステップ型（タクティク駆動）と全文型（whole-proof）のハイブリッド**

   * “下書き→対話的補修→最終証明”などの**段階設計**や、探索時間を動的に配分する**適応サンプリング**は差別化しやすい。既存は whole-proof（Goedel）と RL+探索（DeepSeek）が主流。両者の良さを繋ぐ余地があります。([arXiv][1])

7. **ベンチ拡張とリーク対策**

   * miniF2F/ProofNetの**パラフレーズ版**や**難易度調整版**を公開し、**データリーク検査**（重複・近傍検索）とセットで評価基盤を整える研究。最近はPutnam系や派生ベンチも出ていますが（例：**PutnamBench**、さらに派生の“-Solving”系）、設計空間は広いです。([arXiv][1])

8. **他システム（Coq/Isabelle）との相互運用・転写**

   * Leanで得た証明を他系へ**写像**、あるいは**中間表現**で相互変換する基盤作りは未成熟。ここはエンジニアリングの貢献でも新規性が立ちます。

9. **産業寄り応用（検証×プログラム）**

   * あなたの強み（コード最適化/コンパイラ）を活かし、**C/LLVM変換の正当性補題**や**最適化の前後同値性**の自動証明に寄せると**新規×実用**の両立が可能。

10. **計算コスト最適化の理論と実装**

* “同じPass\@32を**1/3のGPU時間**で達成”のような**効率最適化**（サンプリング配分、early-reject、Kernel検証のスケジューリング）は、実務上価値が高く論文化もしやすい。

# いま押さえるべき“事実ベース”

* Goedel-Prover：**大規模自動形式化（約164万）＋Lean検証の反復収集＋SFT主体**で miniF2F **Pass\@32=57.6%**、PutnamBench **7題**。公開サイトとarXivに詳細。([arXiv][1], [goedel-lm.github.io][9])
* DeepSeek-Prover-V1.5：**RL（PAF）＋MCTS**で miniF2F/ProofNetを強化した路線。([arXiv][2])
* ベンチの性格：**miniF2F**（高校〜オリンピック系）、**ProofNet**（大学教科書系）で分布が異なる。ここを跨いだ一般化は未踏が多い。([GitHub][4], [arXiv][5])

# すぐ着手できる“新規性を出しやすい設計”例

* **テーマ**：*「自動形式化の頑健性評価＋修復」*

  1. miniF2FとProofNetの**パラフレーズ増補**（意味保持）セットを自作
  2. NL→Lean 形式化器の**忠実度メトリクス**（意味一致判定＋Lean検証）を提案
  3. 不一致時に**反例的カウンター例**や**局所修正パッチ**を出す修復器を併設
  4. 指標：忠実度↑、修復成功率↑、最終Pass\@kの劣化≦X%
     （RAGはLeanDojoを利用、ベースラインにGoedel/DeepSeekを置く） ([arXiv][6], [NeurIPS Papers][8])

---

**まとめ**：SFT×反復収集の“スケール勝負”はやや飽和気味ですが、**評価・データ品質・分布横断・検索/計画統合・効率化**のラインは未開拓が多く、**新規性は十分に狙えます**。
ご希望なら、あなたの計算環境に合わせて\*\*1テーマ選定→実験設計（データ、指標、比較相手、リスク）\*\*まで一気に書き下ろします。

[1]: https://arxiv.org/abs/2502.07640?utm_source=chatgpt.com "Goedel-Prover: A Frontier Model for Open-Source Automated Theorem Proving"
[2]: https://arxiv.org/abs/2408.08152?utm_source=chatgpt.com "DeepSeek-Prover-V1.5: Harnessing Proof Assistant Feedback for Reinforcement Learning and Monte-Carlo Tree Search"
[3]: https://arxiv.org/html/2406.06555v1?utm_source=chatgpt.com "An Evaluation Benchmark for Autoformalization in Lean4"
[4]: https://github.com/openai/miniF2F?utm_source=chatgpt.com "openai/miniF2F: Formal to Formal Mathematics Benchmark"
[5]: https://arxiv.org/abs/2302.12433?utm_source=chatgpt.com "ProofNet: Autoformalizing and Formally Proving ..."
[6]: https://arxiv.org/abs/2306.15626?utm_source=chatgpt.com "[2306.15626] LeanDojo: Theorem Proving with Retrieval- ..."
[7]: https://leandojo.org/leandojo.html?utm_source=chatgpt.com "LeanDojo: Theorem Proving with Retrieval-Augmented ..."
[8]: https://papers.neurips.cc/paper_files/paper/2023/file/4441469427094f8873d0fecb0c4e1cee-Paper-Datasets_and_Benchmarks.pdf?utm_source=chatgpt.com "LeanDojo: Theorem Proving with Retrieval-Augmented ..."
[9]: https://goedel-lm.github.io/?utm_source=chatgpt.com "Goedel-Prover"
