以下のようなイメージで、各スクリプトがどのようにデータを受け渡しながら動くかを示します。矢印で処理の流れを追えるようにしています。

```
┌─────────────────────────────────────────────────────────────────┐
│  1. 定理テキストを用意                                          │
│ ─────────────────────────────────────────────────────────────  │
│ 「results/theorem_descriptions.txt」                         │
│ └───┬──────────────────────────────────────────────────────────┘
│     │
│     ▼
│
│  2. Lean4証明生成＆検証スクリプト                               │
│ ─────────────────────────────────────────────────────────────  │
│  python scripts/batch_loop_runner.py                            │
│    --input_txt_block results/theorem_descriptions.txt           │
│    --output_dir     results/from_txt_logs                       │
│                                                                 │
│ 〔入力〕                                                          │
│   └─ ブロック分割後の「各定理（自然言語＋形式化命題）」          │
│                                                                 │
│ 〔処理（各定理ごと）〕                                            │
│   1) 自然言語説明を読み取り → Lean4 の定理文を組み立てる          │
│   2) GPT（map_to_tactic）で「タクティック列」を生成               │
│   3) clean_tactic で Markdown 記法を取り除きクリーン化           │
│   4) verify_tactics で Lean4に流し込んでサブゴールが消えるか検証 │
│       └─ 成功すれば `.lean` ファイル ⇒ `results/from_txt_logs/◯◯.lean` に出力
│       └─ 成否・試行回数・タクティック列を        │
│            `results/from_txt_logs/result_log.jsonl` に書き込む  │
│                                                                 │
│ 〔出力〕                                                          │
│   ├─ 成功：`results/from_txt_logs/<定理ID>.lean`（Lean4ソース）  │
│   └─ 全ブロックの結果ログ：                                   │
│        `results/from_txt_logs/result_log.jsonl`                 │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
          │
          ▼
┌─────────────────────────────────────────────────────────────────┐
│  3. サマリ＆可視化スクリプト                                     │
│ ─────────────────────────────────────────────────────────────  │
│  a) サンプル抽出用                      (簡易レポート)            │
│     python scripts/analyze_results.py                             │
│     ├─ 「成功定理」「失敗定理」をそれぞれ `samples/` フォルダへ  │
│     └─ コンソールに「成功件数／失敗件数／成功率」を出力          │
│                                                                   │
│  b) CSV＋ヒストグラム生成                 (詳細レポート)          │
│     python scripts/analyze_results_csv.py                         │
│     ├─ `results/from_txt_logs/analysis/summary.csv` を出力        │
│     │    （各定理ID・成否・タクティック長・Leanコード長など）      │
│     ├─ `results/from_txt_logs/analysis/theorem_length_hist.png`   │
│     │    （タクティックの長さ分布を可視化）                        │
│     └─ `results/from_txt_logs/analysis/lean_length_hist.png`      │
│          （Lean ソース文字数の分布を可視化）                       │
│                                                                   │
└─────────────────────────────────────────────────────────────────┘

```

---

### フローの要点まとめ

1. **定理テキストの準備**

   * `results/theorem_descriptions.txt` に、複数ブロック（各定理）の形式化命題＋自然言語説明を記述。

2. **自動証明サイクル**

   * `batch_loop_runner.py` を実行すると、

     * 各ブロックを分割して読み込み、
     * GPT→タクティック生成 → Lean4 検証 → 成功なら `.lean` 書き出し、
     * 成否ログ（JSONL）を蓄積。
   * 出力先フォルダ：`results/from_txt_logs/`

3. **レポート生成**

   * **サンプル抽出（analyze\_results.py）**

     * 成功／失敗それぞれの事例を `samples/` フォルダへコピーしつつ、
     * コンソールに成功率だけざっくり表示。
   * **CSV＋グラフ（analyze\_results\_csv.py）**

     * JSONL ログを読み込み、summary.csv を生成。
     * タクティック長／Leanソース長のヒストグラム PNG を作成。
     * 保存先：`results/from_txt_logs/analysis/`

---


Q  
命題を抽出する際に、一個だけを選定する？  
複数の候補を挙げて、成功確率が高いものを採用する？

上はとりま却下！  
miniF2F（データセット）から自然言語による証明文を生成させる。  
つまり、lean形式→自然言語してLLMによるLean形式に変換させる。その際の評価で元のデータセットでの比較で評価を行う。

仮想化：venv\Scripts\activate  
set OPENAI_API_KEY=

