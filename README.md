
---

##  全体構成図（Pipeline Overview）

```txt
          +---------------------------+
          |  Wikipedia / 教科書記事   |
          +------------+--------------+
                       ↓
            ① 自然言語定理テキスト生成
               (auto_extract_wiki_proofs.py)
                       ↓
            ② 命題（Proposition）抽出
               (loop.py + extract_theorem_statement)
                       ↓
            ③ 証明ステップ分割 (Chain-of-Thought)
               (splitter.py)
                       ↓
            ④ tactic へのマッピング
               (mapper.py)
                       ↓
            ⑤ Lean4 による検証
               (verifier.py)
                       ↓
            ⑥ ログ保存 + CSV可視化
               (results/wiki_logs + analyze_results_csv.py)
```

---

##  ステップ詳細

###  ① 自然言語の証明文生成（LLM）

* ファイル: `auto_extract_wiki_proofs.py`
* 処理:

  * Wikipediaのカテゴリ（例: `Mathematical theorems`）から記事タイトルを自動取得
  * 各タイトルを LLM に投げて「定理本文＋簡単な証明」テキストを生成
  * `.json` 形式で `data/wiki_auto/` に保存

---

###  ② 命題抽出（命題ステージの導入）

* ファイル: `loop.py`（関数：`extract_theorem_statement`）
* 処理:

  * LLM に「この自然言語証明文から命題（定理の主張）を抽出してLeanで表現せよ」とプロンプト
  * `theorem my_prop : <Lean命題>` を生成
  * 証明すべき対象が `True` でなくなる（←重要）

---

###  ③ Chain-of-Thought（思考分解）ステップ

* ファイル: `splitter.py`
* 処理:

  * 自然言語証明を意味のある論理的サブステップに分割
  * 「したがって」「ゆえに」「なぜなら」などに注目して文を分割
  * 出力は `["Step1: ..., Step2: ..."]` のリスト形式

---

###  ④ tactic マッピング

* ファイル: `mapper.py`
* 処理:

  * 各ステップを Lean4 の tactic に変換
  * プロンプトで「この自然言語文はどうやって証明すればいい？」と尋ねる
  * 出力は `["exact this", "apply that", ...]`

---

###  ⑤ Lean4形式による検証（Verifier Loop）

* ファイル: `verifier.py`
* 処理:

  * `lake build` & `lean --make` を使って実際にLeanで証明が通るかを判定
  * 失敗した場合はエラー解析→フィードバックプロンプト→再試行（最大 N 回）

---

###  ⑥ 結果の記録と可視化

* ファイル:

  * `results/wiki_logs/result_log.jsonl`
  * `analyze_results_csv.py`
* 処理:

  * 各命題ごとに：

    * 成功か？失敗か？何回の試行で成功したか？生成された tactic は？
  * CSVやグラフにして出力（成功率推移など）

---

## 実行順まとめ（CLI）

```bash
# 1. Wikiから自然言語証明を大量取得
python scripts/auto_extract_wiki_proofs.py

# 2. 形式化パイプラインをバッチ実行（命題抽出→証明生成→検証）
python scripts/batch_loop_runner.py --input_dir data/wiki_auto --output_dir results/wiki_logs

# 3. 結果をCSVにまとめてグラフ可視化
python scripts/analyze_results_csv.py
```

---

##  特徴まとめ

| 特徴                    | 内容                         |
| --------------------- | -------------------------- |
|  命題抽出ステージ           | `True` ではなく意味ある定理命題を動的生成   |
|  Chain-of-Thought活用 | 論理的ステップに自動分割               |
|  フィードバックループ         | Lean失敗時はLLMへ再問い合わせ → 修正繰返し |
|  自動可視化              | 成功率・試行回数・トークン量などをCSV出力     |
|  教師なし・外部知識不要        | 入力＝自然言語証明テキストだけで構成可能       |

---

Q  
命題を抽出する際に、一個だけを選定する？  
複数の候補を挙げて、成功確率が高いものを採用する？

上はとりま却下！  
miniF2F（データセット）から自然言語による証明文を生成させる。  
つまり、lean形式→自然言語してLLMによるLean形式に変換させる。その際の評価で元のデータセットでの比較で評価を行う。

仮想化：venv\Scripts\activate
