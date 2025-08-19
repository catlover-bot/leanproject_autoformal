[“Goedel-Prover: A Frontier Model for Open-Source Automated Theorem Proving”](https://goedel-lm.github.io/)

# サマリー

**自然文の数学問題を Lean 4 に大量形式化（auto-formalization）→ その命題に対する“全文（whole-proof）生成”プローバを反復的に育てることで、既存オープンモデル（DeepSeek-Prover-V1.5）を上回る性能を達成**。コード・モデル・データも公開されています。([arXiv][1])

# 何がボトルネックで、どう解決した？

* **課題**：Lean の命題・証明データが少ない。
* **解決策（2本柱）**

  1. **自動形式化**：Numina などの自然文問題を Lean 4 命題に変換し、**1.64M（164万）件**の formal statements を構築（Goedel-Pset-v1）。その後、AoPS/Lean Workbook を追加し**計 1.78M件**まで拡張。形式化の正しさは LLM チェックも併用。([arXiv][1])
  2. **エキスパート反復（expert iteration）**：既存/自作プローバで証明候補を大量生成→**Lean で検証**→通った証明だけを学習に継ぎ足すサイクルを**8回**実施。最終的に \*\*Goedel-Pset-v1-solved（80万件超）\*\*の “命題＋正しい証明” を得る。([arXiv][1])

# どんなモデルをどう学習した？

* **プローバ**：ベースは **DeepSeek-Prover-V1.5-Base**。**強化学習なしの SFT だけ**で **Goedel-Prover-SFT** を作成（生成時は Lean と非対話の **whole-proof** 方式）。この SFT 版がすでに SOTA を更新。さらに **DPO/RL** を上乗せすると **Pass\@32 が 60%超**まで伸長。ただし **RL は“ショートカット”への過適合＆推論計算増に対する伸びの鈍化**も観測。([arXiv][1])
* **形式化器**：スタイル多様性のため**2系統**（A/B）を訓練。B は **Claude-3.5 Sonnet**で 23 万件を形式化→**Lean を通過した 17 万件**をペアとして再学習。**A と B を混ぜた方が汎化が良い**というアブレーションも提示。([arXiv][1])

# 主要結果（ベンチマーク）

* **miniF2F（Lean4, whole-proof）**：**Pass\@32 = 57.6%**（DeepSeek-V1.5-RL の \*\*50.0%\*\*に対し **+7.6pt**）。計算予算を増やしても一貫して優位（例：Pass\@3200 など）。([arXiv][1])
* **PutnamBench**：\*\*7題（Pass\@512）\*\*を解き **リーダーボード1位**。※当初 8 題と報告したが、1 題は形式化誤りのため除外と注記。([arXiv][1])
* **Lean Workbook**：**2.97万題**の新規正式証明を公開（従来合計 **1.57万**→**ほぼ倍増**）。([arXiv][1])

# どうやって“正しさ”を判定している？

* 生成した証明は **Lean コンパイラ（カーネル）の型検査**で機械的に検証。**通れば、その命題の正式な証明**と見なされます（whole-proof なので生成中は Lean と対話しないが、**判定は必ず Lean**）。([arXiv][1])

# 追加の分析・示唆

* **データ分布の違い**：**ProofNet は miniF2F/Lean-Workbook/NuminaTest と負の相関**。**Mathlib4 を入れると ProofNet は上がるが miniF2F は下がる**＝分布差への注意が必要。([arXiv][1])
* **外部簡約（SymPy）**：式簡約で一部の miniF2F を直接解けるが、主要スコアには**不採用**（効果が限定的）。([arXiv][1])

# なぜ重要？

* **データ不足の根本解決**（自動形式化＋反復収集）と**単純な SFT でも SOTA**という事実を示し、強化学習に依存しない強力なベースラインを提供。さらに**コード／モデル／データ**が公開され、後続研究の再現と発展が容易。([arXiv][1])

# 公開物（入手先）

* **論文**・**GitHub**（評価スクリプト含む）・**Hugging Face**（SFT/DPO モデル、Goedel-Pset-v1 / v1-solved、Lean-Workbook-proofs）。([arXiv][1])

---

もっと踏み込んだ内容（たとえば *miniF2F の評価コマンド例・推奨サンプリング設定・`sorry/axiom` 自動検出の運用*）まで必要なら、そのまま実行できる形で用意します。

[1]: https://arxiv.org/html/2502.07640v3 "Goedel-Prover: A Frontier Model for Open-Source Automated Theorem Proving"



# 作成したモデル（この研究の成果）

* **Goedel-Prover-SFT（約7B, LLaMA系）**
  既存ベース（DeepSeek-Prover-V1.5-Base）を**教師あり微調整のみ**で訓練した“whole-proof”生成モデル。**miniF2F Pass\@32=57.6%**で先行SOTA（DeepSeek-V1.5-RL）を+7.6pt上回る。Hugging Face公開版は**6.91Bパラメータ**表記。([arXiv][1], [Hugging Face][2])

* **Goedel-Prover-DPO（約7B）／Goedel-Prover-RL（GRPO）**
  SFTの上に**DPO**や**GRPO**を重ねた派生。**Pass\@32が60%超**に向上する一方、**証明の冗長化や特定タクティク（`try` など）への過適合**も観察。DPO版モデルも公開。([arXiv][1], [Hugging Face][3])

* **二系統の“形式化器（formalizer）”**
  自然文の数学問題を Lean 4 の命題に変換するモデルを**2本立て**で用意し、**1.64M件**の formal statements を作成。どちらも**Qwen-2.5-Coder-32B**を微調整した派生で、

  * **Formalizer-A**：Lean Workbook の非形式/形式ペアで学習。([arXiv][1])
  * **Formalizer-B（SonnetAnnotated）**：Claude 3.5 Sonnet による注釈ペアで学習。両者を**併用した方が性能が最良**（アブレーション）。モデルカードも公開。([arXiv][1], [Hugging Face][4])

# 研究で“使用”した主な外部モデル・要素

* **DeepSeek-Prover-V1.5-Base / -RL**
  収集初期は**V1.5-RLで各命題16サンプル**の証明候補を生成→Leanで検証→正答だけを集め、**V1.5-Base**を出発点に**8回のエキスパート反復**で Goedel-Prover を育成。([arXiv][1])
* **（補助的検討）OpenAI o1-preview**
  スケッチ→サブゴール分割→DeepSeek-RLで充足、という代替パイプラインも試したが**有効性は限定的**（miniF2F val 244題で76題のみ）。([arXiv][1])
* **評価環境**
  ベンチは \*\*miniF2F（Lean 4.9.0版）\*\*などのLean 4データを使用。**Leanコンパイラの型検査**で各候補証明を機械検証し、Pass\@Nを算出。([arXiv][1])

# どこに公開されている？

* **論文・コード・モデル・データ**はすべて公開：
  GitHub（評価スクリプト）、HF（**Goedel-Prover-SFT/DPO**, **Formalizer-32B×2**, **Goedel-Pset-v1**, **Goedel-Pset-v1-solved**, **Lean-workbook-proofs**）。([arXiv][1])

> まとめ：**7BクラスのSFTモデル（Goedel-Prover-SFT）が主役**。その上に**DPO/GRPO**を重ねた派生も作成。**Qwen-2.5-32Bベースの形式化器を2系統**用意して多様な Lean 命題を大量生成し、**DeepSeek-V1.5**を足がかりに**8反復の自己ブートストラップ**で性能を引き上げています。([arXiv][1])

もっと掘るなら、各モデルの**推奨推論設定（温度・本数）**や**サイズ別メモリ要件**もすぐ出せます。

[1]: https://arxiv.org/html/2502.07640v3 "Goedel-Prover: A Frontier Model for Open-Source Automated Theorem Proving"
[2]: https://huggingface.co/Goedel-LM/Goedel-Prover-SFT "Goedel-LM/Goedel-Prover-SFT · Hugging Face"
[3]: https://huggingface.co/Goedel-LM/Goedel-Prover-DPO "Goedel-LM/Goedel-Prover-DPO · Hugging Face"
[4]: https://huggingface.co/Goedel-LM/Goedel-Formalizer-32B-SonnetAnnotated?utm_source=chatgpt.com "Goedel-LM/Goedel-Formalizer-32B-SonnetAnnotated"




いいよ！“Goedel-Prover”の流れを**最短で全体把握**できるように、やること→作る物→使い道の順で並べます。

# ワークフロー（ざっくり7ステップ）

1. **自然文の問題を集める**
   　Numina / AoPS などの数学問題（自然言語）を入口の素材にする。目的は「Lean で学習できる形式データを大量に作る」こと。 ([arXiv][1])

2. **“形式化器”で Lean 命題に翻訳 → Goedel-Pset-v1（164万件）**
   　専用の**ステートメント形式化モデル**を学習し、自然文→Lean 4 の命題に自動変換。これで **1.64M** の formal statements から成る **Goedel-Pset-v1** を作る。翻訳の内容保持は LLM でチェック。 ([arXiv][2])

3. **（重要）Lean で“命題そのもの”を機械検証**
   　作られた Lean 命題は、Lean コンパイラ（カーネル）の型検査が通るか確認。以降も**正しさの判定は常に Lean** が担当（信頼境界）。 ([arXiv][2])

4. **エキスパート反復：証明を回収してデータを巨大化**
   　仮のプローバで各命題に**候補証明を多数生成**→Lean で検証→**通った証明だけ**を次の学習に追加——を**何周も反復**。その結果、**80万件超**の「命題＋正証明」から成る **Goedel-Pset-v1-solved** を得る。 ([arXiv][2])

5. **最終プローバ（Goedel-Prover-SFT）を“教師ありのみ”で訓練**
   　ベース（DeepSeek-Prover-V1.5-Base）に対し、上の **v1-solved** を使って**SFTだけ**で微調整。**生成は whole-proof**（生成中は Lean と非対話で、**全文の証明**を一発で出す方式）。 ([arXiv][2])

6. **評価：Pass\@k（miniF2F / PutnamBench / Lean Workbook）**
   　各問題につき N 本サンプル（例：32）を出し、**どれか1本でも Lean 検証を通れば成功**＝Pass\@N。
   　結果：**miniF2F Pass\@32 = 57.6%（先行SOTA+7.6pt）**、**PutnamBench 7題（@512）**、**Lean Workbook 2.97万題の新規証明**。必要に応じ **DPO/RL** を足すと **Pass\@32が60%超**まで伸びるが、出力が冗長化しやすい傾向も解析。 ([arXiv][2])

7. **公開：コード／モデル／データ**
   　GitHub（評価スクリプト）、Hugging Face（SFT/DPOモデル、**Goedel-Pset-v1 / v1-solved**、Lean-workbook-proofs）を**フル公開**。再現・拡張がしやすい。 ([arXiv][2])

---

## 1行で言うと

\*\*「自然文→Lean 命題（大量生成）」→「Lean で確かめながら証明を回収（反復）」→「教師ありだけで強い whole-proof プローバを完成」→「Pass\@k で評価・公開」\*\*という、データ拡張と機械検証を中心に回すワークフローです。 ([arXiv][2])

必要なら、この流れを**あなたの環境用の具体コマンド列**（形式化 → 反復収集 → 学習 → 評価）に落として書き下ろします。

[1]: https://arxiv.org/abs/2502.07640?utm_source=chatgpt.com "Goedel-Prover: A Frontier Model for Open-Source Automated Theorem Proving"
[2]: https://arxiv.org/html/2502.07640v3 "Goedel-Prover: A Frontier Model for Open-Source Automated Theorem Proving"


了解！“技術の中身”をできるだけ平易に、でも要点はしっかり押さえて説明します。

# 技術的なポイントをやさしく

## 1) まずはデータ作り（自動形式化）

* 自然文の数学問題（Numinaなど）を \*\*Lean 4 の命題（statement）**に自動翻訳する**形式化器（formalizer）\*\*を2本用意。

  * **Formalizer A**：Lean Workbook の「非形式 ↔ 形式」対で学習。
  * **Formalizer B**：**Claude 3.5 Sonnet**が作成した対訳を使って学習。
    2本を併用して**1,640,000件**の Lean 命題 **Goedel-Pset-v1** を作成。翻訳の“意味が保たれているか”は LLM でチェック（後述）。 ([arXiv][1])

* 形式化の品質管理：

  * **CCテスト**（Lean でコンパイルが通るか）と、**FCテスト**（自然文の意味が**忠実**か）を実施。
  * FCは **Qwen2.5-72B-Instruct** に4回判定させてスコア化し、閾値未満は除外。各問題につき**A/B各8本=16本**生成→CC/FCを通った候補のみ残す運用。 ([arXiv][1])

## 2) 証明データを“Leanで確かめて”増やす（エキスパート反復）

* 初回は先行SOTA **DeepSeek-Prover-V1.5-RL**で**各命題あたり16候補**の**全文証明**を生成→**Lean コンパイラで検証**→**正答だけ**を集めて学習し直す。
* 以降は自前の新モデルでさらに未解決を解いては学習…を**計8反復**。
  その結果、命題1.64Mに対し**約0.93M**の「命題＋正しい証明」まで拡大（表：iter-9で **928k** solved）。 ([arXiv][1])

## 3) 生成の流儀：**whole-proof（全文一発生成）**

* 生成中は **Lean と対話せず**、最初から最後まで**完成した証明**を出力（タクティク逐次探索はしない）。正しさの判定は**最後に Lean で検証**して行う、という設計です。 ([arXiv][1])

## 4) 学習レシピ：SFTが主役、RLは上乗せ検討

* ベースは **DeepSeek-Prover-V1.5-Base**。収集した「命題＋証明」だけで\*\*教師あり微調整（SFT）\*\*した **Goedel-Prover-SFT** が主役。
* さらに \*\*DPO / GRPO（RL）\*\*を上乗せすると **Pass\@32 が約+3pt**伸びる一方、

  * 証明が**冗長化**（平均長が大幅増）、
  * **特定のタクティク（例：`try`）の濫用**が増え、
  * **試行回数を増やしたときの伸び（Pass\@3200など）が鈍る**＝出力多様性の低下が示唆、という挙動も解析。 ([arXiv][1])

## 5) 評価と結果（Leanで機械検証→Pass\@k）

* **miniF2F（Lean4, whole-proof）**：**Pass\@32 = 57.6%**（先行の DeepSeek-V1.5-RL を **+7.6pt**上回る）。**Pass\@3200 = 62.7%**、\*\*Pass\@25600 = 64.7%\*\*でも優位。 ([arXiv][1])
* **PutnamBench**：\*\*7題（Pass\@512）\*\*でリーダーボード首位（同率含む）。注記：誤形式化の1題は除外。 ([arXiv][1])
* **Lean Workbook**：**29.7K題**の新規正式証明を公開。 ([arXiv][1])
* 評価の実行方法（公開スクリプト）：`-n` が Pass 本数、`-c` が Lean 検証の並列度。例：`eval.sh ... -n 32 -g 2 -c 128`。 ([GitHub][2])

## 6) データ分布の注意点（どこで強い／弱い？）

* **ProofNet / Mathlib4** と **miniF2F / Lean-Workbook / NuminaTest**の間に**分布差**あり。Mathlib4を入れると**ProofNetは上がるが miniF2F は下がる**など、評価集合により傾向が変わることを解析。 ([arXiv][1])

---

## まとめ（技術の芯）

* **2本の形式化器で多様に命題を量産**→**CC/FCで意味も機械チェック**→**Lean検証で正答だけを回収**して**SFTを反復**、という\*\*「データ拡張×機械検証のループ」\*\*が核。
* 生成は**whole-proof**でシンプル・高速、**判定はLeanカーネル**で厳密。**SFTだけでもSOTA**、RLは一長一短。 ([arXiv][1])

必要なら、あなたの環境向けに

* 形式化→反復収集→学習→評価までの**実行コマンド表**、
* **CC/FC実装の最小プロンプト例**、
* **Lean検証（`sorry`/公理検査）チェックリスト**
  もそのまま使える形で用意します。

[1]: https://arxiv.org/html/2502.07640v3 "Goedel-Prover: A Frontier Model for Open-Source Automated Theorem Proving"
[2]: https://github.com/Goedel-LM/Goedel-Prover "GitHub - Goedel-LM/Goedel-Prover"
