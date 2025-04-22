# Autoformal: 非形式的証明の自動形式化パイプライン

このリポジトリは、自然言語＋数式の非形式的証明をLean4形式証明へ自動変換するパイプラインです。

## 構成
- `data/`: アノテーション済みデータと前処理ツール
- `prompts/`: LLMプロンプトテンプレート
- `src/`: パイプライン実装モジュール
- `lean/`: Lean4プロジェクト
- `results/`: 実験ログ・可視化結果

## セットアップ
```bash
git clone <repo_url>
cd autoformal
python3 -m venv venv
source venv/bin/activate
pip install -r requirements.txt
leanproject get-mathlib

## 仮想環境アクティブ
venv\Scripts\activate
