# p-vs-np-lab

[![Research checks](https://github.com/HeliCorgi/p-vs-np-lab/actions/workflows/ci.yml/badge.svg)](https://github.com/HeliCorgi/p-vs-np-lab/actions/workflows/ci.yml)

P versus NPに関連する、再現可能な定理・反例・計算実験の研究室。
最初のテーマは **境界関係の圧縮・合成・存在消去**。

**P vs NPの解決は主張していません。** 初期成果は、特定の表現形式がどこで破綻し、どの限定された制約クラスなら正確に扱えるかを確認するものです。2026年11月4日（日本時間）の確認時点で、[Clay Mathematics Institute](https://www.claymath.org/millennium/p-vs-np/)もこの問題を未解決として掲載しています。

## 今回わかったこと

「小さい部品の境界関係が短く書けるなら、それを繰り返し合成して一般SATを解けないか」を出発点にしました。内部変数を消去した後の表現サイズが最初の障害です。

| 対象 | 確認した結果 | 証拠と範囲 |
|---|---|---|
| 5色・5端子の星グラフ | 中心を消去すると、境界の等式・不等式だけからなるCNFには10種類すべての等式を含む節が必須 | Lean。補助変数なし・このリテラル語彙に限定 |
| XOR鎖のCNF | n=12では45節・幅3から、境界だけのCNFは最小2,048節・幅12へ | 既知の全nの証明を記述し、n=3..12で有限検証 |
| 同じ偶数パリティ関係 | n=12ではOBDDの内部ノード23個、XORでは方程式1本 | 表現依存性を確認する対照 |
| GF(2)方程式の合成・射影 | n=4,8,16,32,64,128,256のXOR鎖を境界の方程式1本へ消去 | 正確なGaussian消去。小入力は独立全探索とも照合 |
| 既存HNの保存された境界12状態 | 13個の共通不等式に加える二項OR節は最小4、一意 | 全855状態で再現。保存SAT葉は前提 |

星グラフの結果は、5色固定では **幅10未満、特に幅2で閉じるという期待** を否定します。あらゆる固定幅や、あらゆる表現形式を否定したわけではありません。一般q色・q端子では必要幅は `q*(q-1)/2` ですが、その族では色数も増えています。

## 1. Leanで確認する小さな定理

5個の境界端子の色を `a0,...,a4`、隠れた中心の色を `x` とすると、

\[
\exists x\in\{0,1,2,3,4\}\;\bigwedge_{i=0}^{4} x\ne a_i
\quad\Longleftrightarrow\quad
\bigvee_{0\le i<j<5} a_i=a_j.
\]

中心に使える色が残るのは、境界のどこかに同色対がある場合です。右辺には10個の等式があります。これを短い節の集まりに置き換えようとしても、全端子が異色の割当を拒否する節には、10種類すべての等式が必要になります。各対だけを同色にした許容割当が、それぞれの等式を必須にします。

[`Formal/StarProjection.lean`](Formal/StarProjection.lean) は、境界の有限判定に加えて、**任意個数・任意長の節からなるCNF**についてこの必要性を証明します。主定理は `every_exact_CNF_has_all_equalities_clause` です。有限サイズのCNF候補だけを列挙した主張ではありません。

[`Formal/BoundaryComposition.lean`](Formal/BoundaryComposition.lean) は、内部が独立に分離された二つの部品について、存在量化した境界関係が論理積で合成できることを証明します。内部間に新しい辺がある分解へ適用する場合は、その前提を別途確認する必要があります。

Lean 4.19.0とStdのみを使用します。主要8定理の実際の推移的な公理依存を [`scripts/audit_axioms.py`](scripts/audit_axioms.py) で取得し、標準の `propext`、`Classical.choice`、`Quot.sound` 以外を拒否します。通常のカーネル判定を用い、証明穴やネイティブ評価への信頼で有限命題を埋めません。

## 2. 指数サイズになる表現と、小さく扱える表現

パリティは、表現形式の限界と計算困難性を混同しないための対照です。

| 境界変数n | 内部変数を持つ元のCNF節数 | 境界のみのCNFの最小節数 | OBDD内部ノード | ネイティブXOR方程式 |
|---:|---:|---:|---:|---:|
| 4 | 13 | 8 | 7 | 1 |
| 8 | 29 | 128 | 15 | 1 |
| 12 | 45 | 2,048 | 23 | 1 |

元の節数は、各XORゲートを4節で表し、最終出力を0にする単位節を1つ加えた、簡約前の数です。境界だけの通常CNFの下界 `2^(n-1)` は既知であり、新規結果とはしません。詳しい一般証明・出典・全列挙の範囲は [parityの記録](docs/parity_projection.md) を参照してください。

GF(2)実装では、連立一次方程式を共有変数で結合し、隠れ変数を先に消去します。256境界変数でも残る制約は `x1 XOR ... XOR x256 = 0` の1本です。この大きさでは真理値表を全列挙せず、正確な行消去の結果を検査しています。中間行は密になり得ます。長整数演算のビット費用も無視しません。

これは一般SAT解法への拡張を意味しません。例えば `x OR y` の許容割当は3個ですが、非空のaffine解集合の大きさは2の冪です。線形な補助変数を足して存在消去するだけでは、このOR関係を表現できません。[GF(2)の記録](docs/affine_projection.md)に、アルゴリズムと適用範囲を書きました。

## 再現

リポジトリルートで実行します。実験はPython 3.10以上、標準ライブラリのみです。CIはPython 3.12を使用します。

```bash
python scripts/reproduce.py --out-dir reproduced --check
```

この1コマンドで次を実行します。

- 22件の意味論テスト。GF(2)射影120系・結合80組の固定seed比較、共有変数や色名を誤って消す負例を含みます。
- 星グラフ4ケース、パリティ10ケース、GF(2)7ケース。
- 旧実験28ファイルのハッシュ確認と再実行。上流11ファイルはさらに上流manifestで照合します。
- 新しい決定的なJSONと、コミット済み `results/*.json` の一致確認。
- 旧結果5ファイルの数学的内容の一致確認。時刻・Python環境・計測時間だけは比較対象から除き、状態数・式・証人・判定結果を比較します。

Leanは別の明示的な検証です。

```bash
lake build Formal
python scripts/audit_axioms.py
```

CIはPythonとLeanを別jobで実行します。Pythonの成功だけを形式証明の成功と扱いません。結果を意図的に更新する場合は `python scripts/reproduce.py --out-dir results` で生成し、変更理由と差分を確認してください。

## ファイル案内

| 場所 | 内容 |
|---|---|
| [`docs/research_notes.md`](docs/research_notes.md) | 結論、主張の種類、未達成事項、次に測るもの |
| [`docs/projection_barrier.md`](docs/projection_barrier.md) | 星グラフの一般qの証明と厳密な範囲 |
| [`docs/parity_projection.md`](docs/parity_projection.md) | 既知のCNF指数下界と有限検証 |
| [`docs/affine_projection.md`](docs/affine_projection.md) | 効率的な射影が閉じるGF(2)の対照 |
| [`src/pnp_lab/relations.py`](src/pnp_lab/relations.py) | ラベル付き有限関係の結合・射影・色対称性検査 |
| [`src/pnp_lab/affine.py`](src/pnp_lab/affine.py) | GF(2)関係の結合・射影 |
| [`results/RUN_SUMMARY.json`](results/RUN_SUMMARY.json) | 実験集計と実行コードのSHA-256 |
| [`experiments/baseline/README.md`](experiments/baseline/README.md) | 旧実験の保存記録。中の単独コマンドはこのディレクトリから実行 |

## 引き継いだもの

`hadwiger-nelson-lab` の上流コミット `c38a11a0b724856eec035483c8d391f08bc29ca8` から取得した保存データとチェッカーを、[manifest](experiments/baseline/upstream/SOURCE_MANIFEST.json)・ライセンス付きで固定しています。旧実験は境界圧縮、35,000割当の部品合成、12ケースのSAT固定点対照です。

HNの幾何や元のSAT葉を独立に再証明したものではありません。SAT固定点の長い反復も、特定の更新則の費用を示すもので、SAT全般の下界ではありません。詳細と着想元は旧READMEに残しています。

今後の焦点は、表現の長さだけでなく、**その表現を作る費用・合成と射影で閉じる範囲・最終判定の費用**を一緒に追うことです。
