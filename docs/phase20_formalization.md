# 第20段階のCNF族の存在と指数下界のLean検証

2026年11月8日（日本時間）。[簡易査読](phase20_review.md)から続けた形式化。

**元の変数上のアフィン節DAGに対する、第20段階の存在と指数下界をLeanで接続した。**
残っていたCNF族の存在と数値評価を証明し、分離条件・密度条件・族の存在を
外部仮定にしない終端定理を追加した。ローカルで全体ビルドと**390定理の公理監査**が成功した。
これは指定された証明系の下界であり、P vs NPの解決でも、数学的新規性の主張でもない。

## 最終定理

[`Phase20.exists_unsat_exponential_lower_bound`](../formal_pc/ProofLab/Phase20.lean) は、

\[
 n\ge n_0=16\cdot1024\cdot12288^4\cdot10^{16}
 =3735465674926184202240000000000000000
\]

を満たす**全ての整数 \(n\)** について、次のCNFの存在を証明する。

- 元のBoolean変数は \(n\) 個、節数は正確に \(12n\)。未使用の変数も許す。
- 各節は相異なる3変数を持ち、異なる2節の支持の共通部分は高々1変数。
- 各変数の出現回数は高々4096。
- \(s=\lfloor n/10^{16}\rfloor\) とし、\(0<|A|\le s\) なら \(|A|<2|\partial A|\)。
- その支持構造にUNSATな符号付けが存在する。

そのCNFと明示的なBoolean公理から、元の変数の \(\mathbb F_2\) 上のアフィン形式の
選言を行とする、正しいソースDAGによって空節を導くとする。
入力行の幅は3以下、各推論の親は先行する1行または2行であり、意味論的に正しい。
先行行の再利用、深さ、導出行の幅やアフィン形式の変数範囲は制限しない。
通常の生の3-CNF入力はこの入力幅の条件を満たす。

\(R=\lfloor s/16\rfloor\)、行数を \(S\)、階数が \(R\) より大きい行の
**相異なる非空の反例集合**の個数を \(H_R\) とすると、同じ定理が

\[
 \boxed{\quad H_R\ge\frac14\exp\!\left(\frac{n}{81\cdot2^{65}\cdot10^{32}}\right),
 \qquad S\ge\frac14\exp\!\left(\frac{n}{81\cdot2^{65}\cdot10^{32}}\right)\quad}
\]

を導く。空の反例集合は数えず、集合として等しい反例空間は重複除去する。
CNF族の存在、普通のPCに対する分離、良い単項式の密度、床関数の条件、
二項係数の比較は、この終端定理の仮定に残っていない。

## CNF族の存在を閉じた方法

[`CNFFamilyExistence.exists_unsatisfiable_family`](../formal_pc/ProofLab/CNFFamilyExistence.lean)
は、族の存在自体については \(n\ge10^6\) で証明する。
証明は有限集合上の実際のBernoulli積重みを使う。
各相異なる三つ組を確率 \(\rho=96/n^2\) で選んだ集合を \(H\)、
その変数次数を \(d_v\)、2変数以上を共有する相異なる三つ組の**順序付き**ペア数を \(P(H)\) とする。

1. **展開性の失敗確率。** \(3\le t\le s\)、\(r=\lfloor7t/4\rfloor\) として、
   \(t\) 節の近傍が \(r\) 変数以下に入る事象を、実際の包含証人で覆う。
   その確率は
   \[
    \binom nr\binom{\binom r3}{t}(96/n^2)^t\le(1/2)^t.
   \]
   \(\binom ab\le(3a/b)^b\) と4乗の比較で証明し、
   有限の幾何級数を足して全失敗確率を \(1/4\) 以下とする。
2. **節数。** \(\mathbb E|H|\ge31n/2\)。指数モーメントに
   \(\theta=-1/64\) を適用して、\(\Pr[|H|<15n]\le e^{-n/256}\le1/16\) を導く。
3. **出現回数と重複。** 各 \(v\) の平均次数は48以下で、
   \(\mathbb E\sum_v d_v^2\le2352n\)。実際の衝突ペアを数えて
   \(\mathbb E P(H)\le4608\) も証明する。
4. **同時成立。** 非負の量
   \[
    {\bf1}_{\text{展開性失敗}}+{\bf1}_{|H|<15n}
      +\frac{\sum_v d_v^2}{8192n}+\frac{P(H)}n
   \]
   の期待値は \(1/4+1/16+2352/8192+1/16=339/512<1\)。
   従って、これが1未満になる標本が存在する。条件ごとの別々の存在から
   同時成立を推測していない。
5. **削除と保持。** 次数が4096を超える変数に触れる節を全て削除する。
   削除数は \(\sum_v d_v^2/4096\le2n\)。次に衝突ペアの端点となる節を全て削除する。
   順序付きペアの第1成分への射影で数えるため、削除数は \(P(H)\le n\)。
   少なくとも \(15n-2n-n=12n\) 節が残り、そこから正確に \(12n\) 節を取る。
   近傍の展開性は削除で保存される。
6. **境界への変換。** 接続関係を数え、
   \(2|N(A)|\le3|A|+|\partial A|\) を証明する。
   \(7|A|<4|N(A)|\) から半境界展開性が従う。
   \(|A|=1,2\) は3変数性と線形性から別に処理する。
7. **UNSAT符号付け。** 各節の局所符号は8通り、固定した割当を満たすものは7通り。
   全ての割当で被覆できる符号付け数は \(2^n7^{12n}<8^{12n}\)。
   被覆外の符号付けを選ぶ。全て正の符号を持つSATな兄弟も、同じ支持上に存在する。

紙上の「高確率で成立し、十分大きければ正の確率で交わる」という部分を、
上記の有限の不等式と明示的な閾値で置き換えた。
族は存在的な構成であり、実用的な時間で生成する算法の主張はしていない。

## 最後の数値評価

[`ExponentialBudget.lean`](../formal_pc/ProofLab/ExponentialBudget.lean) で、
良い単項式を選ぶ確率 \(p=1/(1024\cdot12288^4\cdot10^{16})\) を使う。
これは支持構造の標本確率 \(\rho\) とは別の定数である。
\(n\ge n_0\) から \(pn\ge16\) を導く。
既存の密度定理が選ぶ \(pn/2\le k\le2pn\) に対して、
\(R\ge3\)、\(4(k+3R)\le s\)、\(N=n-R-1\ge k\)、\(3k\le N+1\) を全て証明する。

隣接する二項係数の正確な恒等式と帰納法により、

\[
 b_k(N)\le2\binom Nk,
 \qquad \exp\!\left(\frac{(R+1)k}{n}\right)\binom Nk\le\binom nk
\]

を証明した。\(\binom Nk>0\) も内部で確認してから約分する。
密度の損失 \(a=168n(12288^2)^4p^3\) を含めた指数を、床関数と正確な有理数計算で

\[
 \frac{n}{81\cdot2^{65}\cdot10^{32}}
 \le\frac{(R+1)k}{n}-a
\]

と評価し、既存の次元予算から最終下界を導く。
浮動小数点の実験値や未証明の漸近比較は使っていない。

## 実装の接続

| モジュール | 検証した役割 |
|---|---|
| `DistinctAffineFlats`、`BooleanFunctionSpace`、`IntrinsicAffineRestriction` | 実際の反例集合の重複除去、Boolean関数の次元予算、内在的な座標と階数 |
| `ExpanderSupport`、`ExpanderLocalConsistency`、`ExpanderMonomials` | 支持集合、局所充足性、具体的な良い単項式空間と正確な次元 |
| `IdealNormalForm`、`BooleanIdealNormalForm`、`NormalFormRestriction`、`ExpanderNormalForm`、`ExpanderReduction` | 実際の正規形と還元作用素、反復変数を含む乗算整合性、通常のPCに対する分離 |
| `FiniteBernoulli`、`BernoulliBounds`、`ConnectedSetCounting`、`ExpanderObstructions`、`LinearClauseBoundary`、`BoundaryProbabilitySum`、`ExpanderDensity` | 連結障害の計数、正の相関、二項分布の尾、良い集合の密度 |
| `ExpanderDAGLowerBound`、`ExpanderDensityDAG` | 分離と密度を証明して、実際のソースDAGの個数予算へ接続 |
| [BernoulliCounting](../formal_pc/ProofLab/BernoulliCounting.lean)、[TripleCounting](../formal_pc/ProofLab/TripleCounting.lean) | 有限の期待値・モーメント・合併の上界、三つ組と衝突の正確な標本空間 |
| [RandomCNFEstimates](../formal_pc/ProofLab/RandomCNFEstimates.lean)、[RandomCNFExpansion](../formal_pc/ProofLab/RandomCNFExpansion.lean)、[RandomCNFMoments](../formal_pc/ProofLab/RandomCNFMoments.lean)、[RandomCNFSample](../formal_pc/ProofLab/RandomCNFSample.lean) | 展開性・節数・次数・衝突の評価と同時成立 |
| [TriplePruning](../formal_pc/ProofLab/TriplePruning.lean)、[NeighborhoodBoundary](../formal_pc/ProofLab/NeighborhoodBoundary.lean)、[CNFSigning](../formal_pc/ProofLab/CNFSigning.lean)、[CNFFamilyExistence](../formal_pc/ProofLab/CNFFamilyExistence.lean) | 削除、境界展開性、正確な節数、SAT/UNSAT符号付け、族の存在 |
| [ExponentialBudget](../formal_pc/ProofLab/ExponentialBudget.lean)、[Phase20](../formal_pc/ProofLab/Phase20.lean) | 整数の丸め、二項係数、明示的な指数、存在と下界をまとめた終端定理 |

## 検証記録と範囲

```bash
cd formal_pc
lake build ProofLab
python3 audit.py
```

Lean `4.34.0-rc2` と固定済みMathlibを使い、全体ビルドが成功した。
今回の新規70定理を含む390定理の実際の依存公理は、
`propext`、`Classical.choice`、`Quot.sound` の範囲に収まった。
未証明の補題、`sorryAx`、独自の数学的公理を追加していない。
[今回の記録](../results/phase20_complete_formal_audit.json)に各定理の公理集合とソースハッシュを保存する。

既存のPython 430テストと、総括を含む68件の決定的なレポートの再現照合も成功した。
総括の古い未完了表記を今回のLean記録への参照に更新し、ソースハッシュを更新した。
このPython検査は有限の実装検査であり、上のLeanビルド・公理監査とは別の検査である。

[320定理の密度段階](../results/phase20_density_formal_audit.json)、
[245定理の分離段階](../results/phase20_separator_formal_audit.json)、
[181定理の支持・次元段階](../results/phase20_formal_progress_audit.json)の記録は、
当時の未完了範囲とハッシュを持つ履歴として保持する。

今回完了したのは、上記の \(\mathbb F_2\) の証明系と具体的なCNF族についての指数下界である。
他の体や多親ルールへの紙上の一般化、外部専門家の査読、新規性・優先権の判定、
一般の計算模型への接続は、この完了の主張に含めない。
ローカルの検証であり、新たなGitHub CI実行や、キャッシュされたMathlib全体の
独立なカーネル再検証を意味しない。
