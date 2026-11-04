# p-vs-np-lab

[![Research checks](https://github.com/HeliCorgi/p-vs-np-lab/actions/workflows/ci.yml/badge.svg)](https://github.com/HeliCorgi/p-vs-np-lab/actions/workflows/ci.yml)

P versus NPに関連する、再現可能な定理・反例・計算実験の研究室。
最初のテーマは **境界関係の圧縮・合成・存在消去**。

**P vs NPの解決は主張していません。** 初期成果は、特定の表現形式がどこで破綻し、どの限定された制約クラスなら正確に扱えるかを確認するものです。2026年11月4日（日本時間）の確認時点で、[Clay Mathematics Institute](https://www.claymath.org/millennium/p-vs-np/)もこの問題を未解決として掲載しています。

## 第14段階：Boolean節から3を法とする保存則を発見する

前回の標的だった「元の変数名も、流れを表すグラフも知らずに、保存則を復元できるか」を検査しました。[局所表からの合同式の発見](docs/modular_hull.md)は、入力の節が許すBoolean割当から方程式を導き、重み付き和が矛盾するか調べます。3値の各変数がちょうど一つの状態を選び、局所関係がすべてアフィンであることを確認できた場合には、[真偽の判定と元の充足割当の構成](docs/trit_solver.md)まで行います。未知の入力で保存則が見つからなければ `UNKNOWN` です。

| 何を確かめたか | 結果 |
|---|---|
| [法3のフロー](docs/ternary_flow.md) | 符号・変数名・節順を入れ替えた1,152変数・6,144節で、総電荷が整合する側は割当を構成し全節を確認。不整合な側は元の節から独立に検算できる反証を出力 |
| [異なる法の間で必要な情報を渡す](docs/mixed_modular.md) | 片方が3ビットの和に奇数を要求し、他方がちょうど2を要求する場合、それぞれ単独では未決着。共通のBoolean割当について証明した関係を渡すと反証できる。2,040節の例では実際に双方向の変換を使用 |
| [法を入力で指定しない](docs/prime_spectrum.md) | 局所表の階数を整数の小行列式から調べ、例から2・3・5を検出。[整数の不変因子](docs/local_torsion.md)では、巡回する4状態と独立な二つの偶奇を区別できる。いずれも局所診断で、空の結果はSATを意味しない |
| [素数体では見えない場合](docs/four_flow.md) | 総電荷が2の4状態フローには、局所的にどの体で導いた一次式もすべて満たす一つのBoolean割当がある。一方、[法4の環として計算](docs/cyclic_four.md)すると、480変数・3,840節の例を64項の `0=2 (mod 4)` で反証できる。[有限アーベル群での境界](docs/abelian_visibility.md)も記録 |
| [保存則を隠す／保存則自体がない](docs/modular_barrier.md) | [3,840個の補助変数の消去](docs/modular_padding.md)で保存則を復元した例がある。別に、元の節または変数を `n/1000` 個まで集めても、どの体でも非自明な一次・二次の等式を得られない解あり・解なしの入力対が存在。この強い範囲は存在証明で、SAT一般の計算時間下界ではない |

```bash
python scripts/solve_conservation.py examples/phase14_ternary_sat.json | python scripts/solve_conservation.py examples/phase14_ternary_sat.json --check -
python scripts/solve_conservation.py examples/phase14_mixed.json --method mixed | python scripts/solve_conservation.py examples/phase14_mixed.json --check -
python scripts/solve_conservation.py examples/phase14_four_bad.json | python scripts/solve_conservation.py examples/phase14_four_bad.json --check -
```

統合判定器でも `--conservation` を指定可能。既定の分岐法は以前のままです。[Leanで追加した5定理](Formal/ModularHull.lean)は局所的な含意、重み付き和、法3・法4の矛盾とBoolean上の法をまたぐ含意の健全性に関するものです。アルゴリズム全体や確率的な下界をLeanで検証したものではありません。

## 第13段階：複数の節で枝を移す。その証明はどこまで短いか

前回は、変換先の各節を「元の一節」から保証する規則でした。今回は、変換先の節を偽と仮定して元の節から値を順に強制し、矛盾するまでの節番号を記録します。[独立チェッカー](docs/derived_transport.md)はその推論を再生し、枝Aの解を枝Bの解に移せると確認できたときだけAを削ります。探索の失敗や予算切れでAを捨てることはありません。

| 検証した問い | 結果 |
|---|---|
| 前回の指数個の枝を、本当に新規則で統合できるか | [二項節で等しくなる変数の対応](docs/interface_transport.md)を使うと、前回の反例族では各タグ分岐後に残す代表が1個で足りる。補助変数を足した版にも成立。8回のタグ分岐では8回の移送を実行した。その先の一般部分まで幅1になるとは限らない |
| 以前の前処理が何も見つけられなかった符号化はどうか | [六変数の局所証明と等値関係の復元](docs/blind_recovery.md)により、変数名・符号・節順を変えた12,932変数・18,113節を899変数・2,568節に縮約。解なし側で反証、解あり側で元入力の全節を満たす割当を確認。任意の3-SATから作れる別の表現には、この復元法が何もしない |
| 十分短い解消証明さえ探せば、枝数を一般に抑えられるか | [両方向の証明長下界](docs/robust_ceiling.md)と[各タグ層への拡張](docs/layered_resolution_barrier.md)。選んだ変数順で深さ `d` の `2^d` 個の残余式のどの二つでも、符号付き変数・定数によるどの写像にも、通常の解消規則だけで保証するには指数長の証明が必要な族がある。これは全SAT算法の下界ではない |
| 同じ種類の入力を別の方法で解けるか | [一つの変数の両ケースにパリティ検査を適用](docs/case_parity.md)。8モジュールの実験（888変数・1,280節）で両方に矛盾があり、全入力の充足不能を独立に検算できた |

関連資料：[幅制限を以前の符号化へ移す証明](docs/width_transfer.md)、[単一の分岐層に多数のグラフを埋め込む構成](docs/port_antichain.md)、[小さなグラフでの独立検査](results/rigid_ceiling.json)。[今回追加したLeanの5定理](Formal/DerivedTransport.lean)が扱うのは、単位伝播・二分岐による矛盾・導出した節による証人移送の健全性です。指数下界やPython実装全体を形式検証したものではありません。

```bash
python scripts/solve_pruned.py examples/phase13_hidden_odd.json --recover-parity | python scripts/check_pruning_parity.py examples/phase13_hidden_odd.json -
python scripts/solve_pruned.py examples/phase13_transport_cut.json --derived-depth 0 --label syntax --max-width 1 --max-transport-checks 2
```

2番目は2個のタグを幅1で通過し、その先では比較予算が尽きて `UNKNOWN` になります。[次の研究対象](docs/reverse_engineering.md)は、節の証明を長くすることより、複数の枝に共通する代数的な矛盾を元の節から発見・検算することです。

## 第12段階：枝の解を移す。一方向の証明で足りるか

枝Aの解を枝Bの解に必ず変換できれば、Bを残してAを削れます。BからAへ戻せる必要はありません。[発見器と独立チェッカー](docs/transport_discovery.md)は、Bの各変数をAの符号付き変数または定数で置き換え、Bの各節が恒真になるか、Aの一つの節で保証されるかを元の節で調べます。探索が失敗しても枝は捨てません。[Leanで追加した6定理](Formal/WitnessTransport.lean)は、実際に割当を移すこと、証明書の合成、正しい向きの枝削除を扱います。

| 何を試したか | 結果と限界 |
|---|---|
| [前回の解あり・解なしの対照例](docs/transport_positive.md) | 以前は幅上限15で両方 `UNKNOWN`。同じ上限で、移送を加えると両方正答。別の族では6回のタグ分岐がすべて幅1。残りの一般部分まで幅1で解けるとは限らない |
| [変換の完全探索](docs/transport_discovery.md) | 提案済みの証明書は多項式時間で検査可能。一方、兄弟枝間で有効な符号反転が存在するかの完全判定だけでもNP完全。一般多項式時間の発見器は得られていない |
| [証明書自体が存在しない族](docs/transport_obstruction.md) | 指定のタグを先に分岐すると、深さ `d` にある `2^d` 個の生の残余式はどの二つも、この直接の移送証明書では統合できない。タグの全列挙ではなく全サイズの証明 |
| [枝を作らず根で反証](docs/split_parity.md) | 二通りのタグ値それぞれで導ける共通のXOR式を集める。2,204変数・5,178節の実入力から、1,691項の検算可能な矛盾を得た。偶数パリティの充足可能な対照例は反証しない |
| [補助変数でパリティを隠した場合](docs/transport_padding.md) | [短い解消節を加える](docs/private_resolution.md)と、1,526変数・2,292節の例も分岐前に反証。一方、この根の前処理が解消節もXOR式も一つも生成できないNP完全な入力クラスがある |

```bash
python scripts/solve_pruned.py examples/transport_shielded_unsat.json --label blocked --transport --max-width 15
python scripts/solve_pruned.py examples/transport_switch_k2.json --split-parity | python scripts/check_pruning_parity.py examples/transport_switch_k2.json -
```

第2のコマンドは、元の節と出力された証明だけで充足不能を再検査します。[解決条件から逆算した次の課題](docs/reverse_engineering.md)は、枝間の直接の代入だけに依存せず、複数の枝で共有できる短い帰結をどう発見するかです。

## 第11段階：方針転換 — 全入力で探索の幅を抑えられるか

前回の「少数のパリティ条件を組にして調べる」方針を主軸から外しました。充足可能な入力と充足不能な入力を一組作ると、独立条件が `k` 本あるのに、**どんな階数 `k−1` 以下の線形観測を選んでも両者の可否が一致**します。違いは、全員に別々の資源を割り当てられるかにあります。[反例と証人](docs/parity_shadow.md)は、元の条項を読む他の解法を排除しません。

新しい主軸は[一般3-SATの探索枝の剪定](docs/decision_pruning.md)です。各枝の解集合を保存せず、「このリストのどこかに解がある」という事実だけを保って枝を減らします。一つの基準枝との論理和につけるラベルが安全に比較でき、基準枝に解があるときの種類数が全入力で多項式に抑えられれば、一般3-SATを多項式時間で決定できます。Mahaneyの定理の証明で使われる枝刈りを出発点にした条件であり、**そのようなラベルはまだ見つかっていません**。

| 調べた候補 | 得られた結果 |
|---|---|
| 正確な解数を区別する | [短い比較器](docs/pruning_obstructions.md)で、一つの充足可能な基準枝に対して `2^k−1` 種類が必要。固定した剰余だけでは解0個と正の個数を区別できない |
| 線形条件だけに現れる変数を忘れる | [同じ解を持つ二つの連結な入力](docs/codec_controls.md)を構成。一方ではタグをすべて分岐しても幅1。もう一方では深さ `d` で厳密に `2^d` 枝が残る |
| 解の有無を保つ blocked-clause elimination も使う | [強化した算法](docs/blocked_pruning.md)では前項の補助節を除け、6タグの64ラベルが1種類にまとまる。一方、等値を3本の含意で表す別の連結な族では、解あり・解なしのどちらでも、指定の順序で同じ実装の幅が `2^k` になる |

幅の上限は実験予算です。上限を超えただけで枝を捨てることはなく、決着していなければ `UNKNOWN` を返します。予算を外せば正しく判定しますが、全入力に対する多項式時間上界はありません。

```bash
python scripts/solve_pruned.py examples/overlap_cube_unsat.json --label blocked --unbounded
python scripts/reproduce.py --out-dir reproduced --check
```

[Leanの5定理](Formal/DecisionPruning.lean)では、忠実なラベルと明示的な種類数の仮定のもとで、枝刈り・分割・その反復が解の有無を保存することを扱います。実際のPythonラベルの種類数や時間上界を形式検証したものではありません。

## 第9–10段階：禁止条件の重なりを使い、前回の未決着例を解く

3変数の全8通りの割当を1節ずつ禁止した式は明らかにUNSATです。前回の「穴の個数を足す」判定は、この式を疎なXOR選択問題に変換すると `UNKNOWN` でした。今回の[消去法](docs/event_projection.md)は**同じ変換像**に対し、禁止集合を交差させて1ビットずつ消し、36組の交差検査でUNSATを確定します。1節を外した例では28組を調べ、唯一の解を元の変数に戻して検査します。ここで数えたのは交差検査で、総演算回数ではありません。

| 手法 | 得られた結果 | 一般化の限界 |
|---|---|---|
| [各節を小さく変換](docs/selector_overlap.md) | 補助1ビット・禁止条件2個で充足可能性を保存。3個にすれば元の解と一対一に対応 | いずれも一般3SATを表す。条件数の最小性は文書の局所変換モデル内での主張 |
| [多項式の恒等式による反証](docs/overlap_refutation.md) | 同じ8節の例で、旧セレクタ座標は最小次数4（54項の証明）、小さい変換では最小次数3（24項の証明） | 両変換とも、入力の大きさとともに必要次数が線形に増える充足不能例が存在 |
| [交差をまとめる厳密計数](docs/overlap_lattice.md) | 64次元空間で64本の座標軸を避ける点の数 `2^64−65` を、最大66項で計算 | 連結なパスの入力族では、処理順によらずこの符号付き展開の項数は指数的 |
| [2-SATと線形条件](docs/observation_2sat.md) | 観測ビット間の独立な整合条件が固定本数なら、決定的多項式時間で解を復元 | [先行研究と難しい入力族](docs/observation_limits.md)。一般入力で条件の本数は定数に収まらない |

[元の8節](examples/overlap_cube_unsat.json)を使って、古い変換像をそのまま解く場合、短い反証を出す場合、解がいくつあるか数える場合を試せます。

```bash
python scripts/solve_three_cnf.py examples/overlap_cube_unsat.json --encoding sparse --method project
python scripts/solve_overlap.py examples/overlap_cube_unsat.json --encoding compact --method refute --degree 3
python scripts/solve_overlap.py examples/overlap_cube_unsat.json --encoding parsimonious --method count --slice-source
```

[Leanで追加した6定理](Formal/AffineCover.lean)は、ビット消去の同値、二つの節変換の恒等式と代入、重み付き恒等式から全割当の被覆が従うことを扱います。次数下界・実行時間・Python実装全体を形式検証したものではありません。[証明書を含む実験記録](results/selector_overlap.json)と[次の研究課題](docs/reverse_engineering.md)を収録しました。

## 第7–8段階：グラフに直せる範囲と、表を列挙しない合成

3候補のXOR選択を、入力全体で同じ線形座標変換と、グループごとのXOR平行移動で重み1に変換できれば、完全マッチングで解けます。[必要十分条件](docs/graphic_gauge.md)は、候補対の全差分がグラフの辺の依存関係を表すこと（グラフィック・マトロイド）です。[Pythonの認識器](src/pnp_lab/graphic_support.py)は木の候補を予算内で探索し、見つけた木は元の全差分で検査します。[任意のCMRバックエンド](src/pnp_lab/cmr_graphic.py)も用意し、[固定版CI](results/cmr_integration_audit.json)で実バイナリの5ケースを確認しました。非グラフィックという結果だけではSAT/UNSATは決まりません。

**この座標変換だけでは全入力を覆えません。** [小さな反例の検査可能な証明書](examples/graphic_fano_minor.json)に加え、[任意の二進行列の列依存関係をマイナーとして埋め込む構成](docs/binary_minor_universality.md)を実装しました。アフィンな候補群をすべて消した後でも成立します。元の式は各節に異なる3変数があり、各変数の出現は2～3回で、全真が解です。これは表現上の障害です。

**別の正確な合成法：線形空間から1点だけ除いた集合。** 3候補の局所表は、4点のアフィン平面から1点を除いたものです。二つの平面の方向が重なれば、穴が埋まるか、一つの穴だけを残して合成できます。[算法と証明](docs/hole_flats.md)は、その集合を要素列挙せずに保持し、必要なとき元の候補を復元します。256グループの例では、257次元のアフィン空間にただ1点だけ穴があることを確定し、到達可能な目標と唯一の到達不能な目標を区別しました。[実験記録](results/hole_flats.json)には、合成が効かず `UNKNOWN` になる実際の3SAT還元像も含みます。

複数の空間が残ったときは、各穴が除く分解数を階数から正確に計算します。合計が全分解数より小さければ、[条件付きの数え上げ](src/pnp_lab/flat_cover.py)で指数個の分解を調べずにSAT証人を作れます。この十分条件が反例でどこまで届かないかも一般式で示しました。線形緩和が常に解を持ち、二つずつの合成が一度も発火せず、穴の除外数の和が厳密な上界判定に足りない入力だけでも、元の3SAT判定を表せます。

[Leanの追加3定理](Formal/HoleFibers.lean)は、左右1点ずつの除外を3通りの分解が回避できることと、2通りの場合の欠損点の公式を扱います。最後の公式では、元の和の分解が指定の2通りで尽きること等を仮定しています。Pythonの全実装・線形代数の階数計算・マイナー普遍性まで形式検証したものではありません。

[並進と分岐を使うマッチング法](docs/gauge_matching.md)は、長さ7の奇数サイクルの候補積268,435,456を、線形条件で128回のマッチング判定へ縮めました。この族では一般に `2^n` 回が残ります。[統合判定器](src/pnp_lab/support_solver.py)は使える特殊算法を試し、既定では未決着なら完全な探索へ進みます。探索を予算で打ち切れば `UNKNOWN` です。CMRの使用は明示指定です。

```bash
python scripts/solve_three_cnf.py examples/three_cnf_odd_cycle.json --encoding sparse --method auto
python scripts/solve_three_cnf.py examples/three_cnf_odd_cycle.json --encoding sparse --method gauge --max-matching-calls 16
```

## 第6段階：3候補・重み2のどこに一般SATが残るか

[証明・実装の対応](docs/support_threshold.md)では、各グループからマスクを一つずつ選び、全体のXORが目標に一致するかを判定します。候補数は「一つのグループに何通りあるか」、重みは「一つの候補がいくつのビットを反転するか」です。

| 制限 | 判定 | 根拠 |
|---|---|---|
| 各グループ2候補以下・重み任意 | 多項式時間 | 候補を選ぶビットについての一次方程式を解く |
| 各候補の重み1以下・候補数任意 | 多項式時間 | [完全マッチングに還元](src/pnp_lab/unit_matching.py)し、元の選択を復元 |
| 各グループ3候補以下、各候補の重み2以下、各座標はちょうど2グループに出現、目標0 | NP完全 | [一般3SATからの還元](src/pnp_lab/ternary_support.py)と双方向の証人変換 |

この表は未解決のクラス分離を仮定しません。最後の行に対する一様な多項式時間判定法があれば、P=NPです。逆にNP完全性から全方式の超多項式下界は出ません。前段階の格子下界は5署名の還元像についてのもので、異なるこの3候補の還元像には移していません。

[統合判定器](src/pnp_lab/support_solver.py)は適用できる多項式時間の方法を自動で選び、残る場合は厳密な探索を行います。3SATは次のコマンドで3候補・重み2の表現から判定できます。

```bash
python scripts/solve_three_cnf.py examples/three_cnf_odd_cycle.json --encoding sparse
```

[3候補への還元の検査](results/ternary_support_threshold.json)と[マッチング法の実験](results/unit_support_matching.json)を収録しました。例えば同じ3候補を前半・後半に並べた連結な重み1の入力族では、中間の異なるXOR値は `2^(m+1)-1` 個あり、すべて実際の解まで延長できます。マッチング法はこれらの値を列挙せず、多項式サイズのグラフでSATを判定します。どちらの実装も返す証人を元の入力で検査します。マッチング実装自体をLeanで形式化したとは主張しません。

## 第5段階：個数を数えずにSATを判定する

[判定の数学と全順序での限界](docs/affine_frontier.md)・[3-CNFから証人を返す実装](src/pnp_lab/frontier_sat.py)・[実験結果](results/affine_frontier.json)。候補のXOR和が目標を取れるかだけを調べます。ある局所表がアフィン部分空間の平行移動をちょうど埋める場合、そのブロックは線形代数で吸収できます。残るブロックでは、後続の候補のアフィン包に照らして完成不能な途中状態を除きます。SATなら元の符号付き節に戻して証人を検査し、指定予算で未決着なら `UNKNOWN` と返します。

- 独立な正の3節128個では、384グループすべてを吸収し、残余遷移0回でSAT。表作成と線形代数の費用は別途かかります。
- 同じ長さ9の奇数サイクルで、処理順の変更により遷移が745,225回から16,015回へ減少。長さ31も辺ごとの順なら60,895回でUNSAT。
- 一方、正の2節を並べた偶数辺長 `h` の正方格子では、どの固定順序でも、実際に解へ延長できる異なる途中和が少なくとも `2^(h/9)` 個ある層が生まれます。この入力自体は全真で充足します。よい順序を選ぶことだけでは、この全状態を保持する実装の多項式時間性は証明できません。

```bash
python scripts/solve_three_cnf.py examples/three_cnf_odd_cycle.json
python scripts/solve_three_cnf.py examples/three_cnf_odd_cycle.json --max-transitions 0
```

上はUNSAT、下はUNKNOWNです。JSONの `variables` は変数名、`clauses` は1始まりの符号付きリテラル列です。`group_order` で還元後のグループの順列を指定できます。

[Leanでの4定理](Formal/AffineFrontier.lean)は、元の候補による証人、必要条件で枝を除いても到達可能性を保つこと、後続の署名をまとめる際の必要条件、正確なアフィン集合の吸収を扱います。行消去の実装・格子下界・計算時間は、このLeanモジュールの定理には含まれていません。

## 第4段階：先行研究を調べ、共同推論と署名による計数へ進む

### openai/mathに見つかったETH反証の主張

指定された [`openai/math`](https://github.com/openai/math) をコミット `4eaee87548250b2682affda7d05d947c05554bae` に固定して調べました。family 378 は **固定幅CNFの厳密なモデル数を劣指数時間で数える**という、ETHに直接関係する主張です。[先行研究調査](docs/prior_work.md)、[形式化の意味の監査](docs/eth_formal_audit.md)、[再利用したものとしなかったもの](docs/openai_math_reuse.md)を分けて記録しています。

Leanの対象定理が述べる上界は、入力符号長を `L`、変数数を `n`、固定した節幅を `k` として

\[
(L+1)^{O_k(1)}\,2^{O_k(n(\log\log n)^2/\sqrt{\log n})}.
\]

これは論文の最も鋭い上界より弱い形式化です。正しければETHに反しますが、この上界から多項式時間は出ません。**ETHの反証とP=NPの証明は別の到達点です。** 上界が多項式より大きいことも、算法の実時間が超多項式である証明にはなりません。

[独立した検討会の案内](https://ethdiscussion.blog/2026/10/26/eth-refutation-examination-and-discussion/)は、主催者の参加を認証と受け取らないよう明記しています。本研究室でも、定理の量化・有限機械・実行時間・入力符号化を読む作業と、カーネルで再ビルドする作業を区別しました。[固定版の再ビルドworkflow](.github/workflows/upstream-math.yml)と[監査実行記録](results/upstream_math_audit.json)に、実行できた範囲を記します。完全なComparator再検証や論文全体の独立検証を済ませたとは主張しません。

35分上限で行った再ビルドは途中でキャンセルされ、終端定理とその公理依存の検査には届きませんでした。取得したログにLeanの証明エラーはありませんが、これを検証成功とは扱いません。上流ソースを変えずに行った[180分上限の再実行](https://github.com/HeliCorgi/p-vs-np-lab/actions/runs/41714504846)は157分36秒でfailureになりました。ビルド完了・公理検査の記録はなく、ジョブログは取得できませんでした。特定の証明エラーや時間切れとは判定できません。[終了時のステップ記録](results/upstream_replay_event_41714504846.json)も保存しています。

[必要部分15ファイル](third_party/openai_math/README.md)をApache-2.0ライセンスと出典・ハッシュ付きで収録しました。上流のLean 4.34.1と本研究室のLean 4.19.0を別々に検査します。

### CNFとXORの共同推論で、前回の符号化障壁を越える

XOR行の各変数に二項節 `pivot OR partner` があるとき、すべてのpartnerを偽にするとpivot側の値が強制されます。その値がXORと矛盾するなら、**partnerの論理和が帰結**します。否定リテラル、共有変数、重複したpartnerを許す意味論を [`Formal/JointXorClause.lean`](Formal/JointXorClause.lean) で証明しました。実装は幅3以下の入力XOR行と入力の二項節だけを1回調べるため、この発見処理は多項式時間です。

これにより3SAT橋渡しの元の節が回復し、その後のパリティ推論で奇数サイクルを反証できます。[実験と全サイズの議論](docs/joint_reasoning.md)は、前回のCNF単独のfull-hull定理と矛盾しません。今回は既存のXORも前提に使っています。

| 入力 | 第4段階の結果 | 残る範囲・費用 |
|---|---|---|
| 三角形を橋渡し変換した21変数の入力 | 6個の節を導出し、0セルでUNSAT。合成証明書を独立検査 | 前回は32,768セルを実際に列挙 |
| 長さ101の奇数サイクルを変換した707変数の入力 | 0セルでUNSAT、証明書検査 | 前処理の費用は計上。旧方式の `2^505` セルは式からの予測 |
| 16変数のexactly-two CNF＋奇数パリティ | 32,768セルを実際に列挙してUNSAT | 二項の前提がなく、新規則が発火しない。全サイズでこの方式の超多項式例 |

```bash
python scripts/solve_mixed.py examples/bridge_triangle_unsat.json --joint --max-cells 0 --verify-certificate
python scripts/solve_mixed.py examples/exact_two_unsat.json --joint --max-cells 0
```

前者は証明書付きUNSAT、後者は `UNKNOWN` です。`--joint` は共同推論の後に従来のパリティ推論を含みます。既知のXOR学習・混合ソルバー研究との関係を[先行研究ノート](docs/prior_work.md)に記し、新規性や一般多項式時間は主張しません。

### 上流の有限な恒等式を、実際に動く計数法として取り出す

上流論文の「測定値を固定して和を分離する」部分を、GF(2)のブロック署名に特殊化しました。各ブロックのCNFを満たし、XORへの寄与が `s` になる割当数を `T_g(s)` とすると、

\[
\#F=\sum_{s_1\oplus\cdots\oplus s_g=b}\prod_iT_i(s_i).
\]

[`count_by_signatures`](src/pnp_lab/signatures.py) は多重度を保った畳み込みで厳密に計数し、元変数上の証人を返します。**256個の3変数exactly-oneブロック、計768変数**では、2,048個の局所割当と256回の表の積を調べて `3^256` 個のモデルを数えました。2ビットの署名では4状態の合成も確認しています。

一般のCNFを任意に分割できるとは仮定しません。グループをまたぐCNF節は明示的に拒否します。また恒等測定 `s=u` では、幅 `b` のブロックに `2^b` 個の表要素が必要です。幅14で16,384要素を実測し、すべての幅に対する理由も[計数ノート](docs/signature_counting.md)に記しました。整数のビット演算費用も別途かかり、上流の劣指数算法全体を実装したものではありません。

[上流パラメータの厳密な計算](results/upstream_parameters.json)では、大入力用スケジュールの一つの必要条件が最初に成立するのが `n=2^521283+1` であることと、その後いったん不成立へ戻る非単調性を確認しました。これは完全な切替閾値でも、上流定理の反例でもありません。

### 解決条件をさらに絞る：最大5変数のブロックでも一般3SATが入る

[一定サイズのブロックへの還元](docs/constant_block_bridge.md)を追加しました。まず各非空節を最後のリテラルの反復で3出現にそろえてから、各出現に別々のコピーを割り当て、同じ元変数のコピーを含意の輪で同じ値に拘束します。それから3SAT→CNF＋XORの橋渡しを使い、各コピーとその補助変数を一つのグループにします。

空でない節からなる `m` 節の入力では、**ちょうど `3m` グループ、高々 `4m` 本のXORと `15m` 変数、各グループ最大5変数**です。CNFはグループ内に収まり、XORは互いに素な3変数の式です。各局所表の作成は最大32割当の検査で済み、異なる署名は高々5個です。それでも、このクラスは一般3SATから多項式時間で還元でき、SAT判定としてNP完全です。モデル数を保つ還元ではありません。

したがって、局所ブロックの小ささは確保できました。**この構造での全体の合成を、一様かつ常に多項式時間で処理できること**が、P=NPへ届く具体的な残りの証明義務です。NP完全性だけから超多項式下界を主張してはいません。現行の表を列挙する実装には別途、指数個の合成状態を残す例があり、その例自体は成分分解などで改善できる容易な入力です。

## 第3段階の記録：証明書付きのパリティ推論と、その方式全体の限界

以下の探索結果は `--parity-cuts` 単独の記録です。橋渡し変換された奇数サイクルについては、上の第4段階の `--joint` が改善しています。

[今回の研究ノート](docs/parity_cuts.md)では、CNFから正当なXOR方程式を導いてから線形消去する前処理を追加しました。「少なくとも一つ真」という節と、すべての対について「同時に真にはならない」という二項節があれば、ちょうど一つ真なので、そのリテラルのXORは1です。否定リテラルの符号も式の右辺へ正しく移します。

元のCNFを残し、含意される方程式だけを追加するため、SAT/UNSATと元のモデル数を保存します。各推論は元の節番号を持つ証明書を出し、線形矛盾は入力行・導出行のどれをXORすると `0=1` になるかで示します。独立チェッカーは推論の発見器やGaussian消去を呼ばずに、この短い矛盾証明を検査します。

| 入力 | 前処理を加えた結果 | 範囲 |
|---|---|---|
| 256変数のexactly-one CNF＋偶数パリティ | 0セルでUNSAT、証明書検査成功 | 前処理の費用はかかります。旧算法の `2^255` セルは一般式からの予測で、全列挙していません |
| 64個の3変数exactly-oneブロック＋逆の全体パリティ | 192変数で0セル。65本の行を組み合わせた矛盾 | 各ブロック単独では矛盾せず、全体のXORで検出 |
| 16変数のexactly-two CNF＋奇数パリティ | 32,768セルを実際に列挙してUNSAT | 新しい規則は発火せず、最悪時間は依然として超多項式 |
| 3変数の奇数サイクルを直接記述 | 0セルでUNSAT | 二項節からXORを導いて矛盾 |
| 同じサイクルを第2段階の3SAT変換で記述 | 21変数・32,768セルを実際に列挙 | 等充足な符号化でも推論の効き方が変わる |

### パターン認識の改善だけでは越えられない境界

空節を含まない3SAT入力を変換したとき、CNF部分は

\[
 F(o,h)=\bigwedge_i\bigl(\ell_i(o)\lor h_i\bigr)
\]

という形で、各補助変数は正のリテラルとして一つの節だけに出ます。このCNFのモデル集合のaffine hullは全空間です。したがって、**このCNF単独から含意されるXOR方程式は恒真式 `0=0` だけ**です。

証明は各座標について「その一ビットだけが違う二つのCNFモデル」を作ることです。元変数は全補助変数を1にして反転できます。補助変数は相手の元リテラルを真にしてから反転できます。全モデルで一定のXOR式は、どの座標の係数も1にできません。

これは今回のexactly-one検出器だけの限界ではありません。**CNFだけからXORの帰結を完全に抽出できても、この変換先を強化できません。** 元のXORも前提にする共同推論や、分岐条件の下での推論は、この定理の対象外です。P≠NPの証明ではありません。

[`Formal/ExactlyOneParity.lean`](Formal/ExactlyOneParity.lean) は任意長・符号付きの推論とモデル保存を、[`Formal/BridgeAffineBarrier.lean`](Formal/BridgeAffineBarrier.lean) は任意の有限XOR行に対する上の不可能性を証明します。[座標証明書のチェッカー](src/pnp_lab/affine_hull.py)では、707変数の変換先まで全モデルを列挙せずに確認しています。[実験結果](results/parity_cuts.json)には、小さい完全な証明書も保存しました。

```bash
python scripts/solve_mixed.py examples/mixed_unsat.json --parity-cuts --max-cells 0 --verify-certificate
python scripts/solve_mixed.py examples/exact_two_unsat.json --parity-cuts --verify-certificate
python scripts/solve_mixed.py examples/bridge_triangle_unsat.json --parity-cuts --max-cells 32
```

`--max-cells` は代表元の列挙予算です。最初の例は前処理だけでUNSATが確定し、最後の例は予算切れの `UNKNOWN` になります。推論の認識・短い証明の検査は入力サイズの多項式で済みますが、残る探索と、その列挙証明書は指数サイズになり得ます。

## 第2段階：解決条件から逆算した、前処理なしの混合ソルバー

まず [何を示せばP vs NPの解決になるか](docs/solution_criteria.md) を固定しました。P=NPへの今回の経路は、一般3SATを含む入力すべてに対する、一様・決定的な正しい判定と、総ビット計算時間の固定多項式上界です。

| 追加物 | 到達点 |
|---|---|
| [3SAT→二項CNF＋XORの還元](docs/two_cnf_xor_reduction.md) | 2-SAT型の節と、互いに素な3変数XORの混合でも一般3SATが入ることを明示。式全体の充足可能性を保つ論理をLeanで証明 |
| [混合ソルバー](docs/mixed_solver.md) | 任意の有限XOR＋CNFを正確に判定し、SAT証人を復元。必要なら全セルを含むUNSAT証明書を出力 |
| [構造化実験と反例族](docs/mixed_constraints.md) | 256変数でも8セルで扱える例と、判定モードで指数個を列挙する例の両方を確認 |
| [解決条件からの逆算](docs/reverse_engineering.md) | 一般SATへの適用範囲、正当性、最悪計算量を別々の証明義務として整理 |

### 一般3SATへ戻れる接続

各節にfreshな補助変数 `u,v,w` を用意すると、

\[
a\lor b\lor c\quad\Longleftrightarrow\quad
\exists u,v,w:\ (a\lor u)\land(b\lor v)\land(c\lor w)
\land(u\oplus v\oplus w=0).
\]

全リテラルが偽なら補助変数が全部1に強制され、偶数パリティと矛盾します。どれかが真なら対応する補助変数を0、残りを1にできます。元の `n` 変数・`m` 個の3リテラル節は、`n+3m` 変数・`3m` 個の二項節・`m` 本のXORへ写ります。

**この限定された混合クラスを一般に多項式時間で解ければP=NP**です。各片が容易なことだけでは混合も容易とは言えません。これは充足可能性を保存する還元で、モデル数は保存しません。[還元コード](src/pnp_lab/reductions.py) と [Leanの式全体の同値定理](Formal/ThreeSatBridge.lean) を追加しました。初等的な構成であり、新規性は主張しません。

### 候補の計算量と、確認できた限界

XORを消去して `x=x0+B t` と書きます。自由次元を `d`、CNFが観測する係数形式の階数を `r` とすると、各同値類から1代表を持ち上げて `2^r` 個だけ調べれば正確に判定できます。上界は `poly(N)+2^r poly(N)`。`N` は入力のビット長で、長整数の演算費用も含めます。

| 入力族 | 自由次元d | 観測階数r | 検査した代表元 |
|---|---:|---:|---:|
| 64変数、少数の形式のコピーと未観測方向 | 34 | 3 | 8 |
| 128変数、同じ構造 | 65 | 3 | 8 |
| 256変数、同じ構造 | 130 | 3 | 8 |
| 16変数、exactly-one CNF＋偶数パリティ | 15 | 15 | 32,768 |

最初の3例はモデル数も検査する完全列挙です。最後は **SATの証人があれば停止する判定モード**ですが、矛盾するため全代表元を調べます。一般のk変数の同族で必ず `2^(k-1)` 個を調べ、通常の符号化で入力長は `Θ(k² log k)`。したがって、**このアルゴリズムには超多項式の最悪例があり、一般多項式時間という主張は成立しません**。容易に認識できるこの族は、別アルゴリズムやP≠NPの下界ではありません。

上の3SAT還元でも、元変数がすべて出現する場合 `r=d=n+2m` です。適用範囲を確保する還元であって、この列挙法を高速化する変換ではありません。この段階で残った非線形制約の処理を、第3段階の前処理で拡張しています。

### ソルバーを動かす

```bash
python scripts/solve_mixed.py examples/mixed_sat.json --count-models
python scripts/solve_mixed.py examples/mixed_unsat.json --verify-certificate
python scripts/solve_mixed.py examples/mixed_unsat.json --max-cells 2
```

最後は `UNKNOWN` と終了コード2を返します。予算切れをUNSATにしません。SAT/UNSAT確定は終了コード0、入力・引数エラーは1。通常は最初のSAT証人で停止し、暗黙の上限は設けません。`--count-models` は全セルを調べます。UNSAT証明書は指数サイズになり得るので、`--certificate` / `--verify-certificate` の明示指定です。

[QuotientSearch.lean](Formal/QuotientSearch.lean) は、正しい代表元の被覆と持ち上げを仮定した判定の論理を証明します。Pythonの線形消去や、元のCNFが各同値類で一定になるという橋渡しまで形式化したわけではありません。3SAT還元の定理も、Turing機械の符号化・実行費用まで形式化したものではありません。

## 最初の研究で確認したこと

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

Lean 4.19.0とStdのみを使用します。主要62定理の実際の推移的な公理依存を [`scripts/audit_axioms.py`](scripts/audit_axioms.py) で取得し、標準の `propext`、`Classical.choice`、`Quot.sound` 以外を拒否します。通常のカーネル判定を用い、証明穴やネイティブ評価への信頼で有限命題を埋めません。

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

- 307件の意味論テスト。GF(2)射影120系・結合80組の固定seed比較、共有変数や色名を誤って消す負例を含みます。
- 星グラフ4ケース、パリティ10ケース、GF(2)7ケース、混合制約の構造化例と136例の独立oracle照合、3SAT還元の検査。
- 第3段階の推論・反例・符号化比較。さらに160例・10,200割当を元入力の独立全探索と照合し、707座標までのfull-hull証明書を検査。
- 第4段階の共同推論160例・5,714割当、署名計数144例・8,176割当の独立照合、全サイズの反例族に対応する有限実験。
- 最大5変数のブロックへの還元を50入力・344個の元割当で照合し、262個の元モデルの持ち上げを検査。独立な節の族について、局所表が定数サイズでも現行の合成表が指数的に増えることを確認。
- openai/mathの15ファイルのハッシュ・出典照合と、上流スケジュールの整数計算。これは上流の定理のカーネル検証とは別です。
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
| [`docs/solution_criteria.md`](docs/solution_criteria.md) | P=NP／P≠NPの厳密な証明条件 |
| [`docs/reverse_engineering.md`](docs/reverse_engineering.md) | 現在の算法・一般SATへの還元・計算量の不足箇所 |
| [`docs/research_notes.md`](docs/research_notes.md) | 第1段階の研究記録 |
| [`docs/prior_work.md`](docs/prior_work.md) | ETHの最近の主張、CNF-XOR学習、証明ログの先行研究 |
| [`docs/eth_formal_audit.md`](docs/eth_formal_audit.md) | 上流終端定理の量化、機械モデル、符号化、有限フォールバックの監査 |
| [`docs/joint_reasoning.md`](docs/joint_reasoning.md) | CNFとXORの共同推論、証明書、改善と残る反例 |
| [`docs/signature_counting.md`](docs/signature_counting.md) | 署名による厳密計数の恒等式、実装、費用 |
| [`docs/constant_block_bridge.md`](docs/constant_block_bridge.md) | 最大5変数・5署名の局所ブロックによる一般3SATの表現と、残る合成問題 |
| [`third_party/openai_math/README.md`](third_party/openai_math/README.md) | 再利用元の固定版、ライセンス、出典manifest |
| [`docs/parity_cuts.md`](docs/parity_cuts.md) | 第3段階の推論、証明書、全サイズの限界、先行研究 |
| [`src/pnp_lab/parity_cuts.py`](src/pnp_lab/parity_cuts.py) | 推論の生成・独立検査・混合ソルバーへの接続 |
| [`src/pnp_lab/affine_hull.py`](src/pnp_lab/affine_hull.py) | CNFのfull-hull証明書の生成と独立検査 |
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
