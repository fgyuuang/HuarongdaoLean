# 曹操与关羽位置空间研究报告

本报告对应以下 Lean 文件：

- [CaoGuanGeometry.lean](/D:/learn/AI4math_summer_school/HuarongdaoLean/Huarongdao/CaoGuanGeometry.lean)
- [CaoGuanReportMain.lean](/D:/learn/AI4math_summer_school/HuarongdaoLean/CaoGuanReportMain.lean)
- [cao-guan-fiber-report.json](/D:/learn/AI4math_summer_school/HuarongdaoLean/output/cao-guan-fiber-report.json)

## 1. 状态模型

严格的语义状态取为

```lean
ValidClassicState := { state : State // ValidState state }
```

它保留十个有身份棋子的完整左上角坐标，并排除越界和重叠。具体合法移动由

```lean
ClassicStateSpaceKernel.concrete.step
```

给出。其无向状态图是

```lean
concreteStateGraph
```

即 `StateSpace.Task.simpleGraph concrete concreteReversible`。

数值报告另外使用现有的 `allShapeStates`。它是 65,880 个不区分同形棋子标签的合法几何放置；报告中的固定纤维统计是在这个有限数组上按合法滑动重新构造的诱导图。这样既保留完整语义定义，也使统计可以由程序重算。

## 2. 曹操和关羽位置空间

曹操是 `2 × 2` 方块，棋盘是 `4 × 5`。若 `(x,y)` 是曹操左上角，则

```text
0 <= x <= 2,  0 <= y <= 3.
```

Lean 中定义为

```lean
abbrev CaoPosition := Fin 3 × Fin 4
```

其中第一坐标是列，第二坐标是行。因此

```lean
theorem caoPosition_card : Fintype.card CaoPosition = 12
```

严格证明曹操共有 12 个可能左上角位置。

关羽是 `2 × 1` 横长方块，因此

```text
0 <= x <= 2,  0 <= y <= 4.
```

Lean 中定义为

```lean
abbrev GuanYuPosition := Fin 3 × Fin 5
```

并证明

```lean
theorem guanYuPosition_card : Fintype.card GuanYuPosition = 15
```

## 3. 观测映射和纤维

严格观测映射为

```lean
def caoPositionObservation :
    ValidClassicState -> CaoPosition

def guanYuPositionObservation :
    ValidClassicState -> GuanYuPosition

def jointObservation :
    ValidClassicState -> CaoPosition × GuanYuPosition
```

其中 `pi_C`、`pi_G` 是对应的记号别名。坐标被转换回原始棋盘坐标的定理是：

```lean
caoPositionObservation_toPos
guanYuPositionObservation_toPos
```

对 `p : CaoPosition`，定义曹操纤维

```lean
def caoFiber (p : CaoPosition) : Set ValidClassicState :=
  {state | caoPositionObservation state = p}
```

即

\[
F_p=\{s\in S\mid \pi_C(s)=p\}.
\]

同理定义 `guanYuFiber` 和联合纤维 `jointFiber`。

固定曹操位置的合法变化不应被理解为“曹操可以移动”。正确的诱导图是

```lean
def fixedCaoGraph (p : CaoPosition) :
    SimpleGraph {state : ValidClassicState // state ∈ caoFiber p}
```

它正是

\[
G_p=G[F_p].
\]

在该图中，曹操位置不变的边只能由其他棋子产生。对应的可移动棋子谓词为

```lean
movablePieceWithinCaoFiber
```

并且已经证明：任意非曹操棋子的合法一步移动都给出同一曹操纤维内的边。

## 4. 四种距离及其区别

### 4.1 坐标 Manhattan 距离

对原始坐标定义

\[
d_{\mathrm{coord}}((x,y),(x',y'))
=|x-x'|+|y-y'|.
\]

Lean 定义 `coordinateManhattan`，并在 `CaoPosition` 与 `GuanYuPosition` 上分别定义：

```lean
caoCoordinateManhattan
guanYuCoordinateManhattan
```

这只比较两个左上角坐标，不查看棋盘上其他棋子。

### 4.2 曹操位置诱导图距离

定义 `caoPositionGraph`：

\[
p\sim q
\]

当且仅当存在 `s ∈ F_p`、`t ∈ F_q`，使具体状态图中 `s` 与 `t` 相邻，并且 `p\ne q`。对应距离为：

```lean
caoPositionGraphEdist
caoPositionGraphDist
```

这是存在代表元意义下的投影图距离。它可以把不同具体代表之间的合法边压缩成同一条位置边。

### 4.3 具体状态图最短距离

对合法状态 `s,t` 定义：

```lean
concreteStateGraphEdist s t
concreteStateGraphDist s t
```

其中 `edist` 取值于 `ℕ∞`；若两状态不连通，距离为 `⊤`。自然数版本 `dist` 是其 `toNat`，因此应只在已知连通时解释为通常的最短路长度。

### 4.4 两个纤维之间的最小距离

定义

\[
d_{\min}(F_p,F_q)
=\inf_{s\in F_p,\;t\in F_q}d_G(s,t).
\]

Lean 中的

```lean
caoFiberMinEdist
```

直接使用两个纤维子类型上的 `iInf`，空纤维和不连通情形仍由 `ℕ∞` 保留。

### 4.5 纤维之间的 Hausdorff 距离

使用具体状态图的扩展距离，定义定向距离

\[
d_{\to}(F_p,F_q)
=\sup_{s\in F_p}\inf_{t\in F_q}d_G(s,t),
\]

再定义

\[
d_H(F_p,F_q)
=\max\{d_{\to}(F_p,F_q),d_{\to}(F_q,F_p)\}.
\]

Lean 对应：

```lean
caoFiberDirectedHausdorff
caoFiberHausdorff
```

这一步暂时采用 `ℕ∞` 上的 `iSup/iInf`，因此不需要假设纤维非空或所有状态属于同一个连通分支。若后续只研究经典可达分支，可以在该子空间上证明有限性、对称性和三角不等式。

## 5. 坐标相邻不代表存在合法一步

定义状态依赖的一步观察关系：

```lean
def oneStepCaoPosition
    (source : ValidClassicState) (targetPosition : CaoPosition) : Prop
```

它要求源状态固定，存在一个具体合法动作把曹操观测送到目标位置。这和 `caoPositionGraph` 不同：后者允许为两个位置选择不同的代表状态。

经典初态中：

\[
\pi_C(s_{\mathrm{classic}})=(1,0),\qquad
p_{\downarrow}=(1,1),
\]

且

\[
d_{\mathrm{coord}}\bigl((1,0),(1,1)\bigr)=1.
\]

但是曹操向下移动后会占据第 1、2 行的两列，而关羽位于

\[
\{(1,2),(2,2)\},
\]

发生重叠。因此

```lean
theorem classic_cao_down_is_illegal :
    tryMove classic .caoCao .down = none

theorem classic_has_no_one_step_to_adjacent_cao_position :
    ¬ oneStepCaoPosition classicValid classicCaoDownPosition
```

严格给出反例。这证明：

\[
d_{\mathrm{coord}}(\pi_C(s),p)=1
\not\Rightarrow
\exists t\;(s\sim t\land \pi_C(t)=p).
\]

正确的单步判定必须检查移动棋子的扫掠区域是否越界、是否与其他棋子重叠；不能只检查曹操左上角的坐标差。

## 6. 固定曹操位置的有限统计

统计程序：

```text
lake build report-cao-guan
.lake/build/bin/report-cao-guan.exe output/cao-guan-fiber-report.json
```

报告对象是 `allShapeStates` 的 65,880 个几何放置。12 个纤维的状态数总和为 65,880。

表中 `最大分支` 是该固定位置诱导图中最大连通分支的大小，`最大直径` 是所有连通分支直径的最大值；因此它不是把不连通图误报成一个有限直径。

| 曹操位置 | 状态数 | 分支数 | 最大分支 | 最大分支直径 | 有向合法边数 |
|---|---:|---:|---:|---:|---:|
| (0,0) | 7815 | 86 | 5373 | 133 | 25210 |
| (1,0) | 6795 | 150 | 1637 | 96 | 20964 |
| (2,0) | 7815 | 86 | 5373 | 133 | 25210 |
| (0,1) | 3525 | 215 | 443 | 41 | 10302 |
| (1,1) | 3465 | 174 | 78 | 28 | 10106 |
| (2,1) | 3525 | 215 | 443 | 41 | 10302 |
| (0,2) | 3525 | 215 | 443 | 41 | 10302 |
| (1,2) | 3465 | 174 | 78 | 28 | 10106 |
| (2,2) | 3525 | 215 | 443 | 41 | 10302 |
| (0,3) | 7815 | 86 | 5373 | 133 | 25210 |
| (1,3) | 6795 | 150 | 1637 | 96 | 20964 |
| (2,3) | 7815 | 86 | 5373 | 133 | 25210 |

每个纤维中，曹操的内部可移动计数为 0；关羽、张飞、赵云、马超、黄忠以及四个兵在每个纤维中都至少有一个状态可以在不改变曹操位置的前提下移动。`movablePieceCounts` 数组保存在 JSON 中，数组顺序与 `pieceLabels` 一致，是“允许该棋子在纤维内移动的状态数”，不是动作条数。

这些数据还显示，固定曹操位置后的图通常高度不连通。因而不能用一个单一的“位置距离”替代具体状态距离：同一位置纤维内部也可能存在多个互不连通的组件。

## 7. 投影和相似度的后续形式化

对任意合法状态集合 `A ⊆ S`，投影算子定义为像集：

\[
\Pi_C(A)=\pi_C[A]\subseteq P_C,
\]

\[
\Pi_G(A)=\pi_G[A]\subseteq P_G,
\]

\[
\Pi_{C,G}(A)=\Pi[A]\subseteq P_C\times P_G.
\]

Lean 中对应：

```lean
projectCao
projectGuanYu
projectJoint
```

后续可以在三种层次定义相似度：

1. **位置相似度**：对位置点使用 Manhattan 核
   \[
   K_\lambda(p,q)=\exp(-\lambda d_{\mathrm{coord}}(p,q)).
   \]
2. **纤维相似度**：使用
   \[
   \exp(-\lambda d_{\min}(F_p,F_q))
   \quad\text{或}\quad
   \exp(-\lambda d_H(F_p,F_q)).
   \]
3. **联合观测相似度**：在
   \(P_C\times P_G\) 上使用加权距离
   \[
   d_\alpha((p,g),(q,h))
   =\alpha d_C(p,q)+(1-\alpha)d_G(g,h).
   \]

若需要概率化统计，可以给每个纤维赋予枚举分布

\[
\mu_p(s)=\frac{1}{|F_p|}\mathbf 1_{s\in F_p},
\]

再比较纤维分布的 Wasserstein 距离或基于图核的相似度。当前代码只实现了投影、图距离和 Hausdorff 距离的定义接口，没有把这些后续选择强行固定成唯一的泛函分析结构。

## 8. 当前结论范围

- 12/15 个位置空间和观测映射已经是 Lean 中的严格定义。
- 纤维、固定纤维诱导图和五种距离对象已经定义。
- “坐标相邻不一定一步可达”已有经典初态的形式化反例。
- 固定曹操位置的有限枚举统计已经可执行并输出 JSON。
- 数值表针对完整 `allShapeStates` 几何放置；若只研究经典初态所在 25,955 状态可达分支，应在报告程序中再加入全局组件标签过滤。

## 9. 关羽位置追踪与联合观测

新模块

```text
Huarongdao/GuanYuYield.lean
```

保留前文的严格定义：

```lean
GuanYuPosition := Fin 3 × Fin 5
pi_G := guanYuPositionObservation
jointObservation s :=
  (pi_C s, pi_G s)
```

其中 `π_G` 读取关羽横向 `2×1` 木块的左上角。联合观测只保留曹操和关羽两个 distinguished pieces 的位置，其他八个棋子的坐标被隐藏。

## 10. 出口通道、门区和让路事件

对于任意原始状态 `s`，先把曹操向下平移一个格得到几何候选状态

```lean
caoDownSweepTarget s
```

不要求候选状态本身合法。曹操在该候选移动中新增占据的格子为

```lean
caoDownSweepCells s
```

定义关羽对该次下降的阻塞度：

```lean
guanYuCaoSweepBlockage s : Nat
```

它是 `caoDownSweepCells s` 中同时被关羽占据的格子数。因曹操是 `2×2` 方块，正常向下移动时该数值在几何上最多为 2。

状态门区取为：

```lean
CorridorOpen s := CaoCanDescend s
GuanYuGate s := GuanYuClearsCaoSweep s
```

前者表示曹操当前有合法的向下移动；后者表示存在一个合法的曹操向下移动，且关羽不占据新增扫掠格。已有 Lean 定理给出：

```lean
classic_solution_visits_corridor_open :
  SolutionGate classic CorridorOpen

classic_solution_visits_guanYu_gate :
  SolutionGate classic GuanYuGate
```

这两个定理是状态层面的弱门定理，不声称某个关羽动作刚刚发生。

动作层面的“关羽让路”定义为：

```lean
GuanYuYield source action target :=
  tryMove source action.piece action.direction = some target ∧
  action.piece = .guanYu ∧
  guanYuCaoSweepBlockage target <
    guanYuCaoSweepBlockage source
```

因此它同时要求：

1. `source -> target` 是实际合法一步；
2. 移动棋子确实是关羽；
3. 关羽移动后，曹操下一次向下扫掠的阻塞度严格下降。

这个定义避免把“关羽移动”简单等同于“关羽让路”。例如关羽移动后若阻塞度不降，则不计为 `GuanYuYield`。

## 11. 经典解与强命题检查

可执行检查器为：

```text
GuanYuYieldMain.lean
```

运行：

```text
lake build check-guan-yu-yield
lake env .lake/build/bin/check-guan-yu-yield.exe
```

对现有 116 步经典解，扫描得到 6 个让路事件，步号从 0 开始：

```text
2: 关羽左  2 -> 1
13: 关羽右 2 -> 1
49: 关羽左  2 -> 1
50: 关羽左  1 -> 0
68: 关羽下  2 -> 0
82: 关羽下  2 -> 0
```

这验证了显式经典解满足强命题。

此外，检查器在 `State.key` 的同形棋子商图上执行完整 BFS，并从所有合法动作中删除 `GuanYuYield` 边。结果为：

```text
avoid-yield quotient BFS: no goal found
```

因此在当前有限的经典同形商状态图上，未发现任何完全避开 `GuanYuYield` 的目标路径。结合商图的合法动作枚举，这给出了强命题的可执行有限验证：

\[
\forall w:\text{classic 到目标的合法路径},\quad
\exists i,\ \operatorname{GuanYuYield}(w_{i-1},a_i,w_i).
\]

这里需要区分“可执行验证”和“内核定理”：当前检查器的 BFS 结果是可重放的程序证据，但还没有像 `classic116Play_minimal` 那样封装成一个完整的 Lean 有限闭包证书。若后续需要内核级强定理，应为“禁用 `GuanYuYield` 的子图”增加闭包、覆盖和无目标证书。

## 12. 联合观测并不足以决定出口状态

联合观测

```lean
Pi s = (pi_C s, pi_G s)
```

保留了两个关键木块的位置，但不保留其他棋子的占用信息。由于 `CaoCanDescend` 还会受到其他棋子阻挡，`Pi` 不是 `CorridorOpen` 的充分统计量。

在 `allShapeStates` 的有限几何枚举中，检查器找到同一联合坐标

```text
(pi_C, pi_G) = ((0,0),(2,0))
```

对应的两个合法状态，其中一个满足 `CorridorOpen`，另一个不满足。具体代表状态为：

```text
not open:
曹操 (0,0)，关羽 (2,0)，竖块 (0,3),(1,3),(2,3),(3,3)，
兵 (0,2),(1,2),(2,2),(3,2)

open:
曹操 (0,0)，关羽 (2,0)，竖块 (0,3),(1,3),(2,3),(3,3)，
兵 (2,1),(3,1),(2,2),(3,2)
```

两者的曹操和关羽位置完全相同，但曹操向下移动的新增扫掠区被不同的兵布局处理，因此出口状态不同。这说明联合观测适合做几何追踪和统计分层，但不能替代完整状态。

## 13. 后续投影与相似度形式化

对状态集合 `A ⊆ S`，现有投影定义为：

```lean
projectCao A
projectGuanYu A
projectJoint A
```

后续可在联合空间上定义

\[
d_\alpha((p,g),(q,h))
=\alpha d_C(p,q)+(1-\alpha)d_G(g,h),
\qquad 0\leq\alpha\leq1.
\]

其中 `d_C`、`d_G` 是两个位置空间上的 Manhattan 距离。纤维层面可以继续使用：

\[
d_{\min}(F_p,F_q)=
\inf_{s\in F_p,t\in F_q}d_G(s,t),
\]

\[
d_H(F_p,F_q)=
\max\left\{
\sup_{s\in F_p}\inf_{t\in F_q}d_G(s,t),
\sup_{t\in F_q}\inf_{s\in F_p}d_G(s,t)
\right\}.
\]

位置相似度可取 `exp(-λ d)`，纤维相似度可取 `exp(-λ d_min)` 或 `exp(-λ d_H)`。这些是后续选择，不应与当前已证明的图论事实混为一个唯一的泛函分析结构。
