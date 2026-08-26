# 经典华容道状态空间复现与 Lean 4 研究路线

本文区分三件容易混在一起的事：

1. **状态空间**：哪些棋盘局面合法，哪些局面相差一步；
2. **商图与结构定理**：哪些标签、对称或循环区域应视为同一个宏观状态；
3. **三维布局**：怎样给已经存在的图分配 `x,y,z`，让人能看见它。

三维坐标不是数学证明的一部分。更换布局算法不应改变状态、边、可达性、最短距离、桥或割集。

## 1. 视频中的图是怎样生成的

### 1.1 不是 `3d-force-graph`

原互动网站没有加载 Three.js、D3 或 `3d-force-graph`。它读取已经计算好的 `data.json` 中的 `x,y,z`，自行投影后用 Canvas 绘制：

- [网站入口](https://github.com/2swap/Klotski-Webpage/blob/6e27747b2c5b21553ab9c64855d8eb23bee76ca2/index.html#L12-L21)
- [读取预计算坐标](https://github.com/2swap/Klotski-Webpage/blob/6e27747b2c5b21553ab9c64855d8eb23bee76ca2/client.js#L25-L37)
- [三维到二维投影](https://github.com/2swap/Klotski-Webpage/blob/6e27747b2c5b21553ab9c64855d8eb23bee76ca2/client.js#L150-L154)

准确说法是：视频制作工程 `swaptube` 使用作者自写的 C++ 图结构和 CUDA 力导向求解器 `GraphSpread.cu`；在线网站本身不运行力布局，而是显示 `Old-Graph-Spreader` 预计算的坐标。

### 1.2 组合图的生成

上游和本项目采用相同的基本思路：

1. 用 `4 x 5` 棋盘表示一个局面；
2. 枚举每枚棋子的上下左右单格移动；
3. 检查边界与碰撞；
4. 从初态做 BFS；
5. 用忽略同形棋子标签的规范键去重；
6. 每个新局面是节点，每个合法单格移动是边。

上游证据：

- [单格移动、边界和碰撞](https://github.com/2swap/swaptube/blob/b10f93640103c3ab5286c777a52b43d9085929de/src/DataObjects/KlotskiBoard.cpp#L125-L175)
- [BFS 与哈希去重](https://github.com/2swap/swaptube/blob/b10f93640103c3ab5286c777a52b43d9085929de/src/DataObjects/Graph.cpp#L148-L177)
- [枚举所有固定形状摆放](https://github.com/2swap/swaptube/blob/b10f93640103c3ab5286c777a52b43d9085929de/src/Projects/Klotski.cpp#L55-L93)
- [展开不可达连通分量](https://github.com/2swap/swaptube/blob/b10f93640103c3ab5286c777a52b43d9085929de/src/Projects/Klotski.cpp#L1825-L1852)

上游用浮点三角函数哈希消除同形标签，这不适合形式化。本项目的 `State.key` 对四个竖块位置和四个小兵位置分别排序，是可解释的规范化；下一步还应证明：

```lean
State.key s = State.key t ↔ SameShape s t
```

### 1.3 三维展开的技巧

上游布局器采用以下技巧：

- 非邻接点之间施加随距离衰减的排斥力；
- 邻接点之间施加非线性吸引力；
- 超过 5,000 个点后，把空间划成 `10 x 10 x 10` 网格，近处逐点计算，远处用格子质心近似；
- 先在接近四维的空间展开，再逐步压回三维；视频脚本使用约 `3.98 -> 3.95 -> 3` 维；
- 给水平/垂直镜像节点施加坐标约束，避免随机初始化破坏肉眼可见的对称性；
- 分批加入 BFS 新节点，交替做局部松弛，最后再集中退火。

源码：

- [排斥力与吸引力](https://github.com/2swap/swaptube/blob/b10f93640103c3ab5286c777a52b43d9085929de/src/CUDA/GraphSpread.cu#L17-L38)
- [空间网格近似](https://github.com/2swap/swaptube/blob/b10f93640103c3ab5286c777a52b43d9085929de/src/CUDA/GraphSpread.cu#L67-L130)
- [维度压缩](https://github.com/2swap/swaptube/blob/b10f93640103c3ab5286c777a52b43d9085929de/src/CUDA/GraphSpread.cu#L297-L300)
- [视频使用的维度序列](https://github.com/2swap/swaptube/blob/b10f93640103c3ab5286c777a52b43d9085929de/src/Projects/Klotski.cpp#L1328-L1352)
- [镜像配对](https://github.com/2swap/swaptube/blob/b10f93640103c3ab5286c777a52b43d9085929de/src/DataObjects/Graph.cpp#L461-L484)
- [镜像布局约束](https://github.com/2swap/swaptube/blob/b10f93640103c3ab5286c777a52b43d9085929de/src/CUDA/GraphSpread.cu#L260-L285)

`3d-force-graph` 可以做查看器，但不是复现该布局的必要条件。对于 25,955 个点，稳定结果来自有结构的初值、对称约束、近远场分开的排斥近似和维度退火，而不是把全部节点随机扔进普通三维力导向。经典模式直接读取持久化参考坐标；自定义关卡则由浏览器 Worker 从确定性初值本地计算，因此刷新后会重算，但同一输入产生相同坐标。

## 2. 本项目的可复现链

本项目已经把规则来源与显示来源分开：

```text
Lean Model / tryMove
  -> Lean BFS enumerate classic
  -> frontend/graph.json
  -> 按 State.key 对齐上游预计算坐标
  -> frontend/layout.json
  -> 参考 Three.js / 3d-force-graph / 局部探索只负责显示
```

执行：

```powershell
lake build
lake exe export-graph frontend/graph.json
npm run layout
npm run analyze
npm run serve
```

`scripts/import-reference-layout.mjs` 只导入坐标，不导入上游规则或邻接边。坐标受上游 GPL-3.0 约束，见 `THIRD_PARTY_NOTICES.md`。

上游 `data.json` 是带变量声明的 JavaScript 数据，不是严格 JSON；每个邻接表还多重复一个邻居。本项目不读取其邻接关系，因此不会污染 Lean 图。

### 2.1 当前 `3d-force-graph` 复现

经典图工具栏现在提供三种互补视图：

1. **参考全览**：项目原有的自定义 Three.js 点线渲染器；
2. **3D 力导向**：`3d-force-graph@1.80.0` 管理完整 25,955 节点和 41,948 条去重无向边；
3. **局部探索**：自研的小规模弹簧/排斥模拟，只展示已经发现的状态与一步前沿。

完整力导向模式不会随机冷启动。每个节点从 `layout.json` 获得参考位置 `rx,ry,rz`，每条边记录参考长度 `restLength`。默认令

```text
x = fx = rx
y = fy = ry
z = fz = rz
```

因此首次进入即可看到稳定宏观形状。“释放并重新加热”将 `fx/fy/fz` 设为 `null`，调用 `d3ReheatSimulation()`，使用参考边长弹簧、局部截断的 Barnes-Hut 排斥和一个弱参考锚定力做有限松弛；“固定参考形状”会把坐标和速度精确恢复。节点点击仍调用项目原有 `selectRouteNode`，随后只能沿 Lean 导出的合法边逐帧移动棋盘。

这里的关键技巧是把**图的数学内容**与**图的空间嵌入**分开：Lean JSON 是节点和边的权威来源，参考坐标是稳定初值，浏览器力模拟只是交互性扰动。即使重新加热后的形状改变，桥、割集、商图、最短距离和解的存在性都没有改变。

### 2.2 自定义关卡的通用结构布局

`frontend/structural-layout-worker.js` 为任意实验室关卡实现了一条确定性的本地布局管线：

```text
Lean StateGraph
  -> 约五个最远点图距离地标
  -> BFS 较浅邻居附近的生长初值
  -> 四维非线性吸引与排斥
  -> 状态集合中实际存在的水平/垂直镜像配对
  -> dimensions 3.98
  -> dimensions 3.95
  -> 丢弃第四坐标并按平均边长归一化
  -> Three.js / 3d-force-graph 本地绘制
```

它接受如下通用图契约；输出坐标严格按输入节点顺序排列：

```js
{
  startId: "s0",                 // 可选，默认第一个节点
  nodes: [{ id: "s0" }, { id: "s1", distance: 1 }],
  edges: [{ source: "s0", target: "s1" }],
  board: { width: 4, height: 5 }, // 以下三项只用于可选棋盘镜像约束
  shapes: [{ width: 2, height: 2 }],
  // nodes[i].positions = [{ x, y }, ...]
}
```

最小输入只有 `nodes` 与 `edges`。ID 可以是数字或字符串，边端点可以是 ID 或 `{ id }`；缺少 `distance` 时从 `startId` 自动补无向 BFS 距离。这样 Lean 华容道图、同形块商图、瓶颈压缩图和其他有限转换系统都走同一条坐标管线，棋盘字段只是可选的领域特化。

小于等于 1,400 个节点时，Worker 计算全部点对排斥。更大的图使用混合近似：多数轮次进行确定性的全局抽样排斥，每隔若干轮重建三维空间分箱，对空间近邻做更密的校正，再对远处节点抽样。这样保留“近处不能粘连、远处只需近似”的关键思想，同时避免在浏览器中逐轮扫描所有远格质心。它受上游 `GraphSpread.cu` 的近远场分离方法启发，但不是 CUDA `10 x 10 x 10` 实现的逐行移植。

边力使用视频工程中的单位方向非线性函数：太短的邻接边会排斥，太长的邻接边会吸引，但力的大小不会再额外乘以边长。这个单位化细节对保留长桥和宏观分支很重要。镜像检测根据棋盘尺寸、块尺寸和当前状态集合建立；只有镜像状态实际存在时才加约束。镜像力只作用于最终显示的三个坐标，不压扁第四维。最后返回平均边长、边长标准差、最长边、镜像配对数和镜像误差，供回归测试使用。

结构全览按 BFS 距离给边和普通节点着色，并随节点数增加缩小点半径，使细边和腰部通道不被固定大小的灰点覆盖。`3d-force-graph` 默认固定这些坐标，只负责 WebGL、相机、拾取和交互；“重新加热”才运行可选的 `d3-force-3d` 二次松弛。二次松弛可能把精心构造的宏观形状变成团块，因此它是实验工具，不是权威全览布局。

这里仍有两个明确边界：

1. 当前实验室 BFS 是编号敏感的精确图，尚未自动生成任意关卡的同形块商图；
2. 布局只用于观察。地标、坐标、镜像误差、颜色和屏幕中看见的“桥”都不是 Lean 命题。

### 2.3 网站的 112 步与本项目的 116 步

两边的 25,955 个状态键、964 个目标和 41,948 条无向边完全相同，差异只在起点：

```text
网站起点 key = 1;9;0,3,12,15;13,14,17,18
Lean classic  = 1;9;0,3,8,11;13,14,16,19
```

网站起点是 Lean 节点 40，离最近目标 112 步；Lean 的标准 `classic` 是节点 0，离最近目标 116 步。两者恰差四步：`soldier3 右`、`maChao 下`、`soldier4 左`、`huangZhong 下`。网站 README 说明其展示起点是作者最初见到的版本，与标准起点相差四步。

因此 112 与 116 不是规则、目标或 BFS 错误，而是任务初态不同。形式化陈述必须把 `start` 当作任务数据的一部分。

## 3. 经典商图的实际结构

运行 `npm run analyze` 对 Lean 导出的图重新计算，当前结果为：

| 量 | 结果 |
| --- | ---: |
| 商状态 | 25,955 |
| 有向边记录 | 83,896 |
| 去重无向边 | 41,948 |
| 反向边完整 | 是 |
| 连通分量 | 1 |
| 强连通分量 | 1 |
| 目标状态 | 964 |
| 从本项目经典初态到目标的距离范围 | 116 到 158 |
| 图论桥 | 1,468 |
| 割点 | 1,775 |
| 双连通块 | 1,790 |
| 最大双连通块 | 19,071 个节点 |

这些数字首先是探索结果，不等同于 Lean 内核定理。脚本用于发现候选结构；要称为“已形式证明”，必须让 Lean 检查相应分区、删边不可达或 Tarjan 证书。

### 3.1 为什么不能直接压缩 SCC

全部 83,896 条有向边都有反向边，整个经典可达图只有一个强连通分量。把 SCC 压缩会把 25,955 个节点全部变成一个点，无法表达视频中的“稠密区域与细颈”。

更合适的聚合是：

- **2-边连通块**：删去任意一条边仍相连的区域；商图形成桥树；
- **双连通块**：研究割点连接的循环区域；
- **小顶点割/小边割**：视频中的细线往往是一组边，不一定是单桥；
- **宏观观测量的纤维**：例如曹操与关羽的相对高度、空格分布、关键块所处区域；
- **近似社区**：可用于发现猜想，但必须另给精确边界和证书。

探索检查还显示：从初态到全部 964 个目标，没有除初态外的共同单点支配者。因此“所有解都经过同一个节点”不是正确猜想；“所有解都经过某个状态集合”才自然。

## 4. “华容道任务”应如何定义

通用任务已经采用：

```lean
structure PuzzleSpec where
  width   : Nat
  height  : Nat
  shapes  : Array Shape
  initial : State
  goal    : Goal
```

数学上可分为五层：

1. `ValidState spec s`：有限合法状态；
2. `Step spec s t`：一步转移；
3. `Reachable spec initial t`：初态所在可达分量；
4. `Solution spec`：携带路径和目标证明的解；
5. `Quotient` / `MacroState`：按标签对称、几何对称或结构区域聚合。

不要一开始给有限状态集合套普通点集拓扑。有限离散拓扑的开闭集理论通常平凡；视频中真正有内容的“拓扑”来自图的路径与环，以及独立移动生成的方形/立方复形。

## 5. 三种不同的商

### 5.1 同形标签商

经典华容道有四个同形竖块和四个同形小兵，标签群本质上是 `S4 x S4`。

`Huarongdao/Quotient.lean` 现在把合法状态收紧为：

```lean
abbrev ValidClassicState := { state : State // ValidState state }
abbrev ShapeState := Quotient sameShapeSetoid
```

`ShapeStep` 定义为具体一步关系在商上的**关系像**。具体路径一定能投影到它；反方向的逐代表提升还需要证明完整置换作用与 `tryMove` 等变，不能提前声称双模拟已完成。

### 5.2 几何对称商

水平镜像形成 `C2` 作用。它与标签商不同：标签置换不改变棋盘几何，镜像会产生另一个几何局面。若初态和目标在镜像下不变，可以进一步按镜像轨道取商；若任务本身不对称，只能得到两个任务间的图同构，不能直接合并节点。

### 5.3 宏观区域商

对任意 `classify : State -> Macro`，项目现在定义了 `MacroStep` 和 `MacroReachable`。具体路径总能投影，但抽象边采用存在代表语义，连续两条宏观边可能来自不相容的具体代表，因此宏观可达通常只是过近似。

要从宏观路径反推具体路径，需要证明双模拟：

```lean
forward  : Step s t -> MacroStep (classify s) (classify t)
backward : MacroStep q r -> classify s = q ->
  ∃ t, Step s t ∧ classify t = r
```

## 6. 桥、必经区与分隔证书

应区分：

- `bridge`：删去一条无向边会增加连通分量；
- `articulation point`：删去一个顶点会增加连通分量；
- `separator`：删去一组点/边，使指定初态与目标分开；
- `dominator/gate`：所有指定路径都必须访问的点或区域。

`Huarongdao/Bottleneck.lean` 已加入：

```lean
Path.states
Path.Visits
Path.UsesEdge
Path.UsesTransition
VertexSeparator
ProperVertexSeparator
EdgeSeparator
SolutionGate
```

`ProperVertexSeparator` 要求割集不包含起点和终点，避免把“初态本身”当作平凡瓶颈。

`GoalSeparatorCertificate` 用 `side : State -> Bool` 给状态标记两岸。只要证明初态与目标在不同岸，且每条跨岸合法边至少有一个端点在 `gate`，离散中间值定理就推出每条解都访问 `gate`。`ProperGoalSeparatorCertificate` 还排除起终点本身。

下一步应让可执行程序输出 `side`/`gate` 数组，再证明有限图 checker 的 soundness。Tarjan、最小割或人工观察负责发现候选，Lean 只检查局部边条件和图闭包。

## 7. “关羽必须放过曹操”如何形式化

### 7.1 已完成的第一层

项目已经定义动作敏感的 `CaoDownTransition`，并证明：

```lean
classic_solution_uses_cao_down_action :
  ∀ solution : Solution classic,
    solution.path.UsesTransition CaoDownTransition

classic_solutionGate_caoCanDescend :
  SolutionGate classic CaoCanDescend
```

证明思路：如果整条路径从未记录曹操向下动作，那么曹操纵坐标不会增加；但初态曹操 `y = 0`，所有目标曹操 `y = 3`，矛盾。

这已经证明“每个解都必须出现让曹操下移的局面”，但尚未把阻挡责任专门归因于关羽。

### 7.2 下一层：扫掠区与阻挡者

定义移动新增占据的格子：

```lean
SweepCells s p d :=
  (occupiedCellsAfterMove s p d).filter fun cell =>
    cell ∉ occupiedCells s p

BlocksMove s blocker mover d :=
  ∃ cell, cell ∈ occupiedCells s blocker ∧ cell ∈ SweepCells s mover d
```

目标定理：

```lean
tryMove s mover d = some t ->
  ∀ blocker, blocker ≠ mover -> ¬ BlocksMove s blocker mover d
```

取 `blocker = guanYu`、`mover = caoCao`、`d = down`，再与必有下降动作组合，就得到“某次曹操下降前，关羽已离开曹操扫掠区”。

### 7.3 更接近视频的相对高度势函数

为避免半整数中心，使用二倍行中心：

```text
center2(s,p) = 2 * y(s,p) + height(p)
delta(s) = center2(s,caoCao) - center2(s,guanYu)
```

经典初态 `delta < 0`；合法目标应满足 `delta > 0`。一步只移动一枚棋子一格，所以 `delta` 每步至多改变 2。离散中间值定理将推出每条解都经过 `delta` 接近 0 的“并排/交错”宏状态。这正对应视频源码的红、橙、黄、绿四阶段：

- [四阶段着色](https://github.com/2swap/swaptube/blob/b10f93640103c3ab5286c777a52b43d9085929de/src/Projects/Klotski.cpp#L1590-L1603)

## 8. Mathlib 能提供什么

当前项目没有 Mathlib 依赖，只使用 Lean/Std。Mathlib 有对应模块，但不应直接用一般判定器替代现有线性时间枚举。

| 任务 | Mathlib 模块 / API |
| --- | --- |
| 从关系构造简单图 | `Mathlib.Combinatorics.SimpleGraph.Basic`, `SimpleGraph.fromRel` |
| Walk、Path、Reachable、连通分量、桥 | `Connectivity.Connected` |
| 删除边后的必经边定理 | `Walk.mem_edges_of_not_reachable_deleteEdges` |
| 2-边连通关系 | `Connectivity.EdgeConnectivity`, `IsEdgeReachable` |
| 有限图、边集、邻居、度数 | `Connectivity.Finite`, `SimpleGraph.Finite` |
| 图距离 | `SimpleGraph.Metric`, `dist`, `edist` |
| 图映射、诱导子图、图同构 | `SimpleGraph.Maps`, `map`, `induce`, `G ≃g H` |
| 群作用轨道与稳定子 | `MulAction.orbit`, `orbitRel`, `stabilizer` |

Mathlib 4.33 的版本语义要特别注明：`G.IsBridge e` 本身不保证 `e` 是图中的真实边。枚举桥应写成：

```lean
e ∈ G.edgeSet ∧ G.IsBridge e
```

或从 `G.Adj u v` 出发。

推荐以后新增 `MathlibAdapter.lean`，把证书检查过的节点包装为 `Fin graph.states.size` 上的 `SimpleGraph`。算法仍由当前 BFS/Tarjan 层完成，Mathlib 用于一般定理、群作用和图同构。

## 9. 最能体现 Lean 优势的问题

按优先级建议：

1. **移动可逆性**：证明成功移动存在反方向移动，从语义上解释边为何成对；
2. **规范键完备性**：证明 `key` 相等当且仅当 `SameShape`；
3. **完整 `S4 x S4` 等变性**：证明标签置换与 `valid`、`tryMove`、`goal` 交换；
4. **商图双模拟**：具体路径与商路径相互提升，排除抽象伪路径；
5. **桥树证书**：按 2-边连通块聚合，证明跨块边恰为桥，商图是一棵树；
6. **关羽相对高度门区**：把视频四阶段着色变成所有解必经定理；
7. **完整 116 下界闭合**：把大图 true 证书封装为内核可消费的 `LowerBoundCertificate classic 116`；
8. **不可达岛守恒量**：为上游 898 个连通分量寻找奇偶性或排列不变量；
9. **最短解计数与对称轨道**：证明最短解是否唯一到镜像/标签对称；
10. **局部方形与立方复形**：独立移动交换时形成 4-环，多个自由度形成高维立方体；
11. **同调与环**：填充交换方形后研究剩余非平凡环，而不是只看力导向图片；
12. **抽象验证**：证明宏观阶段图与具体状态图之间的模拟/双模拟。

## 10. 推荐实施顺序

```text
P0  move reversibility
    -> key iff SameShape
    -> full relabel equivariance
    -> quotient bisimulation

P1  finite separator checker
    -> bridge / articulation / 2-edge-block certificates
    -> bridge tree
    -> relative-height gate theorem

P2  mirror group action
    -> orbit/stabilizer counting
    -> shortest solution counting
    -> commuting squares and cubical complex
```

验收边界应始终写清：布局用于发现；脚本统计用于复核；只有被 Lean 定理或 sound checker 接住的结论才称为形式证明。

## 11. 已实现的通用状态空间语义层

`Huarongdao/StateSpace.lean` 现在把“华容道任务”定义为带根、带目标谓词、带动作标签的转移系统：

```lean
structure StateSpace.Task (State Action) where
  initial : State
  goal    : State -> Prop
  step    : State -> Action -> State -> Prop
```

这里故意不把任务直接定义为无向简单图。原因有三点：

1. 同一对状态之间可能有不同动作见证；
2. 移动的可逆性应当是定理，而不是偷偷写进定义；
3. “曹操向下”“关羽离开扫掠区”等陈述依赖动作标签。

通用层已提供：

```lean
StateSpace.Task.Walk
StateSpace.Task.Reachable
StateSpace.Task.Vertex
StateSpace.Task.Solution
StateSpace.Task.Hom
StateSpace.Task.VertexSeparator
StateSpace.Task.SolutionGate
StateSpace.Task.GoalSeparatorCertificate
```

其中精确的根状态空间是：

```lean
{ state : State // task.Reachable task.initial state }
```

这一定义与 BFS 数组不同。BFS 数组只是它的一个有限表示；要证明数组完整，仍需闭包、初态包含、规范键唯一和边 soundness 证书。

### 11.1 观测商与双模拟商

通用层明确区分两个强度不同的商。

`Observation` 只要求：

```text
s ~ t -> (goal s <-> goal t)
```

因此目标谓词可以下降到等价类，并且具体路径总能投影为商路径。这已经足以做可靠的可视化聚合。

`BisimulationQuotient` 进一步要求：

```lean
s ~ s'
step s a t
-------------------------------
exists a' t', step s' a' t' and t ~ t'
```

这表示从等价类中的任意代表出发，都能匹配其他代表的一步。已证明的核心定理是：

```lean
BisimulationQuotient.liftStepFrom
BisimulationQuotient.liftWalkFrom
BisimulationQuotient.liftWalkWithLength
BisimulationQuotient.quotientReachable_iff
```

最后一个定理严格说明：

```text
商图从 [s] 可达 q
<->
存在真实状态 t，从 s 可达 t，并且 [t] = q
```

因此双模拟商不会产生由不兼容代表拼接出的伪路径。
`liftWalkWithLength` 还证明每条商边恰好提升为一条具体边，因此商图上的最短距离可以在完成双模拟实例后用于真实任务的长度证明。

### 11.2 经典同形商已经接入通用接口

`Huarongdao/Quotient.lean` 现在定义：

```lean
validClassicTask
shapeObservation
shapeStep_iff_observationStep
SameShapeStepLift
shapeBisimulation
```

当前完成程度是：

- `SameShape` 已经证明是合法的目标观测；
- 旧 `ShapeStep` 已证明恰好等于通用关系像商边；
- `SameShapeStepLift` 被单独暴露为剩余证明义务；
- 一旦完成该证明，`shapeBisimulation` 就能立刻获得全部商路径提升定理。

`SameShapeStepLift` 不应靠对 25,955 个节点暴力枚举来充当数学证明。推荐证明路线是：

```text
构造完整的 PieceRelabeling
-> occupiedCells 在重标号下等变
-> inBounds / noOverlap / valid 在重标号下不变
-> moveUnchecked 在重标号下等变
-> tryMove 在重标号下等变
-> 任意 SameShape 由一个保形重标号实现
-> SameShapeStepLift
```

### 11.3 通用门区证书

`GoalSeparatorCertificate` 已经从经典棋盘中抽象出来。它只需要：

```lean
side initial = false
goal target -> side target = true
每条跨岸合法一步的两个端点至少一个属于 gate
```

Lean 中的离散中间值定理随后证明：

```lean
GoalSeparatorCertificate.solutionGate :
  每一条完成任务的路径都访问 gate
```

这正适合形式化视频中的“从稠密区域穿过细颈到另一片区域”。Tarjan、最小割或三维图负责发现候选 `side` 和 `gate`；Lean 不信任布局，只检查全部一步转移的局部条件。

## 12. 从全览图到形式定理的研究工作流

以后每个视觉猜想都按以下六步处理：

```text
1. Lean / BFS 生成节点与合法边
2. 不受信任的布局器生成候选 x,y,z
3. Three.js / 3d-force-graph 显示结构并帮助提出猜想
4. 图算法发现候选桥、割点、门区或宏状态
5. 导出有限证书，而不是导出“算法说 true”
6. Lean 证明 checker soundness 并检查证书
7. 得到关于所有真实路径的定理
```

例如“必须经过一条桥”至少有三种精度不同的形式：

```text
全局桥：
  删除无向边 e 后，整张图的连通分量数增加

初态-目标分隔边：
  每条从 initial 到任意 goal 的路径都使用 e

门区：
  每条解都访问某个状态集合 gate
```

视频中肉眼看到的“细线”未必是单条全局桥，通常更可能是小边割或小顶点割。对经典图的探索已经发现 1,468 条全局桥，但没有除初态外被全部 964 个目标共同支配的单一节点，所以优先研究“必经状态集合”比猜一个万能节点更合理。

对于“关羽必须放过曹操”，项目现在已经形成以下定理链：

```text
曹操最终 y 坐标从 0 变成 3
-> 每条解包含曹操向下动作
-> 该动作的 SweepCells 在执行前没有被其他棋子占据
-> 特别地，关羽没有占据这些新增格
-> 每条解访问 GuanYuClearsCaoSweep 门区
```

对应 Lean 声明为：

```lean
SweepCells
BlocksSweep
successful_move_clears_sweep
GuanYuClearsCaoSweep
classic_solutionGate_guanYuClearsCaoSweep
```

这个结论的精度是：在某次曹操实际向下移动前，关羽不占据曹操此次移动新增覆盖的格子。它还没有声称“只有关羽是关键阻挡者”，也没有声称所有解经过同一个具体局面。

下一步叠加相对高度势函数，可以把视频的红、橙、黄、绿四阶段变成一个经过离散中间值定理验证的宏观阶段图。
