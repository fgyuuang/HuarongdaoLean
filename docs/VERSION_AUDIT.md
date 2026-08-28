# 华容道 Lean 4 项目版本架构与检查报告

> 审计基线：`main@300fe47`
> 审计日期：2026-08-28
> 目标：说明 Lean 4 形式化内核、Mathlib 接入、有限状态图证书、导出链、布局算法和浏览器交互之间的依赖与信任边界。

## 1. 执行摘要

当前版本已经形成一条可工作的“规则形式化 -> 状态空间抽象 -> 有限证书 -> 本地可视化”链路。

- Lean 4 工具链与 Mathlib 均固定在 `v4.33.1`。
- `lake build` 成功，43 个 Lean 源文件共约 9,536 行，未发现 `sorry`、`admit`、`axiom` 或 `unsafe`。
- Mathlib 分支提交 `38aa9e8` 已经并入 `main`；当前主分支包含 `SimpleGraph.Metric`、群作用轨道商和轨道-稳定子计数接口。
- 经典横刀立马的 116 步具体解及其全局最短性已经由 Lean 内核检查。
- 经典可视化维护同形商、水平镜像商和决策骨架三层本地数据；自定义关卡通过本地 HTTP 调用 Lean 求解器，再由 Web Worker 计算确定性坐标。
- 当前最重要的边界不是“路径是否合法”，而是“搜索结果是否附带足够证书”。通用 A* 只产生经独立重放验证的可行路径，不产生最短性证明；通用 BFS 的 `complete` 标记本身仍不是证明，但有限表示通过闭包与 BFS 距离证书后，可证明数组距离等于完整语义图距离。

版本结论：项目适合继续作为形式化状态空间研究平台使用，但前端需要更严格地区分“Lean 已证明”“Lean 已重放验证”“搜索器计算结论”和“纯可视化结果”。

## 2. 版本基线与依赖

| 项目 | 当前值 | 说明 |
|---|---:|---|
| Git 分支 | `main` | 跟踪 `origin/main` |
| Git 提交 | `300fe47` | 已合并 Mathlib 图与对称性分支 |
| Lean | `v4.33.1` | `lean-toolchain` |
| Mathlib | `v4.33.1` | `lakefile.toml` 固定 tag，manifest 固定 commit |
| Node 包 | `3d-force-graph@1.80.0` | 完整三维力导向视图 |
| Node 包 | `three@^0.179.1` | 自定义点线渲染、相机、拾取 |
| 本地服务 | `127.0.0.1:4173` | 静态文件与 `/api/puzzle/solve` |
| 经典同形商 | 25,955 状态 / 83,896 有向动作边 | 41,948 条无向可视连接 |
| 水平镜像商 | 13,011 状态 / 42,055 有向动作边 | 484 个目标类 |
| 决策骨架 | 10,429 锚点 / 36,774 有向宏边 | 抑制 2,582 个走廊内部节点 |

## 3. Lean 4 总体框架

[FIGURE:lean-architecture]

### 3.1 单一语义内核

`Huarongdao.StateSpace` 定义与具体棋盘无关的语义对象：

```lean
structure Task (State : Type u) (Action : Type v) where
  initial : State
  goal    : State -> Prop
  step    : State -> Action -> State -> Prop
```

`Task.Walk` 的每个 `cons` 都携带一个 `task.step` 证明，因此路径不是普通数组，而是动作序列及其逐步合法性的依赖类型证明。`Task.Reachable` 定义为存在一个 `Walk`；`Task.Solution` 再携带终点满足 `goal` 的证明。

这一设计把数学语义与 BFS/A* 数组实现分离。搜索器产生的 `StateGraph` 只是有限表示，不是状态空间本身。

### 3.2 经典规则层

经典规则由以下模块构成：

| 模块 | 责任 |
|---|---|
| `Huarongdao/Model.lean` | 棋子、坐标、形状、状态、占用格、合法性、`tryMove`、目标和规范键 |
| `Huarongdao/Transition.lean` | `Action`、`Step`、`Reachable`、合法性保持、`runMoves` |
| `Huarongdao/Paths.lean` | 兼容型 `Path`、`Solution`、执行重放与解见证 |
| `Huarongdao/StateSpace.lean` | 通用 `Task`、`Walk`、商、双模拟商、经典兼容桥 |
| `Huarongdao/StateSpaceKernel.lean` | 对外维护的经典/通用状态空间入口 |

经典 `State` 是十个带身份棋子的左上角坐标数组。`valid` 同时检查数组大小、边界和两两不重叠。`tryMove` 是唯一规则入口；所有路径、搜索边和证书最终都回到该函数。

### 3.3 通用关卡层

`SlidingPuzzle.PuzzleSpec` 把棋盘尺寸、编号矩形块、初态和部分目标约束参数化。通用模块与经典模块平行：

| 模块 | 责任 |
|---|---|
| `Generic/Model.lean` | `PuzzleSpec`、编号状态、目标、合法移动 |
| `Generic/StateSpace.lean` | `stateSpaceTask spec` 与兼容路径双向转换 |
| `Generic/Transition.lean` | 通用 `Step`、`Reachable` 及其与 Task 的等价 |
| `Generic/Search.lean` | BFS、A*、有限图、边 checker、解重放 |
| `Generic/Certificates.lean` | 闭包、不可达、下界和最短性证书 |
| `Generic/MathlibGraph.lean` | Mathlib `SimpleGraph`、距离和可达性桥 |

当前保留“兼容 Path/Solution API”和“统一 Task API”两套入口。二者已经证明双向互逆且保持动作与长度，但维护成本仍然存在。

## 4. 状态空间抽象塔

```text
raw : State
  | 兼容层，允许类型中出现非法数组
  v
concrete : { s : State // ValidState s }
  | 同形棋子标签置换 S4 x S4
  v
shape : ShapeState
  | 水平反射群 C2
  v
mirror : MirrorShapeState
  | 压缩非分岔走廊，宏边带 primitive weight
  v
corridor : CorridorState
```

### 4.1 从具体状态到同形商

`SameShape` 忽略四个竖块和四个小兵内部的标签。项目证明：

- `SameShape` 是等价关系；
- 目标谓词在等价类上保持；
- 任意 `SameShape` 都由实际 `PieceRelabeling` 实现；
- `tryMove` 对重标记等变；
- `shapeBisimulation` 可以从任意同形代表提升一步和整条路径，并保持长度。

这不是只用字符串 key 去重，而是具有代表无关性定理的精确商。

### 4.2 从同形商到水平镜像商

`HorizontalSymmetry` 有 `identity` 和 `reflection` 两个元素。`horizontalMirrorAction` 把状态和动作同时反射，并证明迁移与目标保持。`mirrorShapeBisimulation` 给出第二个长度保持精确商。

Mathlib 进一步提供：

- `Group HorizontalSymmetry`；
- `MulAction HorizontalSymmetry ShapeState`；
- 项目轨道关系与 `MulAction.orbitRel` 等价；
- `MirrorShapeState` 与 Mathlib 轨道空间等价；
- 轨道-稳定子公式；
- 对称状态轨道大小为 1，非对称状态轨道大小为 2。

### 4.3 决策骨架不是普通等价商

`corridor` 压缩的是路径中的强制非分岔段，不是把“相等状态”取商。锚点包括初态、目标和无向邻接度不等于 2 的节点。宏边保存：

- 源锚点与目标锚点；
- 完整父图节点路径；
- 每个原子步骤的一条可重放动作代表；
- 权重，即原子步骤数。

`corridorWalk_liftsToConcrete` 证明形式化宏路径可以展开到具体合法状态路径，且具体长度等于宏权重之和。

当前缺口：`checkCorridorExport_sound` 只把总 Bool 检查拆成多个 Bool 条件；它尚未把导出的数组重新构造成依赖类型 `CorridorSegmentation`。因此“数组通过 Lean checker”与“任意数组已经产生路径提升证明对象”之间仍缺一个反射桥。

## 5. Mathlib 接入评估

### 5.1 已使用模块

```lean
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.GroupTheory.GroupAction.Quotient
```

### 5.2 SimpleGraph 的实际作用

`Generic/MathlibGraph.lean` 在合法状态子类型上定义无向无环图：

```lean
def puzzleSimpleGraph (spec : PuzzleSpec) :
    SimpleGraph (PuzzleVertex spec)
```

合法移动的可逆性用于证明 `Adj` 对称；一步不能回到原状态用于证明 loopless。`legalMoves` 的 soundness/completeness 还给 `Adj` 提供了有限、可执行的 `DecidableRel`。项目路径可以转成 Mathlib Walk 且长度不变，由此获得：

- `SimpleGraph.dist <= Path.length`；
- 若候选路径长度等于 `dist`，则它在固定端点之间最短；
- 项目 `Reachable` 与 Mathlib `SimpleGraph.Reachable` 等价；
- Mathlib 的最短 walk 可以提升回带动作的项目路径。

### 5.3 已认证有限表示桥

`Generic/FiniteMathlibGraph.lean` 已实现第一阶段有限桥：

```lean
abbrev StateGraph.Vertex (graph : StateGraph) :=
  Fin graph.states.size

def FiniteGraphCertificate.finiteSimpleGraph :
    SimpleGraph graph.Vertex
```

`FiniteGraphCertificate` 记录根索引、根等于初态、所有数组状态合法以及状态数组无重复。由此构造：

- `vertexEmbedding : graph.Vertex ↪ PuzzleVertex spec`；
- `finiteSimpleGraph`，即完整语义图沿该嵌入的 `comap`；
- `isoInducedRange`，证明索引图同构于完整谜题图在数组状态集合上的诱导子图；
- 有限图邻接的 `DecidableRel`，可直接使用 Mathlib 的有限连通性与删边 API。

距离证明分为两个可复用层次：

1. `GraphMetric.RootedDistanceCertificate` 只要求根层级为零、每条边至多增加一层、每个非根点存在低一层前驱，并证明 `dist_eq_rank`。
2. `StateGraph.BfsDistanceCertificate` 将 `graph.distance` 包装为与状态数组等长的总距离表，再把上述局部条件实例化到有限语义图。

最终定理：

```lean
finiteSimpleGraph_dist_eq_arrayDistance
puzzleSimpleGraph_dist_eq_arrayDistance
```

第一条证明每个认证顶点的 BFS 数组距离等于有限诱导子图的 Mathlib `SimpleGraph.dist`。第二条组合 `checkClosedGraph_closed`、完整图 walk 的支持集提升和诱导子图同构，进一步证明：

```text
完整 puzzleSimpleGraph.dist
  = 有限 Fin 图 SimpleGraph.dist
  = graph.distance 数组值
```

因此闭包有限表示上的最短路径不会通过离开数组状态集而变短。`Generic/Examples.lean` 已用一个真实的两节点 BFS 输出验证有限距离和完整语义距离两条链，并由 Mathlib `IsBridge` 证明唯一转换边是桥。

此外新增：

- `GraphMetric.IsVertexPredicateCut`：删除满足某一状态谓词的所有顶点后，源点与目标点不再可达；
- `IsVertexPredicateCut.walk_hits`：每条源到目标的 walk 必须命中该谓词；
- `GraphMetric.IsMandatoryVertex`：单点割的必经点/支配点接口。

这使“关羽处于某个相对位置阶段”“曹操下降扫掠区已经清空”等状态谓词可以作为割集候选，而不必先压缩成一个手工命名节点。

### 5.4 Mathlib 尚未替代的部分

- 经典 25,955 节点有限数组仍使用项目自定义 `Graph`，不是 `SimpleGraph` 的有限枚举实例。
- BFS/A*、HashMap 去重、父指针和 JSON 导出仍是项目代码。
- 图闭包、商代表和距离势函数证书仍使用项目结构；当前有限桥面向通用精确 `StateGraph`，不是经典同形商 `Graph`。
- `BfsDistanceCertificate` 目前是证明接口，尚未有适合 25,955 节点文件的自动化 checker/证书构造器。
- Mathlib 已可直接处理有限图的桥与连通分量；割点、块割树、支配关系和走廊压缩仍需项目层定义及 soundness 定理。

推荐方向：为经典 `Graph.CertificateEdge` 建立同形商 `SimpleGraph`，证明其与现有 `QStep`/双模拟一致；随后实现可执行的有限证书 checker，把已经完成的通用闭包距离定理应用到 25,955 节点经典商图。

## 6. 搜索、证书与最短性

### 6.1 经典 BFS

`Huarongdao.Search.enumerateByKey` 从初态进行无上限 BFS。使用 `State.key` 时得到同形商代表；使用 `mirrorKey` 时得到镜像商代表。经典最短性不是只信任 BFS 队列，而是通过 `checkQuotientLowerBound` 重新检查：

- 图非空且根代表初态；
- 根势函数值为 0；
- 每个合法后继在商图中有可提升的表示；
- 势函数沿每步最多增加 1；
- 每个目标代表的势函数至少为 116。

`classicQuotientLowerBound_checked` 使用 `native_decide` 证明该有限检查为 true，随后 `classic116Play_minimal` 把 116 步上界与 116 步下界结合，得到全局最短性。

### 6.2 通用 BFS

通用 BFS 使用精确编号状态 key，继续展开直到队列耗尽或达到资源上限。它计算的第一条目标路径具有 BFS 层序意义，但当前源码没有形式证明队列不变量。

`StateGraph.checkClosedGraph` 提供独立闭包 checker，并有：

```lean
checkClosedGraph_sound :
  graph.checkClosedGraph spec = true ->
  forall state, Reachable spec spec.initial state ->
    state ∈ graph.states.toList
```

再结合 `checkNoGoal` 可证明不存在可达目标。但 `GenericMain.resultJson` 当前没有调用这两个 checker，因此 API 的 `status = unreachable` 仍是搜索器结论，不是已导出的内核不可达证书。

### 6.3 通用 A*

当前优先级为：

```lean
cost + goalManhattan spec state * 8
```

这是加权启发式，不保证可采纳；此外 `State.symmetryKey` 会把形状和目标约束相同的编号块合并用于运行时去重，但尚未证明相应商的路径提升。A* 找到的动作列表会由 `checkSolution` 从初态独立重放，因此：

- 可以证明“这条路径合法且到达目标”；
- 不能由现有定理证明“这是最短路径”；
- 不能由现有定理证明“未找到即不可达”。

`LowerBoundCertificate` 是正确的最短性接口。只要给出与候选长度相同的下界证书，`shortest_of_verified_path_and_lower_bound` 就能证明全局最短。

## 7. 形式化保证矩阵

| 声明 | 当前状态 | 证明/检查入口 |
|---|---|---|
| 成功移动保持合法性 | Lean 已证明 | `tryMove_preserves_validity` |
| 路径逐步合法 | Lean 类型保证 | `Path.cons` / `Task.Walk.cons` |
| 返回动作到达目标 | Lean 重放验证 | `checkSolution_sound` |
| 通用存储边合法 | Lean checker soundness | `StateGraph.checkEdge_sound` |
| 通用所有可达状态均在节点数组 | 有接口，API 未调用 | `checkClosedGraph_sound` |
| 通用不可达 | 有接口，API 未导出证书 | `no_reachable_goal_of_closed_graph` |
| A* 候选最短 | 未证明 | `kernelProved = false` |
| BFS 队列算法完备 | 未证明 | 需闭包 checker 替代信任 |
| 经典同形商精确 | Lean 已证明 | `shapeBisimulation` |
| 经典镜像商精确 | Lean 已证明 | `mirrorShapeBisimulation` |
| 经典 116 步全局最短 | Lean 已证明 | `classic116Play_minimal` |
| corridor 形式化宏路径可展开 | Lean 已证明 | `corridorWalk_liftsToConcrete` |
| 导出 corridor 数组构造依赖型分段对象 | 未完成 | 当前仅 Bool checker |
| Worker 坐标确定性 | JS 回归测试 | `check-layout.mjs` |
| 坐标反映图的数学不变量 | 不声明 | 纯可视化 |

## 8. 导出与本地运行链

[FIGURE:runtime-pipeline]

### 8.1 经典模式

```text
Lean enumerate / enumerateMirror / buildCorridorExport
  -> graph.json / graph.mirror.json / graph.corridor.json
  -> 参考坐标映射与父层坐标子集
  -> layout.json / layout.mirror.json / layout.corridor.json
  -> 浏览器读取本地 JSON
  -> Three.js 或 3d-force-graph 渲染
```

`layout.json` 的经典坐标由 `import-reference-layout.mjs` 按规范 key 映射自 2swap/Klotski-Webpage 的预计算坐标。镜像布局取镜像配对两端的中点；决策骨架布局选取镜像父层锚点坐标。Python 脚本不生成 Lean 图，也不改变状态、边或权重。

### 8.2 关卡实验室

```text
浏览器编辑 PuzzleSpec
  -> POST /api/puzzle/solve
  -> Node 参数检查
  -> .lake/build/bin/solve-puzzle.exe
  -> Lean BFS / A*
  -> JSON: validation + stats + graph + solution + proof
  -> Web Worker 结构布局
  -> Three.js / 3d-force-graph
  -> 点击、路径规划和逐边播放
```

全部发生在本机。`127.0.0.1` 是回环地址，不是在线渲染服务。

## 9. 确定性状态图布局

自定义关卡不是直接把 `3d-force-graph` 从随机位置放开。主布局由 `structural-layout-worker.js` 预计算，再交给渲染器。

### 9.1 输入标准化

`state-space-visualization.js` 接受一般有限图：

- `nodes` 或 `states`；
- `edges` 或 `links`；
- 数字或字符串节点 ID；
- 数字端点或 `{ id }` 端点；
- 可选 `startId`、`distance`、`board`、`shapes` 和棋盘位置。

它建立 ID 索引、有向入边/出边、无向 BFS 距离、固定坐标 `fx/fy/fz` 和点击 payload。

### 9.2 初始四维坐标

布局器先把有向重复边合并为无向可视边，再执行：

1. 从起点开始选择最远点地标，共最多 5 个。
2. 计算各节点到地标的 BFS 距离。
3. 用距离差构造四维初始坐标。
4. 用棋盘状态特征和确定性伪随机扰动打破重合。
5. 按 BFS 深度把新节点向已放置父节点附近收缩。
6. 归一化各维并调整平均边长。

### 9.3 对称约束

若输入包含棋盘尺寸、块形状和每个状态的块位置，Worker 会查找水平/垂直镜像配对。配对节点在相应轴上取相反坐标，其他可视维度取平均，并在松弛阶段继续施加弱镜像修正。

这是布局约束，不是状态商证明。目标约束是否在镜像下保持仍由 Lean 的任务对称性理论决定。

### 9.4 四维松弛与投影

布局分三阶段：

| 阶段 | 维数参数 | 作用 |
|---|---:|---|
| `4D spread` | 3.98 | 边吸引、节点排斥、弱镜像约束 |
| `4D -> 3D` | 3.95 | 继续松弛并逐步衰减第四维 |
| `3D projection` | 3.00 | 清零第四维并统一三维平均边长 |

小图使用精确两两排斥；大图交替使用空间分箱局部排斥和确定性远点采样。迭代次数随节点数下降，以控制浏览器成本。回归测试检查坐标有限、重复运行逐值相同、镜像误差和边长统计。

### 9.5 3d-force-graph 的角色

- “结构全览”由自定义 Three.js 点线渲染器直接显示预计算坐标。
- “3D 松弛”把相同坐标写入 `fx/fy/fz`，默认固定。
- 用户点击“重新加热”后才释放固定坐标，运行 `d3-force-3d` 二次松弛。
- “恢复结构”重新写入 Worker 或经典参考坐标。

因此图形之所以稳定且有整体结构，主要来自预计算坐标和分层结构初始化；`3d-force-graph` 主要负责 WebGL 绘制、相机、拾取以及可选二次松弛。

## 10. 前端交互链

### 10.1 经典棋盘

1. `loadGraph` 读取选中层的 graph/layout JSON。
2. `outgoing` 保存原始有向动作边。
3. `renderState` 更新棋盘、历史、计步、图标记和证明轨迹。
4. 手动移动只在当前节点的 `outgoing` 中匹配棋子和方向。
5. 提示和导航在已加载图上做 BFS 路径规划。
6. 路径动画逐条调用已有边，不直接跳转状态。
7. corridor 宏边通过 `steps` 展开为父镜像图的原子动作。

### 10.2 关卡实验室

1. 编辑器构造 JSON 规格并钳制资源上限。
2. Node 服务再次严格检查整数范围和块编号。
3. Lean 返回图后，临时 BFS 生长坐标立即可见。
4. Worker 完成后替换为确定性 4D -> 3D 坐标。
5. 手动拖动、方向键、提示和路径播放都只使用返回图中的有向边。
6. `GraphPath` 文本根据已走边生成，但浏览器不重新编译该证明项。

### 10.3 点击接口

`createNodeClickHandler` 返回的 payload 包含节点 ID、坐标、原始数据、入边、出边和邻居。当前经典和实验室页面各自实现了相机定位、路径端点选择和逐边播放；通用适配层已经具备后续插件化所需的点击接口。

## 11. 风险与技术债

### 11.1 高优先级：通用不可达显示超过当前证书边界

`GenericMain` 没有在 BFS 完成时调用 `checkClosedGraph` 和 `checkNoGoal`，但前端会显示“完整状态图中不可达”，证明面板还写有“BFS 完整闭包未发现目标”。这在算法工程上通常正确，但不符合项目希望达到的内核证书表述。

建议：

- API 增加 `proof.closedVerified` 和 `proof.noGoalVerified`；
- 仅当两者为 true 时显示“Lean 已证明不可达”；
- 否则显示“BFS 枚举结束，搜索器未发现目标”。

### 11.2 高优先级：A* 长度被命名为“最短步数”

JSON 字段名为 `shortestLength`，界面标签也是“最短步数”。当前 A* 使用加权曼哈顿启发式，且对称 key 去重没有商提升定理，不能保证最短。

建议：

- API 改为 `pathLength`；
- A* 显示“候选路径长度”；
- BFS 可显示“BFS 首次目标层长度（算法计算）”；
- 只有持有 `LowerBoundCertificate` 或 Mathlib 距离等式时显示“Lean 已证明最短”。

### 11.3 中优先级：经典“实时证明”是证明骨架

经典页面基于 Lean 导出边和 JS 位置比较生成 `Path/QPath` 文本。生成代码仍包含 `edge*_executed` 等占位证明，并未在浏览器内送入 Lean 编译。

建议把界面文案统一为“证明轨迹”或“可导出的证明骨架”，并在真正完成服务端证书重放后再使用“实时 Lean 验证”。

### 11.4 中优先级：A* 对称去重缺少形式化商

当两个不同编号状态具有相同 `symmetryKey` 时，A* 只保留第一个精确状态；若新状态不与该代表完全相等，其边不会写入搜索图。返回路径仍可重放验证，但搜索可能漏掉只从另一代表可达的分支。

建议为“同形状且同目标约束”的编号块置换建立通用群作用与 `BisimulationQuotient`，或在没有证明时关闭该剪枝的完备性声明。

### 11.5 中优先级：Three.js 运行时重复

页面模块直接加载 `three.module.min.js`，同时全局 `3d-force-graph.min.js` 包含自己的 Three.js 运行时。浏览器会报告多个 Three.js 实例。当前交互可用，但增加内存并可能引入跨实例对象不兼容。

建议统一依赖加载方式：使用同一 ESM 构建链，让 `3d-force-graph` 与自定义渲染器共享 `three`。

### 11.6 中优先级：corridor 数组与依赖证明对象之间缺桥

数学层的 `CorridorMacroStep`、`CorridorSegmentation` 和路径提升定理完整；导出层的 `CorridorExport` 是普通数组。当前 checker 证明检查条件为 true，但没有构造对应依赖对象。

建议定义经过检查的 `VerifiedCorridorExport`，把每条数组宏边反射为 `CorridorMacroStep`，再给出整图覆盖定理。

### 11.7 低优先级：模块和前端体量

- `StateSpace.lean`、`Relabeling.lean`、`Search.lean` 已超过 600 行。
- `frontend/app.js` 约 1,527 行，`laboratory.js` 约 627 行。
- 经典/通用兼容路径 API 与统一 Task API 并存。

建议按“语义、有限表示、证书、导出、视图控制器、渲染适配器”拆分，但不要在证明边界尚未稳定时做大规模重构。

## 12. 推荐研究路线

1. 完成通用 BFS 闭包证书的 API 接入，把“搜索器不可达”升级为“Lean 证明不可达”。
2. 把通用编号块对称性定义为保形且保目标约束的有限置换群，构造轨道商与双模拟。
3. 将已经完成的通用 `StateGraph -> SimpleGraph` 有限桥推广到经典同形商 `Graph`，并补闭包距离保持定理。
4. 从全图 checker 自动构造 `BfsDistanceCertificate` 与 `GoalSeparatorCertificate`，在经典图上核验割集、桥、支配点和必经门区。
5. 把“关羽必须放过曹操”从当前扫掠区门谓词推进到更精细的相对位置/占用区分类定理。
6. 为二度走廊、双连通分量或块割树定义可证明的压缩，区分长度保持压缩与仅保持可达性的宏观商。
7. 将布局统计明确定位为实验观测；若研究结构，需要另定义可证明的图不变量，如度分布、距离层、割点和轨道大小。

## 13. 版本验收清单

### Lean 与证书

- `lake build`
- 搜索 Lean 源码确认无 `sorry/admit/axiom/unsafe`
- `lake exe check-certificate`
- 核对 Mathlib tag、manifest commit 和 Lean toolchain 一致
- 核对经典、镜像、corridor 状态数和边数

### 前端与数据

- `npm run check:generic`
- `npm run check:layout`
- `npm run check:state-spaces`
- `node --check` 检查四个前端/服务脚本
- 浏览器检查经典三层、实验室 BFS/A*、点击、路径播放、坐标恢复和控制台

### 证明边界

- 不把 `edgesVerified` 解释为边完备
- 不把 `graph.complete` 单独解释为内核闭包证书
- 不把 A* 候选路径解释为最短路径
- 不把预计算坐标或力导向稳定形状解释为图论定理
- 不把前端生成的 Lean 代码骨架解释为已编译证明

## 14. 本次检查结果

| 检查项 | 结果 |
|---|---|
| `lake build` | 通过 |
| Lean 源码未完成证明标记扫描 | 通过，未发现目标标记 |
| Mathlib 分支是否并入主分支 | 通过，`38aa9e8` 是 `main` 祖先 |
| 通用布局确定性与镜像误差测试 | 通过 |
| 三层本地 JSON 一致性与 corridor 展开路径 | 通过 |
| 经典证书 checker | 通过 |
| 浏览器主流程 | 可用 |
| 浏览器控制台 | 有一个 Three.js 多实例告警 |

## 15. 关键入口

| 入口 | 用途 |
|---|---|
| `Huarongdao/StateSpaceKernel.lean` | 形式化研究的公共状态空间 API |
| `Huarongdao/StateSpaceAnalysis.lean` | 任务多态有限状态空间、距离证书与割集接口 |
| `Huarongdao/StateSpaceBfs.lean` | concrete/shape/mirror 共用的表示多态 BFS |
| `Huarongdao/Generic/MathlibGraph.lean` | Mathlib 图距离与可达性 |
| `Huarongdao/Generic/FiniteMathlibGraph.lean` | 有限诱导子图、闭包距离、BFS 数组距离、谓词割集 |
| `Huarongdao/MathlibSymmetry.lean` | 群作用、轨道商、稳定子 |
| `Huarongdao/Generic/Certificates.lean` | 闭包、不可达、下界、最短性 |
| `Huarongdao/Bottleneck.lean` | 割集、门区和“关羽让路” |
| `ExportMain.lean` | 经典三层图导出 |
| `GenericMain.lean` | 通用求解 JSON 边界 |
| `frontend/structural-layout-worker.js` | 确定性 4D -> 3D 布局 |
| `frontend/state-space-visualization.js` | 通用状态图适配与点击接口 |
| `frontend/app.js` | 经典三层渲染与交互 |
| `frontend/laboratory.js` | 自定义关卡编辑、求解、布局和探索 |
