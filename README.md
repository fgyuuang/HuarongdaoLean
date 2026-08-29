# 基于 Lean 4 的有限滑块谜题实验室

本项目的正式研究名称是**基于 Lean 4 的华容道有限状态空间与离散几何形式化研究**。核心问题是：华容道的合法滑动、可达性、对称商、最短解和关键门区能否被 Lean 4 严格证明。

> 新队友安装、旧版本迁移和 Git 协作流程见 [`TEAM_START.md`](TEAM_START.md)。

本项目从经典“横刀立马”华容道出发，将合法局面与一步移动定义为有限状态转移系统，并进一步抽象为支持任意有限矩形棋盘、编号矩形木块、给定初态和位置目标的通用滑块谜题形式系统。经典模式保留完整 25,955 节点商图；关卡实验室通过 HTTP 调用 Lean 通用 BFS 或 A*，并独立重放返回路径以构造解的存在性证明。

## 版本审计

当前版本架构、证明边界、Mathlib 接入、状态图导出、确定性布局和前端交互的完整检查见：

- [`docs/VERSION_AUDIT.md`](docs/VERSION_AUDIT.md)：可 diff、可持续维护的审计源。
- [`docs/HuarongdaoLean-Version-Audit-2026-08-28.docx`](docs/HuarongdaoLean-Version-Audit-2026-08-28.docx)：`main@300fe47` 的 Word 版本检查快照。

本次审计确认 `lake build` 通过，Lean 源码未发现 `sorry`、`admit`、`axiom` 或 `unsafe`，Mathlib 图论/群作用分支已经并入主分支。维护时必须继续区分以下四层：

```text
Lean 定理
  -> Lean 可执行 checker
  -> JavaScript 搜索/布局/路径规划
  -> Three.js / 3d-force-graph 展示
```

当前通用 A* 只保证候选动作能由 `checkSolution` 重放为合法解，不保证最短；通用 BFS 的 `complete` 是搜索器运行标记，只有进一步通过 `checkClosedGraph` 与 `checkNoGoal` 才能形成内核不可达证书；经典页面生成的是基于已导出边的证明轨迹/代码骨架，不是在浏览器中重新编译 Lean。

当前 Lean 形式化成果、证明链、证据层级和 `Fintype.card ContinuousClass = 898` 的最终证明目标，集中见 [`docs/FORMALIZATION_OVERVIEW.md`](docs/FORMALIZATION_OVERVIEW.md)。

## 已完成内容

- 棋子、形状、坐标、占用格、边界与不重叠条件
- 可计算的合法移动函数 `tryMove` 与一步关系 `Step`
- 自反传递可达关系 `Reachable`
- 经典初始布局合法性证明
- 成功移动保持合法性、一步保持合法性、可达状态保持合法性证明
- Lean 内实现的 BFS 状态图枚举与 JSON 导出
- 同形棋子标签置换下的规范键，即对称作用的商状态图
- 完整三维状态图：25,955 个节点和 41,948 条无向连接
- 参考全览、`3d-force-graph` 完整力导向、局部探索三种模式
- 曹操位置追踪、同组状态筛选，以及精确位置/镜像位置轨道投影
- 当前状态定位、深度缩放、起终点选择和逐边 Lean 合法路径动画
- 前端实时显示 `ValidState`、`goal` 和转换来源，并可查看已编译的定理
- 到达出口时显示完成节点、玩家步数、BFS 距离和路径验证类别
- `Path`、`Solution` 与 `CertifiedPlay`：玩家通关动作列表可以直接成为证明见证
- `mem_legalMoves_iff`：合法动作枚举的可靠性与完备性
- 116 步具体通关动作由 Lean 内核计算检查
- `SameShape` 商等价、同形棋子换位、左右镜像基础与抽象 `GameSymmetry`
- 同形标签商的完整 `SameShapeStepLift` 与长度保持路径提升
- 同形商上的水平镜像双模拟商，以及可展开的决策骨架加权状态空间
- 统一 `StateSpace.Task` 内核、可组合投影同态和四层端到端具体路径提升
- 图证书检查器验证商边、闭包、唯一代表、距离约束和目标下界
- `classic116Play_minimal` 与 `ClassicStateSpaceKernel.concreteSolution_lower_bound` 将有限证书接入统一状态空间内核
- 局部拓扑分析基础：节点度、二阶邻域、交换方形、Link 连通分支、局部维数与瓶颈候选
- `SymmetryShortestPath` 将定长路径、定长解和最短解长度提升为任务级接口，并证明 `concrete → shape → mirror` 两层双模拟商完整保持原子步最短距离
- `StateSpaceAnalysis` 将完整状态/边枚举、BFS 距离数组、割集与 Mathlib 桥统一参数化于 `StateSpace.Task`；各层通过 `Task.Hom` 和双模拟商连接，并证明商距离等于某个投影纤维代表的细层距离
- `StateSpaceBfs` 提供单一的表示多态 BFS 引擎；`concretePresentation`、`shapePresentation`、`mirrorPresentation` 只替换语义投影与规范键，共用相同的队列、边表和距离数组生成过程
- `StateSpaceConnectivity` 证明可逆任务上的 `Reachable` 是合法移动生成的最小等价关系，定义可达分支商与一步不变量，并给出它与 Mathlib `SimpleGraph.ConnectedComponent` 的典范等价

可达性、组合连续性、对称商与可达商的严格区别，以及“关公必须让路”应如何写成割集定理，见 [`docs/REACHABILITY_AND_CONTINUITY.md`](docs/REACHABILITY_AND_CONTINUITY.md)。

经典形状全集的构造枚举、`65,880` 个合法同形布局、`898` 个 DFS 分量摘要、Klein 四元群下 `230` 个分量轨道，以及 `EnumerationComplete` 到有限数组覆盖的证明桥，见 [`docs/FULL_SHAPE_SPACE.md`](docs/FULL_SHAPE_SPACE.md)。本地启动后可从顶部“全空间预览”进入 [`frontend/full-space.html`](frontend/full-space.html)：一个节点代表一个连续分量，左右/上下/旋转连线只表示离散图同构，不表示合法滑动。全空间计算与重证书被隔离在 `ClassicFullSpace` / `ClassicFullSpaceCertificate`，不拖入默认构建。

全空间节点现在可以直接成为关卡实验室的初态来源。点击节点会显示该分量的确定性代表棋盘；点击“接入当前任务”后，页面通过 `?mode=lab&fullSpaceComponent=<id>` 载入经典 `4×5` 形状组和曹操目标 `(1,3)`，可继续验证、A* 求解或 BFS 枚举。分量代表是全空间枚举的规范初态，不等同于传统“横刀立马”初态；分量 `#15` 才与传统初态处于同一连续等价类。

交换方形在 Lean 中由 `ActionsCommuteAt` / `SquareAt` 定义：从同一状态执行两个不同动作时，两种执行顺序到达同一状态。`checkActionsCommuteAt_sound` 把可执行检查器的成功结果连接到这个命题，`actionsCommuteAt_steps` 则给出方形四条边对应的 `Step` 见证。当前 JavaScript 模块用于离线计算和筛选候选局部子图，不介入主状态图的可视化。

经离线筛选，前端“拓扑样本”独立展示同形商节点 `#1409` 的半径 2 诱导子图。该样本包含 18 个节点、23 条无向边和 4 个交换方形；移除中心后分成 2 个连通分支，因而同时展示了由动作交换产生的二维胞腔和局部切分现象。

该样本的正式研究结果、Lean 定理与计算证书边界见 [`LOCAL_TOPOLOGY_RESEARCH.md`](LOCAL_TOPOLOGY_RESEARCH.md)。

## 关卡实验室

页面顶部可切换“经典华容道 / 关卡实验室”。实验室支持自定义棋盘宽高、编号块尺寸、部分或完整位置目标、搜索资源上限、解路径回放和 Lean 证明链。初态棋盘和目标棋盘都支持拖动：拖动初态块修改初始坐标；先在编号块行勾选“已约束”，再拖动目标棋盘中的虚线块修改目标坐标。棋盘的每个真正空格会在悬停时显示“+”，点击直接新增一个 1×1 编号块；目标棋盘新增时会自动寻找初态空格并同时建立目标约束。每个块的右下角有拉伸手柄，按棋盘格改变矩形宽高；形状属于 PuzzleSpec，因此初态和目标视图同步更新，并清除旧状态图。取消勾选会删除该块的目标约束。未指定目标的块不受终局位置约束；至少必须指定一个目标。

通用规格为：

```lean
structure PuzzleSpec where
  width   : Nat
  height  : Nat
  shapes  : Array Shape
  initial : State
  goal    : Goal
```

`wellFormed` 检查棋盘/形状非零、数组长度、初态边界与不重叠、至少一个目标约束，以及目标坐标边界。`Step`、`Reachable`、`Path` 和 `Solution` 全部以 `PuzzleSpec` 为参数。搜索采用编号敏感的精确状态，不会自动交换同尺寸块的编号。

完整证明链：

```text
PuzzleSpec
  → wellFormed spec = true
  → search spec config
  → result.actions
  → checkSolution spec result.actions = true
  → Solves spec result.actions
  → Path.ofRunMoves
  → Nonempty (Solution spec)
```

关键内核定理：

```lean
checkSolution_iff :
  checkSolution spec actions = true ↔ Solves spec actions

verified_search_implies_exists :
  result.verified spec = true → Nonempty (Solution spec)

verified_search_exhibits_reachable_goal :
  result.verified spec = true →
    ∃ target, Reachable spec spec.initial target ∧ goalMatches spec target = true

StateGraph.checkClosedGraph_sound :
  graph.checkClosedGraph spec = true →
  ∀ state, Reachable spec spec.initial state →
    state ∈ graph.states.toList

shortest_of_verified_path_and_lower_bound :
  VerifiedPath spec actions →
  LowerBoundCertificate spec actions.length →
  IsShortestSolution spec actions
```

### 通用状态图探索

通用 BFS 不会在发现第一个目标后立刻停止，而会继续枚举精确编号状态，直到队列耗尽或触发资源限制。它返回：

```lean
structure GraphEdge where
  source : Nat
  target : Nat
  action : Action

structure StateGraph where
  states    : Array State
  distance  : Array Nat
  edges     : Array GraphEdge
  expanded  : Nat
  generated : Nat
  complete  : Bool
```

关卡实验室的生成与渲染链完全在本机完成：

```text
浏览器编辑 PuzzleSpec
  → POST http://127.0.0.1:4173/api/puzzle/solve
  → 本地 Node 服务启动 .lake/build/bin/solve-puzzle.exe
  → Lean 解析规格并执行 BFS / A*
  → JSON 返回状态、距离、目标标记和带动作的有向边
  → 浏览器 Web Worker 计算确定性的结构坐标
      → 图距离地标初始化与 BFS 父节点附近生长
      → 四维非线性吸引/排斥与镜像约束
      → 3.98 → 3.95 → 3D 投影
  → Three.js / 3d-force-graph 在本地 WebGL 画布渲染
```

`127.0.0.1` 是只指向本机的回环地址，不是云端渲染服务。页面、求解器、布局 Worker、`3d-force-graph` 运行时和图数据都来自项目目录；断开互联网后，只要依赖已经安装且项目已构建，关卡实验室仍可生成和显示状态图。经典模式的 `layout.json` 是构建前已经持久化的参考坐标；自定义关卡则在 Lean 返回图以后，由本地浏览器 Worker 计算坐标并保存在当前页面内存中。

全拼法总览同样完全在本地运行。`FullSpaceMain.lean` 将 65,880 个合法拼法的 DFS 摘要和分量对称像导出到 `frontend/full-shape-components.json`；`full-space.js` 先把 898 个连续分量按左右镜像、上下镜像和 180° 旋转归为 230 个 Klein 轨道，再用确定性的群槽位和螺旋轨道中心计算坐标。这个页面不运行随机力导向，刷新后坐标保持一致。

经典模式提供三个彼此独立、可相互恢复的状态空间：

- **同形商**：直接读取 Lean 导出的 `graph.json` 与参考 `layout.json`，包含 25,955 个 `ShapeState` 代表。
- **镜像商**：读取 Lean 生成的 `graph.mirror.json` 与脚本生成的 `layout.mirror.json`，包含 13,011 个镜像类。保留“展开 / 合并 / 100%”滑块，使用每个镜像类的两端坐标和中点坐标连续展示 `25,955 → 13,011` 的投影。
- **决策骨架**：读取 Lean 生成并检查过的 `graph.corridor.json` 与脚本生成的 `layout.corridor.json`，只显示初始、目标与分岔关键节点。连续的二度中间状态不绘制，只保存在宏边的展开路径中；普通单步边为灰色，确实归并多个底层步骤的边为蓝色，宏边两端用金色点突出显示。每条宏边保存完整镜像商节点路径、一条可重放的原子动作代表链和权重，可展开回父状态空间；同一有向端点若有多个动作标签，corridor 只保留一个代表，镜像层仍保留并认证全部动作边。

三层分类沿用协作审查中形成的结构，但将原“强制走廊”按作用命名为“决策骨架”。镜像图的代表元和带动作边完整性由 Lean 负责；corridor 由 Lean 自动按无标签有向端点邻接分段，并为每个邻接保留一个可重放动作代表。Python 只选取既有坐标、计算镜像中点并写布局文件。各层节点位置、镜像中点、展开动画和骨架关键节点全部使用本地项目已经生成并验收的坐标文件。

实验室提供三种视图：

- **结构全览**：固定使用 Worker 生成的确定性 `4D → 3D` 坐标，并按距初态的 BFS 距离给节点和边着色。全览采用细边主导的绘制策略；普通节点随图规模缩小，起点、当前点、目标和证明路径单独突出，避免大图被节点球遮住。
- **3D 松弛**：`3d-force-graph` 使用同一批结构坐标作为固定的 `fx/fy/fz`；它默认负责 WebGL 绘制、拾取、相机和交互。只有点击“重新加热”后才释放坐标并运行有限的 `d3-force-3d` 二次松弛；“恢复结构”精确返回 Worker 坐标。
- **局部探索**：只显示已经走过的节点及当前状态的一步后继，并使用轻量的局部弹簧/排斥布局。

为了画线，前端会把正反方向重复边合并成一条无向可视连接；Lean 返回的原始有向边、棋子编号和移动方向不会被删除，棋盘移动、路径选择与动画始终使用这些带动作的边。点击节点只选择路径端点，不会直接跳转状态。当前状态棋盘支持选择或拖动编号块、方向按钮、方向键、撤回、复位和提示一步；每次成功移动都会新增一个由已检查边构造的 `GraphPath.cons`。

布局器本身不依赖华容道规则。最小输入只需要节点与边，节点 ID 可以是数字或字符串，边端点也可以直接写 ID 或 `{ id }`；`startId` 可指定布局地标的起点。未提供 `distance` 时，Worker 会在可视无向图上自动计算起点 BFS 距离。只有同时提供 `board`、`shapes` 和每个节点的 `positions` 时，才启用华容道水平/垂直镜像配对。因此同一个模块也可以显示其他有限状态机、商图或由 Lean 导出的任意有限图。

每条 JSON 边由 `StateGraph.checkEdge` 独立重放，并由以下定理连接到通用移动语义：

```lean
StateGraph.checkEdge_sound
StateGraph.checkEdges_sound
GraphPath.toReachable :
  GraphPath spec graph source target → Reachable spec source target
```

只有 **BFS 图枚举**旨在生成整个可达状态图。`graph.complete = true` 表示本次可执行 BFS 没有触发上限并耗尽队列；`graph.complete = false` 且 `graph.truncated = true` 时，界面显示“资源截断子图”，仍可探索已返回部分，但不能声称目标不可达。A* 在找到目标后停止，只返回 `solution-subgraph`，不能当作全览图。

`graph.complete` 仍只是搜索器产生的运行时标记，BFS 队列不变量本身尚未形式证明。新增的 `StateGraph.checkClosedGraph` 不信任该标记，而是重新检查：初态在节点数组中，且数组对每个节点的全部 `legalMoves` 后继封闭。`checkClosedGraph_sound` 随后由 `Reachable` 归纳证明所有可达状态都在数组中。再结合 `checkNoGoal = true`，`no_reachable_goal_of_closed_graph` 可在内核中证明不存在可达目标。

当前通用 BFS 的节点是**编号敏感的精确状态**：两个尺寸相同但编号不同的木块交换位置，默认仍是两个状态。搜索器可以使用由 `shapes + goal.positions` 推导的运行时对称键减少 A* 重复搜索。经典华容道的同形标签商和水平镜像商已经具有无条件的 Lean 路径投影/提升定理；决策骨架层则证明每条带权宏路径都能等成本展开为具体合法路径。任意用户关卡仍需根据其形状与目标约束构造相应等价关系并证明代表无关性，不能直接复用经典关卡的 `S₄ × S₄` 实例。

### 两种搜索方法

- **A* 快速求解**：使用受目标约束块的左上角曼哈顿距离之和作为启发式；二叉最小堆、HashMap 去重、gScore/parent 和 lazy duplicate；目标从最小优先级堆顶弹出后停止，返回 `solution-subgraph`。
- **BFS 图枚举**：继续处理队列直到可达分量耗尽或资源上限，返回 `reachable-graph` 或 `truncated-subgraph`；需要像经典华容道一样自由手动探索所有分支时应选择此模式。

A* 只改变候选动作的搜索顺序。成功结果仍必须由 `checkSolution` 从初态独立重放，随后才能构造 `Solution` 和 `Nonempty (Solution spec)`。A* 的堆不变量和最优性尚未封装为内核定理，因此 `shortest.kernelProved` 仍为 false。

提交前端搜索限制时会取整并钳制：空值回退默认值，`maxStates ∈ [1, 2000000]`，`maxDepth ∈ [0, 10000]`。服务端仍进行独立严格校验。

### 经典横刀立马盲测基准

实验室包含一个 `4×5 / 10 块` 的“经典横刀立马”预设，但通用求解器不会导入或读取 `classic116Actions`。该预设和其他用户关卡一样，只作为 `PuzzleSpec` 输入通用搜索。已有经典证书仅用于独立回归比较，绝不进入实验场搜索路径。

普通编号 A* 在 50,000 状态内未找到解。加入由 `shapes + goal.positions` 自动推导的“同形状且同目标约束”搜索对称类后，HTTP 盲测在约 22 秒内搜索得到 116 步候选，随后由通用 `checkSolution` 重放为 true。当前对称去重和 A* 最优性仍是可执行算法边界；返回路径合法性是 Lean 内核定理。

求解等待时间默认 120 秒，页面可设置 1–600 秒。超时只表示资源未决：第一层关卡成立保持通过，搜索层显示警告，不会把超时错误报告成 `wellFormed=false` 或证明失败。

棋盘外框右下角也有拖拽手柄，可按格改变棋盘宽高（1–16）；两个编辑棋盘同步更新，越界木块会标红并等待 Lean 重新验证。

### 搜索结果语义

- `solved`：Lean BFS 找到动作列表，并由 `checkSolution` 从初态逐步重放验证目标；
- `unreachable`：没有资源截断，整个可达分量处理完毕且没有目标；
- `limit`：达到 `maxStates` 或 `maxDepth`，只能报告“结论未知”；
- `invalid`：`wellFormed spec = false`。

BFS 与 A* 返回的路径长度首先是可执行搜索结果。通用路径存在性、图边 checker soundness、`GraphPath.toReachable` 和独立有限节点集闭包 checker 已由 Lean 内核证明；搜索队列本身的完备性和 A* 最优性仍未封装成内核证明，因此 API 继续返回 `shortest.kernelProved = false`。

通用最短性现在具有独立的证明接口。`LowerBoundCertificate spec L` 提供势函数 `rank`，证明初态势为零、每个合法动作至多把势增加一、每个目标状态的势至少为 `L`。若一条已由 `checkSolution` 重放的路径恰有 `L` 步，`shortest_of_verified_path_and_lower_bound` 证明它不长于任何其他可执行解。搜索器负责提供上界，证书负责提供下界，两者不要求信任 A* 的堆顺序。

## Lean 与前端的数据链

`Model.lean / Transition.lean` 定义和证明规则，`ExportMain.lean` 调用同一个 `legalMoves / tryMove` 枚举状态图并生成 `frontend/graph.json`，浏览器只读取这份数据。前端不会重新实现一套华容道碰撞规则，因此棋盘可执行的每条边都来自 Lean 模型。

### Windows 启动

在项目根目录双击 [`start-huarongdao.cmd`](start-huarongdao.cmd)，或在 PowerShell 中运行：

```powershell
.\start-huarongdao.cmd
```

脚本会检查 Node.js、Lean Lake、`node_modules` 和 Lean 求解器；缺少前端依赖时执行 `npm ci`，缺少编译产物时执行 `lake build`，缺少经典图数据时执行 `lake exe export-graph frontend/graph.json`，随后在可见的独立窗口启动本地服务，并打开：

```text
http://127.0.0.1:4173/?mode=lab
```

关闭服务窗口即可停止服务。脚本会先请求 `http://127.0.0.1:4173/api/health`：若已是本项目服务则直接打开；若 `4173` 被其他程序占用则明确报错，不会重复启动。

视频、原互动网站和本项目采用不同的显示技术：视频使用作者自写的 C++/CUDA 渲染与力布局；原网站读取预计算坐标并用 Canvas 2D 投影；本项目按研究需求额外使用 `3d-force-graph` 提供可释放、可重新加热的三维查看器。自定义关卡的结构坐标由 `structural-layout-worker.js` 在本机计算，不来自在线网站或经典 `layout.json`。力布局只改变坐标，不改变 Lean 状态、合法边、可达性或最短距离。

实时面板中的 `ValidState = true` 依据是：经典初态有 `classic_valid`，且每条成功转换满足 `tryMove_preserves_validity`，进而所有可达节点满足 `reachable_preserves_validity`。`goal` 则直接读取 Lean 导出时对该状态计算的目标谓词。

通关结果会区分两种情况：只使用棋盘方向操作时，记录为连续的玩家解；图导航会先计算合法路径，再逐边更新棋盘并将每帧标记为 `tryMove = some`，但不把自动导航计作玩家手动解。

## 经典模式的三种图展示

- **参考全览**：自定义 Three.js 点线渲染器显示全部 25,955 个节点和 41,948 条连接，固定使用离线预计算坐标。
- **曹操追踪 / 位置投影**：在 `shape` 层按曹操左上角精确坐标形成 12 组；在 `mirror` 和 `corridor` 层使用 `min(x, 2 - x)` 形成 8 个水平镜像位置轨道，避免依赖导出器选择的代表元。普通边只在真实曹操移动时改变位置组；corridor 宏边检查完整 `steps`，因此不会漏掉首步不是曹操、但内部包含曹操移动的压缩路径。该粗粒度视图是 `Observation` 的关系像，不把相同位置状态错误声明为双模拟等价，也不声称保持最短距离。
- **终局汇点**：只把全部 `goal = true` 的成功状态收缩成一个合成汇点，非目标状态保持原样；删除目标内部边并保留所有进入目标集合的边，因此到目标集合的最短距离保持不变。汇点用于可视化与导航，不声称不同终局之间存在一步转换。
- **3D 力导向**：由 `3d-force-graph@1.80.0` 渲染同一份 Lean 图。默认以 `fx/fy/fz` 固定参考形状；“释放并重新加热”会保留参考边长和弱锚定力，运行有限次 `d3-force-3d` 松弛；“固定参考形状”可精确恢复坐标。
- **局部探索**：只显示已经到达的状态、已经走过的边，以及当前状态的一步合法后继。玩家移动或路径动画每经过一条合法边，图中就加入对应节点和连接，逐步织出转换图。

三种模式共享同一套路径交互。点击节点只选择路径端点，系统先计算 `当前 → 选定起点 → 选定终点` 的最短路径，再逐边更新棋盘；任何一帧都必须对应 Lean 导出的合法边，不允许直接跳转状态。

## 路径就是证明

`Path s t` 是一个依赖类型。它的每个 `cons` 构造器都必须携带等式：

`tryMove s action.piece action.direction = some next`

因此无法为非法移动构造 `Path`。`Solution classic` 再增加 `goal target = true`；`CertifiedPlay classic` 则直接保存玩家的 `List Action`、执行成功等式和目标证明。项目已经构造 `classic116Play`，并证明它包含 116 个动作且执行后到达出口。

前端顶部的“路径证明”按钮会打开实时证明工作台。每次操作都会新增一个 `Path.cons`；如果导出的商图目标更换了同形棋子标签，则展示 `QPath.cons`，其中分别显示精确 `tryMove = some actual` 和 `SameShape actual representative`。到达出口后，精确玩家路径显示为 `CertifiedPlay`，使用规范代表的路径显示为 `QSolution`。工作台还提供证明树和可复制的 Lean 证明骨架。

## 四层证明状态

1. **动作枚举**：`mem_legalMoves_iff`、`legalMoves_sound`、`legalMoves_complete` 已由 Lean 内核检查。
2. **路径证明**：`Path`、`Solution`、`CertifiedPlay`、`classic_solvable` 和 116 步具体解已完成。
3. **图证书**：`checkQuotientLowerBound_sound` 将初态、闭包、逐边势函数约束和目标下界的可执行检查转成 `QuotientLowerBoundCertificate`；经典 25,955 节点商图由 `native_decide` 给出 true 证明。
4. **最短性**：`classic116Play_minimal` 证明已检查的 116 步玩家解全局最短；`ClassicStateSpaceKernel.concreteSolution_lower_bound` 进一步说明统一内核中任意具体解都至少需要 116 个原子移动。

## 对称性

`SameShape` 忽略四个竖块和四个小兵的标签差异，并已证明自反、对称、传递及目标保持。`PieceRelabeling` 表示保形标签置换；`Relabeling.lean` 进一步证明任意合法 `SameShape` 都由一个实际置换实现，且 `occupiedCells`、`valid`、`moveUnchecked` 和 `tryMove` 在该置换下等变，因此同形商是长度保持的精确双模拟商。`mirrorState` 和 `Direction.mirror` 表示左右镜像，并证明镜像保持合法性、成功移动和中央出口目标。

最短路径并不因这些对称性而唯一。运行 `npm run analyze:symmetry` 会对最短路径 DAG 做精确大整数计数，并同时报告“整条路径统一做一次左右镜像”的轨道数和逐状态镜像商中的路径数；计数按节点序列去重，不把同一对商节点之间的平行动作标签重复计数。

抽象 `GameSymmetry` 表明：只要一个状态变换与 `tryMove` 交换且保持 `goal`，Lean 就能自动把任意 `Path` 和 `Solution` 映射为对称的新证明。

经典内核维护四个互不覆盖的 `StateSpace.Task`：

```text
具体合法状态
  -> 同形标签商
  -> 水平镜像商
  -> 决策骨架加权压缩
```

前两层通过 `Observation.projectionHom` 投影，并通过 `BisimulationQuotient` 从任意代表逐边提升；决策骨架层的每条宏边携带完整镜像商路径。`CorridorExport` 在 Lean 中验证父图所有不同的有向端点邻接均被恰好一次分段覆盖、路径内部节点确为非 anchor 且每个步骤可重放。镜像层的 `checkMirrorEdgesComplete` 才负责全部带动作存储边，包括同一端点的平行动作边；因此 corridor 元数据使用 `parentAdjacencyIntegrity`，并明确声明 `one_representative_per_directed_adjacency`。`ClassicStateSpaceKernel.corridorWalk_liftsToConcrete` 将形式化的 corridor 宏路径展开为具体合法路径，并证明具体步数等于宏边权重之和。当前 `CorridorExport` 的数组 checker 还没有把任意 JSON 数组反射成依赖类型的 `CorridorSegmentation` 对象；这里的“已验证”是 Lean 内核执行的有限 `Bool` 证书检查，不能表述为该桥接定理已经完成。

## 数学模型

棋盘宽 4、高 5。状态保存十个带身份棋子的左上角坐标；棋子形状由身份固定。`valid s` 同时检查所有棋子在界内且两两不重叠。

`tryMove s p d : Option State` 是唯一受信任的转换入口：返回 `some t` 当且仅当把棋子 `p` 沿 `d` 平移一格后得到合法状态。关系层定义为：

`Step s t := ∃ action, tryMove s action.piece action.direction = some t`

导出时，四个 1×2 竖块和四个 1×1 小兵分别按位置排序生成规范键。这对应按 `S₄ × S₄` 标签置换作用取商，避免把几何上相同的布局重复展示。Lean 核心状态仍保留棋子身份，因此规则定义和证明不依赖商表示。

## 构建与运行

要求 Lean 4.33.1、Lake、Node.js 20 或更高版本。

```bash
lake build
lake exe huarongdao
lake exe export-graph frontend/graph.json
lake exe check-certificate
lake exe solve-puzzle 3 2 1000 20 2 1 1 0 0 2 0 1 1 1 0 '*' '*'
npm run analyze
npm run layout
npm run serve
```

浏览器打开 <http://127.0.0.1:4173>。也可用 `npm run check` 同时验证 Lean 构建和前端脚本语法。

## 状态空间持久化与缓存

状态空间数据分成四个可独立复用的层：

| 层 | 主要文件 | 内容 |
| --- | --- | --- |
| `classic-full-shape` | `frontend/full-shape-components.json` | 65,880 个同形合法布局、898 个连续分量摘要 |
| `classic-shape-quotient` | `frontend/graph.json`、`frontend/layout.json` | 经典同形商图及坐标 |
| `mirror-quotient` | `frontend/graph.mirror.json`、`frontend/layout.mirror.json` | 水平镜像商图及坐标 |
| `corridor` | `frontend/graph.corridor.json`、`frontend/layout.corridor.json` | 带权决策骨架和可回放宏边 |

`frontend/state-space-manifest.json` 是这些产物的统一索引。它记录每个文件的
SHA-256、字节数、修改时间、来源证书、状态数量、边数量、分量数量和工具链版本。
坐标文件被视为与对应图文件的状态顺序绑定的展示缓存，不作为 Lean 数学证书。

缓存命令只读取现有文件，不重新执行 Lean 证书：

```bash
npm run cache:status   # 检查源文件和产物指纹，退出码 2 表示需要刷新
npm run cache:write    # 根据当前已有产物写入/更新 manifest
```

只要某个空间的生成器依赖和产物 SHA-256 没有变化，后续导出器、前端和报告都应直接复用
manifest 指向的文件；不要以重新运行 `native_decide` 作为缓存命中检查。只改证明接口
不会使状态图和布局空间失效。
Lean 证明侧的共享入口是 `Huarongdao.ClassicFullSpaceCachedCertificate`。
该模块只投影 `ClassicFullSpaceCertificate` 已经生成的证明对象，不引入新的全空间计算。

## 关键文件

- `Huarongdao/Model.lean`：棋盘、合法性、移动、目标和经典布局
- `Huarongdao/Transition.lean`：一步关系、可达性和保持性证明
- `Huarongdao/Enumeration.lean`：动作枚举 soundness/completeness
- `Huarongdao/Paths.lean`：依赖路径与 Solution
- `Huarongdao/StateSpace.lean`：统一 `Task` 对象、同态及复合、观测商任务、双模拟商和长度保持路径提升
- `Huarongdao/ProofGame.lean`：CertifiedPlay 与抽象 GameSymmetry
- `Huarongdao/Symmetry.lean`：商等价、标签换位与镜像
- `Huarongdao/Relabeling.lean`：保形重标号的合法性/移动等变，以及从 `SameShape` 构造实际置换
- `Huarongdao/Quotient.lean`：同形标签观测商、已完成的 `sameShapeStepLift` 与精确双模拟
- `Huarongdao/MirrorQuotient.lean`：镜像合法性、同形商上的镜像双模拟及两级商到具体状态的提升
- `Huarongdao/CorridorCompression.lean`：保留完整展开路径的加权决策骨架状态空间
- `Huarongdao/StateSpaceKernel.lean`：经典四层状态空间的统一公开入口与端到端定理
- `Huarongdao/MathlibSymmetry.lean`：水平反射与同形重标号的 Mathlib 群作用、轨道商、稳定子和轨道大小定理
- `Huarongdao/SymmetryShortestPath.lean`：以等形/镜像对称商为基准的定长可达与最短路径等价；`mirror_shortestSolutionLength_116` 直接在镜像商上给出经典关卡最短距离
- `Huarongdao/StateSpaceAnalysis.lean`：任务多态的完整有限状态空间、BFS 距离证书、层间索引投影、割集/桥接口，以及经典 `concrete → shape → mirror` 商塔
- `Huarongdao/StateSpaceBfs.lean`：可执行表示与语义任务分离的通用 BFS；同一引擎可枚举 concrete、shape、mirror 层，并保留具体动作作为路径提升和前端交互载荷
- `Huarongdao/StateSpaceConnectivity.lean`：可逆任务上的可达等价关系、可达分支商、一步不变量及 Mathlib 连通分支等价
- `Huarongdao/ClassicFullSpace.lean`：经典全拼法候选枚举、紧凑索引、单次 DFS 分量摘要与数据层
- `Huarongdao/ClassicFullSpaceCertificate.lean`：隔离运行的 65,880 状态、898 摘要与闭包原生证书
- `Huarongdao/ClassicFullSpaceSoundness.lean`：DFS 父边、闭包 checker 到语义可达分类的 soundness 桥
- `Huarongdao/ClassicFullSpaceCompleteness.lean`：经典同形空间的规范枚举完备性证明
- `Huarongdao/ClassicContinuousClassCard.lean`：隔离的 `898` 基数接口和经典大分量 `25,955` 语义计数接口
- `Huarongdao/ClassicComponentSymmetry.lean`：水平/垂直反射对合法移动、ShapeState、连续分量和二分图着色的形式化
- `Huarongdao/ClassicComponentSymmetryCertificate.lean`：459 个水平轨道、固定分量和两个最大分量交换的隔离原生证书
- `Huarongdao/GraphTopology.lean`：Mathlib 二分图、交换方形胞腔、基本环类、桥与必经门 checker
- `Huarongdao/Search.lean`：BFS、图 checker 与商图下界证书
- `Huarongdao/ClassicCertificate.lean`：经典有限商图的 116 下界、玩家解最短性及统一 `StateSpace.Task` 接口
- `Huarongdao/Minimality.lean`：势函数最短性定理
- `Huarongdao/Bottleneck.lean`：必经区域、割集、扫掠区，以及“所有解都到达关羽已清空曹操下降扫掠区的状态”定理
- `Huarongdao/ClassicSolution.lean`：116 步内核检查解
- `Huarongdao/Generic/Model.lean`：通用棋盘、编号块、初态、目标和移动
- `Huarongdao/Generic/Enumeration.lean`：通用合法动作枚举精确性
- `Huarongdao/Generic/Paths.lean`：参数化 Path、Solution 和 checker 命题
- `Huarongdao/Generic/Transition.lean`：通用 Step、Reachable 及保持性
- `Huarongdao/Generic/Reversibility.lean`：方向取逆、合法移动可逆、一步关系对称与无自环
- `Huarongdao/Generic/Search.lean`：有资源上限的精确 BFS、StateGraph、GraphPath 与边 checker
- `Huarongdao/Generic/Verification.lean`：搜索成功到可达目标及解存在的最终证明链
- `Huarongdao/Generic/Certificates.lean`：有限状态集闭包 checker、不可达证书、势函数下界与通用最短性定理
- `Huarongdao/Generic/MathlibGraph.lean`：项目状态图到 `SimpleGraph` 的投影、可判定邻接、walk/可达性桥和 `SimpleGraph.dist` 最短路接口
- `Huarongdao/Generic/FiniteMathlibGraph.lean`：认证有限数组到诱导子图的嵌入、闭包下完整语义图/有限图/BFS 数组距离一致性、谓词割集和必经点接口
- `Huarongdao/Generic/Examples.lean`：非华容道 3×2 内核回归实例，以及有限 BFS 图、完整语义图的 Mathlib 距离与桥判定实例
- `GenericMain.lean`：通用 Lean 求解器 JSON 输出程序
- `frontend/laboratory.js`：关卡编辑、API、回放和证明链
- `frontend/structural-layout-worker.js`：任意关卡的确定性四维展开、镜像约束和三维投影
- `frontend/state-space-visualization.js`：通用状态空间、布局坐标与节点点击负载的适配接口
- `scripts/serve.mjs`：静态资源与 `POST /api/puzzle/solve`
- `scripts/check-generic.mjs`：四类搜索结果自动回归测试
- `scripts/check-layout.mjs`：30、660 和 1,620 节点图的有限性、确定性、镜像误差与大图近场分箱回归
- `CertMain.lean`：经典完整图证书执行检查
- `ExportMain.lean`：BFS 枚举与 JSON 导出
- `FullSpaceMain.lean`：导出 898 个确定性分量代表及完整性元数据
- `frontend/full-space.html`、`frontend/full-space.js`：898 个连续分量和 230 个 Klein 轨道的确定性三维总览
- `frontend/full-shape-components.json`：Lean 导出的分量大小、代表棋盘和三种离散对称像
- `frontend/app.js`：棋盘、参考全览、`3d-force-graph` 与局部探索交互
- `frontend/vendor/`：项目本地固定的 Three.js、OrbitControls 和 `3d-force-graph` 浏览器运行时
- `frontend/graph.json`：由 Lean 生成的状态和合法边，不手工维护
- `frontend/layout.json`：按 Lean 状态 ID 对齐的参考三维坐标
- `frontend/graph.mirror.json`、`frontend/layout.mirror.json`：本地镜像商数据、两端坐标与中点坐标
- `frontend/graph.corridor.json`、`frontend/layout.corridor.json`：Lean 有限 checker 验证的决策骨架关键节点、代表性宏边路径与坐标
- `scripts/import-reference-layout.mjs`：参考坐标到规范状态键的可复现映射
- `scripts/build_mirror_quotient.py`：从同形商底图生成独立镜像商文件
- `Huarongdao/CorridorExport.lean`：Lean 中的有限 corridor 自动分段、有向邻接覆盖和代表动作路径重放检查
- `scripts/build_corridor_compression.py`：只从 Lean corridor 图映射坐标、计算中点并写布局摘要
- `scripts/check-local-state-spaces.mjs`：三层计数、布局对齐和宏边完整展开回归
- `scripts/analyze-state-space.py`：桥、割点和双连通块的探索性复算
- `STATE_SPACE_RESEARCH.md`：图生成证据、Mathlib 对应关系与后续形式化路线
- `STATE_SPACE_VISUALIZATION.md`：任意有限状态空间的输入、坐标、渲染和点击接口
- `THIRD_PARTY_NOTICES.md`：参考布局来源和 GPLv3 许可说明

## 当前边界

当前“步”定义为单个棋子平移一个格。最短距离因此按单格移动计数。两个完整图模式绘制整个可达连通分量；局部探索只绘制本局逐步发现的子图。棋盘操作和自动导航都会移动当前状态环并更新路径，其中自动导航的相邻帧必须由一条 Lean 合法边连接。经典参考坐标适配自 2swap/Klotski-Webpage，自定义坐标由本项目 Worker 生成；两者都只是可视化数据。地标、镜像配对、力参数、屏幕中的细颈以及 `3d-force-graph` 的松弛结果都不是数学证书。Lean 权威数据仍是状态、动作标签与合法有向一步；视觉上的桥或门区必须经过有限图 checker 后才能成为定理。通用精确 `StateGraph` 现可认证嵌入 Mathlib 有限诱导子图；在额外通过 `checkClosedGraph` 后，Lean 证明完整语义图距离、有限诱导子图距离和 BFS 距离数组三者一致，Mathlib 的有限连通性和 `IsBridge` 因而可以直接应用。经典 25,955 节点数据仍是同形商 `Graph`，尚需单独的商图桥接。BFS 枚举器与独立证书检查器都是可执行 Lean 程序。一般性的动作枚举、路径、商证书下界和最短性推导已经形式证明；完整 25,955 节点商图的 true 证书现已由 `ClassicCertificate.lean` 封装为可被统一状态空间内核直接消费的 116 步下界。
