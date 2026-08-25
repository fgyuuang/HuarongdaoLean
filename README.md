# 基于 Lean 4 的有限滑块谜题实验室

本项目从经典“横刀立马”华容道出发，将合法局面与一步移动定义为有限状态转移系统，并进一步抽象为支持任意有限矩形棋盘、编号矩形木块、给定初态和位置目标的通用滑块谜题形式系统。经典模式保留完整 25,955 节点商图；关卡实验室通过 HTTP 调用 Lean 通用 BFS，并独立重放返回路径以构造解的存在性证明。

## 已完成内容

- 棋子、形状、坐标、占用格、边界与不重叠条件
- 可计算的合法移动函数 `tryMove` 与一步关系 `Step`
- 自反传递可达关系 `Reachable`
- 经典初始布局合法性证明
- 成功移动保持合法性、一步保持合法性、可达状态保持合法性证明
- Lean 内实现的 BFS 状态图枚举与 JSON 导出
- 同形棋子标签置换下的规范键，即对称作用的商状态图
- Three.js 完整三维状态图：25,955 个像素级节点和 41,948 条无向连接
- 全览/探索双模式、当前状态定位、深度缩放、起终点选择和逐边路径动画
- 前端实时显示 `ValidState`、`goal` 和转换来源，并可查看已编译的定理
- 到达出口时显示完成节点、玩家步数、BFS 距离和路径验证类别
- `Path`、`Solution` 与 `CertifiedPlay`：玩家通关动作列表可以直接成为证明见证
- `mem_legalMoves_iff`：合法动作枚举的可靠性与完备性
- 116 步具体通关动作由 Lean 内核计算检查
- `SameShape` 商等价、同形棋子换位、左右镜像基础与抽象 `GameSymmetry`
- 图证书检查器验证商边、闭包、唯一代表、距离约束和目标下界

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
```

### 通用状态图探索

通用 `search` 不会在发现第一个目标后立刻停止，而会继续枚举精确编号状态，直到队列耗尽或触发资源限制。它返回：

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

前端状态图使用独立 Three.js 场景，尽量复现经典华容道的图交互：透视相机、OrbitControls 旋转/缩放、Raycaster 节点拾取、当前/起点/终点圆环、视图定位、路径覆盖线和逐边动画。全览按 BFS 距离构造三维分层布局并绘制所有已枚举节点和去重连接；探索模式只显示已经走过的节点及当前一步后继，并使用持久的局部弹簧/排斥力导向布局。点击节点只选择路径端点，播放时必须沿 Lean 导出的边逐步更新棋盘，不允许直接跳转状态。当前状态棋盘也支持原版式手动探索：选择或拖动编号块、方向按钮和方向键都只匹配当前节点的 Lean outgoing；支持撤回、复位和提示一步，每次成功移动都会织入探索图并新增一个 GraphPath.cons。

每条 JSON 边由 `StateGraph.checkEdge` 独立重放，并由以下定理连接到通用移动语义：

```lean
StateGraph.checkEdge_sound
StateGraph.checkEdges_sound
GraphPath.toReachable :
  GraphPath spec graph source target → Reachable spec source target
```

`graph.complete = false` 时，界面明确显示“资源截断子图”；此时图仍可探索，但不能用于声称目标不可达。`graph.complete = true` 表示本次可执行 BFS 没有触发上限并耗尽队列。BFS 闭包完备性尚未封装为内核级队列不变量定理。

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

BFS 与 A* 返回的路径长度是可执行搜索结果。通用路径存在性、图边 checker soundness 和 GraphPath.toReachable 已由 Lean 内核证明；搜索队列的完备性/最短性尚未封装成内核证明，因此 API 明确返回 `shortest.kernelProved = false`。

## Lean 与前端的数据链

`Model.lean / Transition.lean` 定义和证明规则，`ExportMain.lean` 调用同一个 `legalMoves / tryMove` 枚举状态图并生成 `frontend/graph.json`，浏览器只读取这份数据。前端不会重新实现一套华容道碰撞规则，因此棋盘可执行的每条边都来自 Lean 模型。

实时面板中的 `ValidState = true` 依据是：经典初态有 `classic_valid`，且每条成功转换满足 `tryMove_preserves_validity`，进而所有可达节点满足 `reachable_preserves_validity`。`goal` 则直接读取 Lean 导出时对该状态计算的目标谓词。

通关结果会区分两种情况：只使用棋盘方向操作时，记录为连续的玩家解；图导航会先计算合法路径，再逐边更新棋盘并将每帧标记为 `tryMove = some`，但不把自动导航计作玩家手动解。

## 经典模式的两种图展示

- **全览模式**：显示全部 25,955 个灰度节点和 41,948 条连接。支持深度缩放、定位当前状态、选择任意起点和终点；点击终点后，系统先计算 `当前 → 选定起点 → 选定终点` 的最短路径，再逐边播放棋盘动画，不允许直接跳转状态。
- **探索模式**：只显示已经到达的状态、已经走过的边，以及当前状态的一步合法后继。玩家移动或路径动画每经过一条合法边，图中就加入对应节点和连接，逐步织出转换图。

## 路径就是证明

`Path s t` 是一个依赖类型。它的每个 `cons` 构造器都必须携带等式：

`tryMove s action.piece action.direction = some next`

因此无法为非法移动构造 `Path`。`Solution classic` 再增加 `goal target = true`；`CertifiedPlay classic` 则直接保存玩家的 `List Action`、执行成功等式和目标证明。项目已经构造 `classic116Play`，并证明它包含 116 个动作且执行后到达出口。

前端顶部的“路径证明”按钮会打开实时证明工作台。每次操作都会新增一个 `Path.cons`；如果导出的商图目标更换了同形棋子标签，则展示 `QPath.cons`，其中分别显示精确 `tryMove = some actual` 和 `SameShape actual representative`。到达出口后，精确玩家路径显示为 `CertifiedPlay`，使用规范代表的路径显示为 `QSolution`。工作台还提供证明树和可复制的 Lean 证明骨架。

## 四层证明状态

1. **动作枚举**：`mem_legalMoves_iff`、`legalMoves_sound`、`legalMoves_complete` 已由 Lean 内核检查。
2. **路径证明**：`Path`、`Solution`、`CertifiedPlay`、`classic_solvable` 和 116 步具体解已完成。
3. **图证书**：`checkEdges_sound`、闭包 soundness 和抽象 `QuotientLowerBoundCertificate.solution_lower_bound` 已证明；对完整图执行 checker 得到边可靠、闭包、唯一代表和距离约束全部为 true。
4. **最短性**：`LowerBoundCertificate` 已证明局部势函数约束推出任意玩家解的全局长度下界，并证明达到下界的解最短。当前最后桥梁是把完整大图的可执行 true 证书封装成内核级 `LowerBoundCertificate classic 116`，避免证明阶段重新运行完整 BFS。

## 对称性

`SameShape` 忽略四个竖块和四个小兵的标签差异，并已证明自反、对称、传递及目标保持。`PieceRelabeling` 表示保形标签置换；项目包含小兵一/二换位实例。`mirrorState` 和 `Direction.mirror` 表示左右镜像，并证明方向镜像二次还原、有界状态镜像两次恢复以及中央出口目标保持。

抽象 `GameSymmetry` 表明：只要一个状态变换与 `tryMove` 交换且保持 `goal`，Lean 就能自动把任意 `Path` 和 `Solution` 映射为对称的新证明。

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
npm run layout
npm run serve
```

浏览器打开 <http://127.0.0.1:4173>。也可用 `npm run check` 同时验证 Lean 构建和前端脚本语法。

## 关键文件

- `Huarongdao/Model.lean`：棋盘、合法性、移动、目标和经典布局
- `Huarongdao/Transition.lean`：一步关系、可达性和保持性证明
- `Huarongdao/Enumeration.lean`：动作枚举 soundness/completeness
- `Huarongdao/Paths.lean`：依赖路径与 Solution
- `Huarongdao/ProofGame.lean`：CertifiedPlay 与抽象 GameSymmetry
- `Huarongdao/Symmetry.lean`：商等价、标签换位与镜像
- `Huarongdao/Search.lean`：BFS、图 checker 与商图下界证书
- `Huarongdao/Minimality.lean`：势函数最短性定理
- `Huarongdao/ClassicSolution.lean`：116 步内核检查解
- `Huarongdao/Generic/Model.lean`：通用棋盘、编号块、初态、目标和移动
- `Huarongdao/Generic/Enumeration.lean`：通用合法动作枚举精确性
- `Huarongdao/Generic/Paths.lean`：参数化 Path、Solution 和 checker 命题
- `Huarongdao/Generic/Transition.lean`：通用 Step、Reachable 及保持性
- `Huarongdao/Generic/Search.lean`：有资源上限的精确 BFS、StateGraph、GraphPath 与边 checker
- `Huarongdao/Generic/Verification.lean`：搜索成功到可达目标及解存在的最终证明链
- `Huarongdao/Generic/Examples.lean`：非华容道 3×2 内核回归实例
- `GenericMain.lean`：通用 Lean 求解器 JSON 输出程序
- `frontend/laboratory.js`：关卡编辑、API、回放和证明链
- `scripts/serve.mjs`：静态资源与 `POST /api/puzzle/solve`
- `scripts/check-generic.mjs`：四类搜索结果自动回归测试
- `CertMain.lean`：经典完整图证书执行检查
- `ExportMain.lean`：BFS 枚举与 JSON 导出
- `frontend/app.js`：棋盘与完整 Three.js 点线状态图交互
- `frontend/vendor/`：项目本地固定的 Three.js 与 OrbitControls 运行时
- `frontend/graph.json`：由 Lean 生成的状态和合法边，不手工维护
- `frontend/layout.json`：按 Lean 状态 ID 对齐的参考三维坐标
- `scripts/import-reference-layout.mjs`：参考坐标到规范状态键的可复现映射
- `THIRD_PARTY_NOTICES.md`：参考布局来源和 GPLv3 许可说明

## 当前边界

当前“步”定义为单个棋子平移一个格。最短距离因此按单格移动计数。全览模式绘制完整可达连通分量；探索模式只绘制本局逐步发现的子图。棋盘操作和自动导航都会移动当前状态环并更新路径，其中自动导航的相邻帧必须由一条 Lean 合法边连接。三维布局坐标适配自 2swap/Klotski-Webpage，状态、合法边、起点距离和目标判定仍来自 Lean 导出。BFS 枚举器与独立证书检查器都是可执行 Lean 程序。一般性的动作枚举、路径、商证书下界和最短性推导已经形式证明；完整 25,955 节点证书已计算验证为 true，但尚未全部封装为一个可由内核定理直接消费的大型证明对象。
