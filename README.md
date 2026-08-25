# 基于 Lean 4 的华容道状态转移图

本项目形式化经典“横刀立马”华容道，将合法局面与一步移动定义为有限状态转移系统，并把 Lean 枚举得到的完整可达商图导出给交互式 Web 前端。

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

## Lean 与前端的数据链

`Model.lean / Transition.lean` 定义和证明规则，`ExportMain.lean` 调用同一个 `legalMoves / tryMove` 枚举状态图并生成 `frontend/graph.json`，浏览器只读取这份数据。前端不会重新实现一套华容道碰撞规则，因此棋盘可执行的每条边都来自 Lean 模型。

实时面板中的 `ValidState = true` 依据是：经典初态有 `classic_valid`，且每条成功转换满足 `tryMove_preserves_validity`，进而所有可达节点满足 `reachable_preserves_validity`。`goal` 则直接读取 Lean 导出时对该状态计算的目标谓词。

通关结果会区分两种情况：只使用棋盘方向操作时，记录为连续的玩家解；图导航会先计算合法路径，再逐边更新棋盘并将每帧标记为 `tryMove = some`，但不把自动导航计作玩家手动解。

## 两种展示模式

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
- `CertMain.lean`：完整图证书执行检查
- `ExportMain.lean`：BFS 枚举与 JSON 导出
- `frontend/app.js`：棋盘与完整 Three.js 点线状态图交互
- `frontend/vendor/`：项目本地固定的 Three.js 与 OrbitControls 运行时
- `frontend/graph.json`：由 Lean 生成的状态和合法边，不手工维护
- `frontend/layout.json`：按 Lean 状态 ID 对齐的参考三维坐标
- `scripts/import-reference-layout.mjs`：参考坐标到规范状态键的可复现映射
- `THIRD_PARTY_NOTICES.md`：参考布局来源和 GPLv3 许可说明

## 当前边界

当前“步”定义为单个棋子平移一个格。最短距离因此按单格移动计数。全览模式绘制完整可达连通分量；探索模式只绘制本局逐步发现的子图。棋盘操作和自动导航都会移动当前状态环并更新路径，其中自动导航的相邻帧必须由一条 Lean 合法边连接。三维布局坐标适配自 2swap/Klotski-Webpage，状态、合法边、起点距离和目标判定仍来自 Lean 导出。BFS 枚举器与独立证书检查器都是可执行 Lean 程序。一般性的动作枚举、路径、商证书下界和最短性推导已经形式证明；完整 25,955 节点证书已计算验证为 true，但尚未全部封装为一个可由内核定理直接消费的大型证明对象。
