# 华容道 Lean 项目交接说明

> 更新时间：2026-08-27

## 1. 项目定位

`HuarongdaoLean` 是一个 Lean 4 + Three.js 的有限滑块谜题形式化与可视化项目。经典模式完整形式化“横刀立马”华容道；通用关卡实验室支持自定义有限矩形棋盘、编号矩形块、初态和目标约束。Lean 负责状态、合法移动、可达性、证明对象、搜索图及证书检查；浏览器前端消费 Lean 导出或求解接口返回的数据，不另建一套权威碰撞规则。

## 2. 当前已完成

### Lean 形式化核心

- 建立 4×5 棋盘、10 个有身份棋子、棋子形状、坐标和状态模型。
- 定义界内、不重叠和 `ValidState` 合法性。
- 定义唯一可信移动入口 `tryMove`，并以 `Step`、`Reachable` 表示一步移动和可达性。
- 完成经典初始布局 `classic` 及其合法性证明 `classic_valid`。
- 证明成功移动、一步关系和可达状态保持合法性。
- 完成 `legalMoves` 的可靠性与完备性：`mem_legalMoves_iff`、`legalMoves_sound`、`legalMoves_complete`。

### 路径、解与对称性

- 用依赖类型 `Path` 强制每一步携带 `tryMove = some next` 的等式，因此非法动作不能构造路径。
- 完成 `Solution`、`CertifiedPlay`，并给出 116 个单格移动的具体通关序列 `classic116Play`。
- Lean 内核计算检查 116 步动作长度、执行结果和目标谓词。
- 完成 `SameShape` 商等价、同形棋子换位、左右镜像及抽象 `GameSymmetry` 基础。

### BFS、商图和证书

- Lean 内实现可达状态 BFS：按等形棋子标签置换取规范键，生成商状态图。
- 已生成过完整图数据：约 25,955 个商状态、41,948 条无向连接（导出的有向边数量约为 83,896，具体以运行命令输出为准）。
- 证书程序检查商边 soundness、后继闭包、规范代表唯一性、距离约束、目标 116 步下界以及 116 步目标存在性。
- 抽象定理 `QuotientLowerBoundCertificate.solution_lower_bound` 与势函数最短性框架已经完成。

### Web 前端

- Three.js 三维状态图，支持全览模式和探索模式；全览可在原图、左右镜像商图和带权路径骨架之间切换。
- 当前前端计算得到 13,011 个镜像轨道（67 个自对称点）；路径骨架保留 10,429 个锚点，压缩 2,582 个度数为 2 的中间点。
- 商节点可局部展开具体成员，骨架边可展开完整商节点序列；路径压缩只作用于显示层，不改变状态等价关系或实际移动步数。
- 支持棋盘手动操作、撤回、复位、提示、导航到终点、路径动画、当前节点定位、起终点选择和缩放。
- 实时展示 `ValidState`、`goal`、转换来源、BFS 距离和合法后继。
- 有“路径证明”工作台，可展示精确 `Path`/`Step`、商图 `QPath`/`QStep`、证明树和 Lean 代码骨架。
- 到达出口后显示完成节点、玩家移动数、BFS 距离和验证类别。
- 已保留若干桌面端与移动端截图作为交接参考。

### 通用关卡与状态空间研究

- `Huarongdao/Generic/` 提供与经典棋子身份解耦的有限矩形滑块模型、转移、路径、搜索和验证接口。
- 关卡实验室支持编辑棋盘尺寸、编号块尺寸与位置、部分目标约束、搜索上限，并通过 Lean 服务求解和独立重放结果。
- 通用搜索返回精确编号状态图，可构造 `Nonempty (Solution spec)` 与可达目标见证。
- `Huarongdao/StateSpace.lean`、`Quotient.lean`、`Bottleneck.lean` 及配套研究文档提供有限状态空间、商映射和瓶颈分析基础。
- 经典前端同时保留参考全览、`3d-force-graph` 力导向和局部探索；参考全览内部再支持原图、镜像商图、路径骨架三级切换。

## 3. 当前重要边界 / 未完项

1. **最短性证明已经闭合**：`ClassicCertificate.lean` 使用 `native_decide` 检查完整 25,955 节点商图所需的起点、闭包、距离和目标下界条件，构造 `classicQuotientLowerBoundCertificate`，并给出最终内核定理 `classic116Play_minimal : classic116Play.Minimal`。首次重建该模块会执行完整图检查，耗时明显高于普通模块。
2. 当前“步”是一个棋子平移一格，距离按单格移动计数，不是传统宣传中的宏观步数。
3. `frontend/graph.json` 是 Lean 生成物，已加入忽略规则；需要运行导出命令才能重新生成。`frontend/layout.json` 是参考三维坐标，通常应保留。
4. 参考布局来自 `2swap/Klotski-Webpage`，受 GPLv3 影响，详见 `THIRD_PARTY_NOTICES.md` 和 `frontend/reference-layout.LICENSE.txt`。

## 4. 构建、验证和运行

环境要求：Lean 4.33.1、Lake、Node.js 20+。

```bash
lake build
lake exe huarongdao
lake exe export-graph frontend/graph.json
lake exe check-certificate
npm run layout
npm run check:quotient
npm run check
npm run serve
```

前端服务默认访问：<http://127.0.0.1:4173>。

建议交接时先执行：

```bash
npm run check
lake exe check-certificate
```

其中 `check-certificate` 应打印并验证：边 sound、后继闭包、规范代表唯一、距离约束、所有目标距离至少 116、存在距离 116 的目标。

## 5. 协作建议

- Lean 模型与定理：优先修改 `Huarongdao/Model.lean`、`Transition.lean`、`Enumeration.lean`、`Paths.lean`、`ProofGame.lean`、`Symmetry.lean`、`Search.lean`、`Minimality.lean`、`ClassicSolution.lean`。
- 图导出与证书入口：`ExportMain.lean`、`CertMain.lean`。
- 前端交互：`frontend/app.js`、`frontend/styles.css`、`frontend/index.html`；商图与骨架算法位于 `frontend/overview-quotient.js`。
- 前端商图一致性检查：`scripts/check-overview-quotient.mjs`。它检查镜像覆盖、商边具体见证、骨架路径连续性和完整边覆盖。
- 参考布局映射：`scripts/import-reference-layout.mjs`；静态服务：`scripts/serve.mjs`。
- 不要手工编辑 `frontend/graph.json`；修改 Lean 规则后重新导出。
- 建议后续分支：`mirror-automorphism`（完整镜像移动双射）、`certificate-ci`（缓存完整证书构建）、`frontend-polish`（交互/UI）。
- 每次协作提交前至少运行 `npm run check`；涉及图规则时再运行导出和证书检查。

## 6. Git 与同步状态

- 默认分支为 `main`，远端为 `https://github.com/fgyuuang/HuarongdaoLean.git`。
- 本轮同步基于远端已有的通用关卡实验室与状态空间可视化提交完成 rebase，没有覆盖远端历史。
- `.gitignore` 忽略 `.lake/`、`node_modules/`、日志、临时产物以及 Lean 生成的 `frontend/graph.json`。
- 提交内容包含 Lean 源码、前端源码、固定第三方运行时、参考布局、许可证说明和本交接文档；生成图和构建缓存不进入版本库。

## 7. 2026-08-27 修稿详细汇报

### 7.1 修稿目标与最终结论

本轮修稿围绕两个目标展开：一是把全览图中的左右镜像压缩从纯前端展示提升为具有 Lean 定义的商关系；二是补齐经典 116 单格移动解的全局最短性证明。两个目标均已落地：

- Lean 中已有最终定理 `classic116Play_minimal : classic116Play.Minimal`。
- 完整 25,955 节点同形商图通过可执行检查，并由通用 soundness 定理提升为 `QuotientLowerBoundCertificate classic 116`。
- 前端在原图之上新增左右镜像商图和带权路径骨架，且每条商边、每条骨架路径都保留原始 Lean 图中的具体边序列作为见证。

### 7.2 Lean：同形重标号与移动兼容性

主要修改位于 `Huarongdao/Symmetry.lean` 和 `Huarongdao/Model.lean`：

- 为 `Piece`、`State` 补充 `ReflBEq`、`LawfulBEq`，使可执行等值检查能够安全进入证书链。
- 为 `PieceRelabeling` 增加恒等置换、复合、逆置换相关接口。
- 证明重标号保持 `occupiedCells`、`inBounds`、`noOverlap` 和 `valid`。
- 证明 `moveUnchecked`、`tryMove` 与同形棋子重标号交换。
- 枚举四个竖块和四个小兵各自的 24 个排列，提供 `findShapeRelabeling`，并证明 `findShapeRelabeling_sound`。
- 增加 `ObservationalEq` 下的移动与目标兼容定理，避免依赖底层数组表示的字面相等。

这部分解决了原先 `SameShape` 只有几何意义、但证书无法提取具体标签置换 witness 的问题。现在图中每个规范代表都能与具体后继通过显式 `PieceRelabeling` 联系起来。

### 7.3 Lean：左右镜像商

在既有 `mirrorPos`、`mirrorState`、`Direction.mirror` 基础上新增：

- `ValidState.horizontallyBounded`：合法状态必然满足水平镜像所需的边界条件。
- `MirrorEquivalent s t := SameShape s t ∨ SameShape (mirrorState s) t`。
- `mirrorEquivalent_goal_iff`：镜像商在有界布局上保持目标判定。
- `MirrorQStep`：精确移动之后允许选择直接同形类或左右镜像类。
- `Step → QStep → MirrorQStep` 的嵌入定理。

因此，前端的 13,011 个镜像轨道已有对应的 Lean 语义。当前 Lean 层形式化的是镜像等价关系、目标兼容和商边入口；前端的具体轨道枚举仍由导出图上的可执行算法完成，并由独立检查脚本复核。

### 7.4 Lean：完整下界证书与最短性闭合

主要修改位于 `Huarongdao/Search.lean`、`Huarongdao/ClassicCertificate.lean` 和 `CertMain.lean`：

- `Graph` 保留 BFS 的规范键索引，用于从具体状态定位代表节点。
- `checkRelabeledClosed` 检查每个代表状态的每个合法后继都能找到显式重标号代表，并满足距离至多增加 1。
- `Graph.Represents` 用“观察等价于某个代表的重标号”表达具体状态属于商节点。
- `Graph.CertificateEdge` 同时携带精确移动、目标重标号和局部距离不等式。
- `Graph.quotientLowerBoundCertificate` 将起点、闭包、距离和目标下界检查的 soundness 组装成抽象证书。
- `QuotientLowerBoundCertificate.play_lower_bound` 直接对 `CertifiedPlay` 的动作列表给出长度下界。
- `classicQuotientLowerBound_checked` 使用 `native_decide` 检查完整图条件。
- `classicQuotientLowerBoundCertificate` 是最终可由 Lean 定理消费的证书对象。
- `classic116Play_minimal` 将证书下界与已检查的 116 步具体玩法连接，完成全局最短性证明。

首次从干净缓存构建 `ClassicCertificate.lean` 会重新执行完整 BFS 与闭包检查，本机实测约 8 分钟；缓存有效时普通增量构建会快得多。

### 7.5 前端：镜像商图与路径骨架

新增 `frontend/overview-quotient.js`，并在 `frontend/app.js`、`index.html`、`styles.css` 中接入：

- 原图：25,955 个同形规范状态。
- 对称商图：按左右镜像取轨道，得到 13,011 个类，其中 67 个为自对称类。
- 路径骨架：保留起点、目标和分叉节点，压缩度数为 2 的走廊；得到 10,429 个锚点，压缩 2,582 个中间类，最长走廊为 11 条商边。
- 商节点支持局部展开成员；骨架边支持展开完整商节点序列。
- 所有导航最终还原为原始状态图中的逐边路径，不会把一条带权骨架边误当成一次华容道移动。
- 派生图重新采用三维布局，保留缩放、选择、当前状态定位和路径播放能力。

### 7.6 自动检查与实测结果

新增 `scripts/check-overview-quotient.mjs` 和 npm 命令 `check:quotient`。最后一次完整验证结果：

```text
lake build
Build completed successfully (31 jobs).

lake exe check-certificate
states=25955, edges=83896
all quotient edges sound: true
all legal successors represented: true
canonical representatives unique: true
distance constraints valid: true
all goals have distance >= 116: true
a goal exists at distance 116: true
kernel certificate conditions valid: true

npm run check:quotient
mirror-orbits=13011, fixed=67, edges=20969
skeleton-nodes=10429, weighted-edges=18387
compressed-degree-2=2582, longest-corridor=11
all quotient witnesses and skeleton paths valid: true
```

`npm run check` 已串联 Lean 构建、前端语法检查和商图一致性检查。

### 7.7 文件级变更索引

- `Huarongdao/Model.lean`：补充可执行等值定律实例。
- `Huarongdao/Symmetry.lean`：重标号代数、移动交换律、显式 witness 搜索、左右镜像商。
- `Huarongdao/Search.lean`：图索引、重标号闭包检查、商下界证书构造和玩家下界定理。
- `Huarongdao/ClassicCertificate.lean`：完整经典图检查、证书实例和最终最短性定理。
- `Huarongdao.lean`：导出新增证书模块。
- `CertMain.lean`：输出并纳入内核证书条件检查。
- `frontend/overview-quotient.js`：镜像轨道、商边、路径骨架及 witness 数据。
- `frontend/app.js`：三种全览图层、派生图布局、展开和导航交互。
- `frontend/index.html`、`frontend/styles.css`：商图模式控件和对应样式。
- `scripts/check-overview-quotient.mjs`：镜像覆盖、商边见证和骨架路径检查。
- `package.json`：加入 `check:quotient` 并整合到 `npm run check`。
- `README.md`、`HANDOFF.md`：更新证明边界、运行方式和本轮交接说明。

### 7.8 后续建议

- 若要让镜像后的每一步直接形成完整双射自动机，可继续证明 `tryMove` 与 `mirrorState` 在所有合法状态上的方向交换定理，并封装合法状态版本的 `GameSymmetry`。
- 将完整证书计算放入 CI 时应启用 `.lake` 缓存；无缓存构建耗时较长。
- 修改棋盘规则、规范键或镜像算法后，必须同时运行 `lake exe check-certificate` 与 `npm run check:quotient`。
- `frontend/graph.json` 继续作为生成物，不应手工提交或修改。

### 7.9 与远端既有修稿的合并说明

同步前，GitHub `main` 已包含通用拼图模型、关卡实验室、`3d-force-graph` 完整图、结构布局 Worker 和状态空间研究管线。本轮提交已 rebase 到这些提交之上，最终组合关系如下：

- 顶层经典图模式仍为 `参考全览 / 3D 力导向 / 局部探索`。
- `参考全览` 内部新增 `原图 / 对称商图 / 路径骨架`，没有移除力导向模式。
- `frontend/app.js` 同时保留力导向图的释放、重新加热、固定参考坐标，以及镜像商节点/骨架边的展开功能。
- `package.json` 的 `npm run check` 同时运行通用关卡回归、结构布局回归和镜像商图 witness 检查。
- `Huarongdao.lean` 同时导出通用模型、状态空间研究模块和新增的经典最短性证书模块。

因此本轮不是用经典商图功能替换远端通用化工作，而是将二者合并为同一条可构建、可测试的主线。
