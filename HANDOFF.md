# 华容道 Lean 项目交接说明

> 更新时间：2026-02-21

## 1. 项目定位

`HuarongdaoLean` 是一个 Lean 4 + Three.js 的“横刀立马”华容道形式化与可视化项目。Lean 负责棋盘状态、合法移动、可达性、证明对象、BFS 状态图及证书检查；浏览器前端只消费 Lean 导出的 `frontend/graph.json`，不重新实现一套碰撞规则。

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

- Three.js 三维状态图，支持全览模式和探索模式。
- 支持棋盘手动操作、撤回、复位、提示、导航到终点、路径动画、当前节点定位、起终点选择和缩放。
- 实时展示 `ValidState`、`goal`、转换来源、BFS 距离和合法后继。
- 有“路径证明”工作台，可展示精确 `Path`/`Step`、商图 `QPath`/`QStep`、证明树和 Lean 代码骨架。
- 到达出口后显示完成节点、玩家移动数、BFS 距离和验证类别。
- 已保留若干桌面端与移动端截图作为交接参考。

## 3. 当前重要边界 / 未完项

1. **最短性最后封装尚未完成**：可执行证书已经检查为 true，抽象下界定理也已证明，但 25,955 节点完整证书尚未封装成可由 Lean 内核直接消费的 `LowerBoundCertificate classic 116`。因此目前应准确表述为“116 步解已内核检查，完整商图证书已执行检查，最短性桥梁待封装”，不要直接宣称完整最短性已经由单个内核定理闭合。
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
- 前端交互：`frontend/app.js`、`frontend/styles.css`、`frontend/index.html`。
- 参考布局映射：`scripts/import-reference-layout.mjs`；静态服务：`scripts/serve.mjs`。
- 不要手工编辑 `frontend/graph.json`；修改 Lean 规则后重新导出。
- 建议后续分支：`formal-lower-bound`（最短性封装）、`frontend-polish`（交互/UI）、`docs-and-tests`（自动化验证和文档）。
- 每次协作提交前至少运行 `npm run check`；涉及图规则时再运行导出和证书检查。

## 6. 本次 Git 化结果

- 已在项目根目录初始化 Git 仓库。
- 默认分支为 `main`。
- `.gitignore` 忽略 `.lake/`、`node_modules/`、日志、临时产物以及 Lean 生成的 `frontend/graph.json`。
- 首次提交应包含 Lean 源码、前端源码、固定第三方运行时、参考布局、许可证说明和本交接文档。
