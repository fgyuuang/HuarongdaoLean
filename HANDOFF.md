# 华容道 Lean 项目交接说明

> 更新时间：2026-08-27

## 1. 项目定位

`HuarongdaoLean` 是一个 Lean 4 + Three.js 的“横刀立马”华容道形式化与本地可视化项目。Lean 负责棋盘状态、合法移动、可达性、证明对象、BFS 状态图、商空间和证书检查；浏览器只消费本地生成的状态空间数据与预计算坐标，不重新实现碰撞规则，也不依赖远端动态布局。

本次协作的整合原则是：吸收队友的商空间分类和形式化证明思路，保留本地可视化、坐标、展开动画、关卡实验室和一键启动方式。队友的 `frontend/overview-quotient.js` 动态抽象布局不属于当前实现。

## 2. 当前已完成

### Lean 形式化内核

- 建立 4×5 棋盘、10 个有身份棋子、棋子形状、坐标和 `ValidState` 合法性。
- 以 `tryMove` 作为唯一可信移动入口，使用 `Step`、`Reachable`、`Path` 和 `Solution` 表示可验证移动与路径。
- 完成 `legalMoves` 的可靠性与完备性：`mem_legalMoves_iff`、`legalMoves_sound`、`legalMoves_complete`。
- 完成经典 116 步具体解 `classic116Play` 的长度、执行结果和目标检查。
- 完成 `SameShape`、保形重标号、水平镜像和对应的目标/移动等变性。
- 完成同形商和镜像商的路径投影、逐边提升与长度保持。
- 以统一的 `StateSpace.Task` 维护四层对象：

```text
具体合法状态
  -> 同形标签商
  -> 水平镜像商
  -> 决策骨架加权压缩
```

- `CorridorCompression.lean` 中的内部 `corridor` 名称保留为形式化接口；网页和研究文档对用户显示为“决策骨架”。
- `ClassicCertificate.lean` 将完整商图证书接入内核，`classic116Play_minimal` 和
  `ClassicStateSpaceKernel.concreteSolution_lower_bound` 闭合 116 步下界。

### 本地状态空间数据

- 同形商：25,955 个状态，83,896 条有向边。
- 镜像商：13,011 个状态，42,055 条有向边。
- 决策骨架：10,429 个关键节点，36,774 条有向宏边。
- 决策骨架保存每条宏边的完整镜像商路径、原子步骤和权重；2,582 个连续中间状态不绘制。
- 决策骨架全览中，`weight = 1` 的普通边显示为灰色，`weight > 1` 的归并边显示为蓝色，归并边两端使用金色端点标记。

## 3. 前端交接约定

- 状态空间选择器显示：`同形商`、`镜像商`、`决策骨架`。
- 镜像商保留本地“展开 / 合并 / 100%”滑块；镜像端点、中点和动画坐标来自 `layout.mirror.json`。
- 三个状态空间分别读取：
  - `frontend/graph.json`、`frontend/layout.json`
  - `frontend/graph.mirror.json`、`frontend/layout.mirror.json`
  - `frontend/graph.corridor.json`、`frontend/layout.corridor.json`
- 参考全览、3D 力导向和局部探索均保持本地实现；远端动态重布局和浏览器轨道构造不合入。
- 决策骨架的普通边/归并边/宏边端点使用统一的权重分类，避免把未归并边误显示为蓝色。
- 关卡实验室继续保留，使用 `?mode=lab` 进入。

## 4. 当前重要边界

1. “步”表示单个棋子平移一格；决策骨架中的“宏操作”只是多个底层步的压缩显示。
2. 商空间语义由 Lean 定理提供；JSON、坐标、颜色和屏幕上的节点形状是可视化数据，不是证明本身。
3. `frontend/graph.json` 是 Lean 生成物并被 `.gitignore` 忽略；镜像商 JSON 由 Lean 生成并认证全部带动作边，决策骨架 JSON 由 Lean 生成并认证全部不同有向端点邻接及代表动作路径，Python 只负责布局派生数据。
4. 参考布局来自 `2swap/Klotski-Webpage`，受 GPLv3 影响，详见 `THIRD_PARTY_NOTICES.md` 和 `frontend/reference-layout.LICENSE.txt`。
5. 当前未提交的改动应在本次提交中统一进入 `main`；不要恢复队友的动态可视化文件。
6. corridor 的完备性契约是无标签有向端点邻接完备，不是平行动作边实例的逐条保留；元数据中的 `parentEdgeLabelPolicy` 固定为 `one_representative_per_directed_adjacency`。`CorridorExport` 当前是 Lean 内核执行的有限 `Bool` checker，尚未提供从任意导出数组到依赖类型 `CorridorSegmentation` 的反射桥接定理。

## 5. 构建、验证和运行

环境要求：Lean 4.33.1、Lake、Node.js 20+。

```powershell
npm ci
npm run check
lake exe check-certificate
npm run serve
```

生成或重建本地商空间数据：

```powershell
npm run export
npm run build:mirror
npm run build:corridor
npm run check:state-spaces
```

Windows 下可直接双击：

```text
start-huarongdao.cmd
```

服务默认地址：

```text
http://127.0.0.1:4173/
http://127.0.0.1:4173/?space=corridor
http://127.0.0.1:4173/?mode=lab
```

本次已验证：

```text
npm run check                         -> passed
lake exe check-certificate            -> kernel certificate conditions valid: true
npm run check:state-spaces            -> local state-space files and expansion paths valid: true
browser desktop/mobile regression    -> passed, 0 JavaScript errors
```

浏览器可能仍报告 Three.js 重复导入 warning；当前不影响渲染、路径证明或实验室功能。

## 6. 后续研究入口

- `Huarongdao/StateSpace.lean`：统一 `Task`、同态、复合和路径映射。
- `Huarongdao/Relabeling.lean`、`Quotient.lean`：同形标签商与代表无关性。
- `Huarongdao/MirrorQuotient.lean`：水平镜像商。
- `Huarongdao/CorridorCompression.lean`：决策骨架宏边与展开定理。
- `Huarongdao/CorridorExport.lean`：Lean 中的有限 corridor 自动分段、有向邻接覆盖和代表动作路径重放检查。
- `Huarongdao/StateSpaceKernel.lean`、`ClassicCertificate.lean`：四层状态空间和经典 116 步证书入口。
- `Huarongdao/Search.lean`、`CertMain.lean`：BFS 图证书与可执行检查。
- `frontend/app.js`、`frontend/index.html`、`frontend/styles.css`：本地可视化。
- `scripts/build_mirror_quotient.py`、`scripts/build_corridor_compression.py`：只生成镜像/决策骨架布局及摘要，不生成图边。
- `scripts/check-local-state-spaces.mjs`：三层数据、坐标对齐和宏边展开回归。

## 7. Git 交接

- 主分支：`main`
- 远端：`origin`
- 本次提交包含形式化内核、三层本地状态空间数据、前端融合、启动脚本和本交接文档。
- 推送完成后，其他成员应执行 `git pull --ff-only origin main`，再运行 `npm ci`、`npm run check` 和 `npm run check:state-spaces`。
- 不提交、不恢复 `frontend/overview-quotient.js`；如需参考其数学分类，只在 Lean/文档层面吸收。
