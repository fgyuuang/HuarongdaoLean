# State-Space Cache Design

## 目标

状态空间生成和 Lean 证书检查是昂贵操作，前端布局和交互读取不应重复触发它们。
项目使用 `frontend/state-space-manifest.json` 作为唯一索引，将四层状态空间的产物、
来源和证书元数据绑定在一起。

## 数据层

| 层 | 数据 | 语义 |
| --- | --- | --- |
| `classic-full-shape` | `full-shape-components.json` | 全部同形合法布局的连续分量摘要 |
| `classic-shape-quotient` | `graph.json`、`layout.json` | 经典同形商图和确定性坐标 |
| `mirror-quotient` | `graph.mirror.json`、`layout.mirror.json`、`mirror-quotient-summary.json` | 水平镜像商图 |
| `corridor` | `graph.corridor.json`、`layout.corridor.json`、`corridor-compression-summary.json` | 带权决策骨架和宏边回放数据 |

图文件是状态和边的权威展示载荷；布局文件只通过状态顺序与图文件关联。
布局坐标、力导向参数和 Three.js 渲染结果不参与 Lean 证明。

## Manifest 字段

Manifest 包含：

- `schemaVersion`：缓存格式版本；当前版本为 `2`；
- `gitRevision`、`toolchain`：生成环境；
- `source`：所有空间声明的源码记录的并集；
- `artifacts`：每个 JSON 文件的 SHA-256、字节数和修改时间；
- `spaces`：空间到产物、源码记录、上游 artifact 依赖、证书模块和结构摘要的映射；
- `policy`：证书权威性、失效规则和坐标绑定规则。

每个 `spaces.<name>` 条目同时包含：

- `sourceFiles`：该空间的完整生成链源码路径；
- `sources`：按路径保存的源码文件记录，所有记录都会参与 stale 比较；
- `dependencies`：该空间读取的上游 JSON artifact 记录；
- `artifacts`：该空间自己生成的 JSON artifact 记录。

例如，镜像商显式依赖 `frontend/graph.json` 和
`frontend/layout.json`；corridor 层显式依赖
`frontend/graph.mirror.json` 和 `frontend/layout.mirror.json`。因此上游图或布局
改变时，下游空间也会标记为 `stale`。

`full-shape-components.json` 的摘要会记录 65,880 个布局、898 个连续分量、
206,780 条有向动作边、经典分量大小 25,955，以及 `allValid`、`keysUnique`、
`closed` 三个已有证书结果。镜像和 corridor 摘要分别记录节点、边、目标和最短距离。

## 命中与失效

```text
npm run cache:status
```

该命令只读取文件并按空间比较 SHA-256：

- `ready`：该空间的源码、上游 artifact 和自身产物均未变化，可以直接复用；
- `stale`：列出该空间具体变化的源码、上游 artifact 或自身产物，只安排受影响层的生成/证明任务。

源码记录按空间独立比较，而不是只依赖全局源码表。这样修改
`FullSpaceMain.lean`、`ExportMain.lean`、`MirrorQuotient.lean`、
`CorridorCompression.lean`、`CorridorExport.lean`、布局导入脚本或任一
Python 派生脚本时，相关空间会立即失效；传递依赖这些生成链的下游空间也会一并失效。

它不会调用 `lake`、BFS、DFS 或 `native_decide`。写入 manifest：

```text
npm run cache:write
```

写入先生成临时文件，再原子重命名，避免浏览器或并行任务看到半个 JSON。

## Lean 证书缓存边界

`Huarongdao.ClassicFullSpaceCertificate` 是执行昂贵 native 检查的唯一入口。
`Huarongdao.ClassicFullSpaceCachedCertificate` 只把已证明的
`fullSpace_facts` 投影为共享结构，不执行新的计算。连续类、对称性和报告模块应
依赖这个共享接口。

`.olean` 只能作为本地增量编译缓存，不能作为可移植数学数据。跨机器或跨版本复用时，
必须同时满足 manifest 中的源 SHA-256、Lean 版本和 mathlib revision；否则标记为失效。

## 推荐工作流

1. 修改状态模型、枚举器或证书源码后运行 `npm run cache:status`。
2. 只有在 `CACHE MISS` 时，安排一次对应层的生成和一次 Lean 证书检查。
3. 生成完成后运行 `npm run cache:write`，保存新的 manifest。
4. 前端首先读取 manifest，再加载对应空间的 JSON；点击事件只在已缓存图上查询节点和棋盘。
5. 只改变布局或 UI 时，不重跑状态生成和 Lean 证书；manifest 会仅显示布局文件变化。

任意新任务可沿用同一格式：新增一个 `spaces.<name>` 条目，列出状态图、布局、
摘要和证书模块，将完整生成链加入 `sourceFiles`，并将读取的上游 JSON 加入
`dependencies`。不要只把路径加入列表而省略对应的记录；`cache:write` 会自动为
这些路径记录 SHA-256。
