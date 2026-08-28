# 有限状态空间可视化接口

这份接口把有限状态空间的数学内容、坐标生成和页面交互分成三个独立层次。

```text
状态与有向转换
  -> 确定性结构布局
  -> 带固定坐标的可视图
  -> Three.js / 3d-force-graph
  -> 点击负载
  -> 路径查询、棋盘回放或 Lean 证明展示
```

## 1. 最小状态空间

布局器不要求节点来自华容道。最小输入为：

```js
const stateSpace = {
  startId: 's0',
  nodes: [
    { id: 's0', label: '初态' },
    { id: 's1', label: '中间状态' },
    { id: 's2', label: '目标', goal: true }
  ],
  edges: [
    { source: 's0', target: 's1', action: 'a' },
    { source: 's1', target: 's2', action: 'b' }
  ]
};
```

要求：

- 节点 `id` 唯一，可以是数字或字符串；省略时使用数组下标。
- `source`、`target` 可以是节点 ID，也可以是 `{ id }`。
- `edges` 保留方向和动作标签。布局计算时只把它们视为无向连接，不改变原始转换语义。
- `startId` 可选，默认第一个节点。
- `distance` 可选，缺少时从 `startId` 计算无向 BFS 距离。
- 也可以只提供 `states`：字符串或数字状态直接作为节点 ID；对象状态默认使用数组下标作为 ID。
- 不在 `startId` 连通分量中的节点距离记为 `-1`，不会被误报为起点距离 `0`。

华容道可以额外提供 `board`、`shapes` 和每个节点的 `positions`，用于检测棋盘镜像。普通状态机不需要这些字段。

## 2. 初始坐标

随机坐标会使同一个图每次得到不同形状，也容易陷入力导向的团块局部极小值。本项目使用确定性图距离初值。

1. 从 `startId` 开始，反复选择离当前地标集合最远的节点，得到约五个地标。
2. 对每个地标执行 BFS，得到节点到各地标的图距离 `d0 ... d4`。
3. 用距离差构造四维坐标：

```text
x = d0 - d1
y = d2 - d3
z = (d0 + d1 - d2 - d3) / 2
w = d4 - (d0 + d1 + d2 + d3) / 4
```

4. 按距起点的 BFS 深度排序，让新节点向较浅邻居的平均位置靠近，并加入确定性微扰。
5. 对每个维度去中心化、归一化，再把平均边长缩放到固定范围。

这一步给出稳定的结构种子：相同节点顺序、边和起点产生完全相同的初值。

## 3. 结构松弛

初值随后进入四维力布局：

- 所有节点之间存在短程排斥。
- 邻接边使用单位方向的非线性边力；边过短时排斥，过长时吸引。
- 小图精确计算点对排斥。
- 大图使用空间分箱：近场更精确，远场确定性抽样。
- 有棋盘信息时，可加入水平和垂直镜像配对约束。
- 先在 `3.98` 维展开，再压缩到 `3.95`，最后丢弃第四维得到三维坐标。

布局输出：

```js
{
  coordinates: Float32Array, // [x0,y0,z0,x1,y1,z1,...]
  meta: {
    algorithm,
    landmarks,
    startIndex,
    elapsedMs,
    nodeCount,
    edgeCount,
    edgeMean,
    edgeDeviation,
    edgeMax,
    mirrorXError,
    mirrorYError
  }
}
```

浏览器中应通过 Web Worker 运行，避免布局计算阻塞界面。

## 4. 可视图适配

同步计算适合测试和小图：

```js
import { computeVisualStateSpace } from './state-space-visualization.js';

const visual = computeVisualStateSpace(stateSpace, progress => {
  console.log(progress.phase, progress.ratio);
});
```

浏览器大图应先由 Worker 返回布局结果，再组合数据：

```js
import { buildVisualStateSpace } from './state-space-visualization.js';

const visual = buildVisualStateSpace(stateSpace, {
  coordinates,
  meta
});
```

对于 Lean `StateGraph` 或 API 返回的图，可以直接调用：

```js
import { computeVisualStateGraph } from './state-space-visualization.js';

const visual = computeVisualStateGraph({
  meta: { initial: 0 },
  states: leanStates,
  distance: bfsDistances,
  edges: checkedEdges
});
```

浏览器页面应优先使用 Worker 异步版本：

```js
import { computeVisualStateGraphAsync } from './state-space-visualization.js';

const visual = await computeVisualStateGraphAsync(leanStateGraph, {}, {
  onProgress: ({ phase, ratio }) => {
    console.log(phase, ratio);
  }
});
```

返回的 `visual` 已经可以直接交给渲染器；布局计算不会阻塞页面主线程。

适配器会把 `states + distance + edges` 转换为通用输入；Lean 状态中的位置数组
`[[x, y], ...]` 会转换为布局器使用的 `{ x, y }`。这一步只做数据适配，不重新实现
合法移动规则。Worker 的异常、消息解码失败或坐标数量不匹配都会使 Promise 拒绝，
不会返回半成品状态空间。

`visual.nodes` 中每个节点具有：

```text
id, index, distance, x, y, z, fx, fy, fz, raw
```

`visual.edges` 保留原始动作字段，并增加：

```text
index, source, target, sourceIndex, targetIndex, raw
```

此外还提供 `outgoing`、`incoming`、`indexOf(reference)` 和 `interaction(reference)`。

## 5. 渲染策略

结构全览应优先表达图的宏观形状：

- 普通边使用细线，并按距初态、距目标或连通分量着色。
- 节点数越大，普通节点越小、越透明。
- 起点、当前点、目标、选中点和证明路径单独突出。
- 固定使用布局坐标，不在首次显示时重新随机运行三维力导向。
- 相机按三维包围盒取景，保留旋转、缩放和定位。

`3d-force-graph` 可以直接使用：

```js
graph
  .nodeId('id')
  .graphData({ nodes: visual.nodes, links: visual.links })
  .onNodeClick(clickHandler);
```

因为节点已经带有 `fx/fy/fz`，默认显示的是确定性结构。只有研究布局稳定性时才释放这三个字段并重新加热。

## 6. 点击接口

统一点击处理器：

```js
import { createNodeClickHandler } from './state-space-visualization.js';

const clickHandler = createNodeClickHandler(visual, payload => {
  console.log(payload.id);
  console.log(payload.position);
  console.log(payload.outgoing);
  console.log(payload.incoming);
  console.log(payload.neighbors);
  console.log(payload.raw);
});
```

用于 `3d-force-graph`：

```js
graph.onNodeClick(clickHandler);
```

用于自定义 Three.js `Raycaster`：

```js
const hit = raycaster.intersectObject(points)[0];
if (hit) clickHandler(visual.nodes[hit.index], pointerEvent);
```

点击负载为：

```js
{
  id,
  index,
  node,
  raw,
  position: { x, y, z },
  outgoing,
  incoming,
  neighbors,
  event
}
```

后续逻辑只消费该负载，可以实现：

- 选择路径起点和终点；
- 查询最短路径；
- 显示该状态对应的棋盘；
- 高亮一步合法后继；
- 回放边上的动作标签；
- 展示 `GraphPath` 或可达性证明；
- 在商图节点与具体代表状态之间切换。

## 7. 数学边界

坐标、颜色、相机和点击都是观察工具，不改变状态空间。

```text
Lean 权威层：节点、带动作的有向边、目标谓词、合法性证明
可视化层：无向布局连接、三维坐标、颜色、线宽、相机、点击
```

屏幕上看到的桥、团块或细颈只能作为候选结构。要把它们变成“所有解必须经过某区域”之类的定理，仍需生成割集、门区或商图证书并交给 Lean 检查。
