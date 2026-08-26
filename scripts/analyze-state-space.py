"""Explore structural features of a Lean-exported Huarongdao state graph.

This script discovers candidate bottlenecks.  Its output is not a Lean proof;
promising cuts should be rechecked by a sound Lean certificate.
"""

from __future__ import annotations

import argparse
import json
from collections import deque
from pathlib import Path


def load_graph(path: Path) -> tuple[dict, list[dict], list[dict]]:
    with path.open("r", encoding="utf-8") as stream:
        payload = json.load(stream)
    return payload.get("meta", {}), payload["states"], payload["edges"]


def connected_component(adjacency: list[set[int]], start: int) -> set[int]:
    seen = {start}
    queue = deque([start])
    while queue:
        node = queue.popleft()
        for neighbor in adjacency[node]:
            if neighbor not in seen:
                seen.add(neighbor)
                queue.append(neighbor)
    return seen


def tarjan_decomposition(
    adjacency: list[set[int]],
) -> tuple[list[tuple[int, int]], set[int], list[int]]:
    """Return bridges, articulation points, and biconnected vertex sizes."""

    discovery = [-1] * len(adjacency)
    low = [0] * len(adjacency)
    parent = [-1] * len(adjacency)
    children = [0] * len(adjacency)
    edge_stack: list[tuple[int, int]] = []
    bridges: list[tuple[int, int]] = []
    articulation_points: set[int] = set()
    block_sizes: list[int] = []
    time = 0

    def pop_block(stop: tuple[int, int] | None = None) -> None:
        vertices: set[int] = set()
        while edge_stack:
            edge = edge_stack.pop()
            vertices.update(edge)
            if stop is not None and edge == stop:
                break
        if vertices:
            block_sizes.append(len(vertices))

    for root in range(len(adjacency)):
        if discovery[root] != -1:
            continue
        discovery[root] = low[root] = time
        time += 1
        stack: list[tuple[int, object]] = [(root, iter(adjacency[root]))]
        while stack:
            node, neighbors = stack[-1]
            try:
                neighbor = next(neighbors)
            except StopIteration:
                stack.pop()
                ancestor = parent[node]
                if ancestor == -1:
                    continue

                low[ancestor] = min(low[ancestor], low[node])
                tree_edge = (ancestor, node)
                if low[node] > discovery[ancestor]:
                    bridges.append(tuple(sorted(tree_edge)))
                if low[node] >= discovery[ancestor]:
                    if parent[ancestor] != -1 or children[ancestor] > 1:
                        articulation_points.add(ancestor)
                    pop_block(tree_edge)
                continue

            if discovery[neighbor] == -1:
                parent[neighbor] = node
                children[node] += 1
                edge_stack.append((node, neighbor))
                discovery[neighbor] = low[neighbor] = time
                time += 1
                stack.append((neighbor, iter(adjacency[neighbor])))
            elif neighbor != parent[node] and discovery[neighbor] < discovery[node]:
                low[node] = min(low[node], discovery[neighbor])
                edge_stack.append((node, neighbor))

        pop_block()
        if not adjacency[root]:
            block_sizes.append(1)

    return sorted(set(bridges)), articulation_points, sorted(block_sizes, reverse=True)


def analyze(path: Path) -> dict:
    meta, states, edges = load_graph(path)
    adjacency = [set() for _ in states]
    directed_edges: set[tuple[int, int]] = set()
    self_loops = 0
    for edge in edges:
        source = int(edge["source"])
        target = int(edge["target"])
        directed_edges.add((source, target))
        if source == target:
            self_loops += 1
            continue
        adjacency[source].add(target)
        adjacency[target].add(source)

    reciprocal = sum((target, source) in directed_edges for source, target in directed_edges)
    component_sizes: list[int] = []
    unseen = set(range(len(states)))
    while unseen:
        component = connected_component(adjacency, next(iter(unseen)))
        component_sizes.append(len(component))
        unseen.difference_update(component)

    bridges, articulations, blocks = tarjan_decomposition(adjacency)
    goals = [state for state in states if state.get("goal", False)]
    goal_distances = [int(state["distance"]) for state in goals]

    return {
        "source": str(path.resolve()),
        "meta": {
            key: meta[key]
            for key in ("width", "height", "initial", "stateCount", "edgeCount")
            if key in meta
        },
        "states": len(states),
        "directedEdgeRecords": len(edges),
        "uniqueDirectedEdges": len(directed_edges),
        "uniqueUndirectedEdges": sum(map(len, adjacency)) // 2,
        "selfLoopRecords": self_loops,
        "reciprocalDirectedEdges": reciprocal,
        "allDirectedEdgesReciprocal": reciprocal == len(directed_edges),
        "connectedComponents": len(component_sizes),
        "connectedComponentSizes": sorted(component_sizes, reverse=True),
        "stronglyConnectedComponentsWhenReciprocal": (
            len(component_sizes) if reciprocal == len(directed_edges) else None
        ),
        "goalStates": len(goals),
        "goalDistanceRange": (
            [min(goal_distances), max(goal_distances)] if goal_distances else None
        ),
        "bridges": len(bridges),
        "bridgeSample": bridges[:20],
        "articulationPoints": len(articulations),
        "articulationSample": sorted(articulations)[:20],
        "biconnectedBlocks": len(blocks),
        "largestBiconnectedBlocks": blocks[:20],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("graph", type=Path, nargs="?", default=Path("frontend/graph.json"))
    parser.add_argument("--compact", action="store_true")
    args = parser.parse_args()
    result = analyze(args.graph)
    print(json.dumps(result, ensure_ascii=False, indent=None if args.compact else 2))


if __name__ == "__main__":
    main()
