# -*- coding: utf-8 -*-
"""Build the forced-corridor state space derived from the mirror quotient.

This script never changes the formal or finite mirror quotient. It reads
graph.mirror.json/layout.mirror.json and writes independent corridor files.
Every macro edge retains its complete mirror-node path and primitive actions.
"""
from __future__ import annotations

import heapq
import json
from collections import defaultdict, deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FRONTEND = ROOT / "frontend"
GRAPH_MIRROR = FRONTEND / "graph.mirror.json"
LAYOUT_MIRROR = FRONTEND / "layout.mirror.json"
GRAPH_OUT = FRONTEND / "graph.corridor.json"
LAYOUT_OUT = FRONTEND / "layout.corridor.json"
SUMMARY_OUT = FRONTEND / "corridor-compression-summary.json"


def load_json(path: Path):
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def save_json(path: Path, data) -> None:
    with path.open("w", encoding="utf-8") as handle:
        json.dump(data, handle, ensure_ascii=False, separators=(",", ":"))


def undirected_key(left: int, right: int) -> tuple[int, int]:
    return (left, right) if left < right else (right, left)


def dijkstra(node_count: int, edges: list[dict], initial: int) -> list[int]:
    adjacency: list[list[tuple[int, int]]] = [[] for _ in range(node_count)]
    for edge in edges:
        adjacency[edge["source"]].append((edge["target"], edge["weight"]))
    infinity = 10**9
    distance = [infinity] * node_count
    distance[initial] = 0
    queue = [(0, initial)]
    while queue:
        current_distance, source = heapq.heappop(queue)
        if current_distance != distance[source]:
            continue
        for target, weight in adjacency[source]:
            candidate = current_distance + weight
            if candidate < distance[target]:
                distance[target] = candidate
                heapq.heappush(queue, (candidate, target))
    return distance


def unweighted_distance(node_count: int, edges: list[dict], initial: int) -> list[int]:
    adjacency: list[list[int]] = [[] for _ in range(node_count)]
    for edge in edges:
        adjacency[edge["source"]].append(edge["target"])
    distance = [-1] * node_count
    distance[initial] = 0
    queue = deque([initial])
    while queue:
        source = queue.popleft()
        for target in adjacency[source]:
            if distance[target] >= 0:
                continue
            distance[target] = distance[source] + 1
            queue.append(target)
    return distance


def main() -> None:
    graph = load_json(GRAPH_MIRROR)
    layout = load_json(LAYOUT_MIRROR)
    states = graph["states"]
    edges = graph["edges"]
    node_count = len(states)
    assert len(layout["coordinates"]) == node_count

    neighbours: list[set[int]] = [set() for _ in range(node_count)]
    edges_by_arc: dict[tuple[int, int], list[dict]] = defaultdict(list)
    for edge in edges:
        source = edge["source"]
        target = edge["target"]
        neighbours[source].add(target)
        edges_by_arc[(source, target)].append(edge)
    for labels in edges_by_arc.values():
        labels.sort(key=lambda edge: (edge["piece"], edge["direction"]))

    missing_reverse = [
        (source, target)
        for source in range(node_count)
        for target in neighbours[source]
        if source not in neighbours[target]
    ]
    assert not missing_reverse, (
        "corridor compression requires reversible mirror edges; "
        f"missing {len(missing_reverse)} reverse arcs"
    )

    initial_mirror = graph["meta"]["initial"]
    goals = {state["id"] for state in states if state["goal"]}
    anchors = {
        node
        for node in range(node_count)
        if node == initial_mirror or node in goals or len(neighbours[node]) != 2
    }

    visited: set[tuple[int, int]] = set()
    corridors: list[list[int]] = []
    for source in sorted(anchors):
        for first in sorted(neighbours[source]):
            first_key = undirected_key(source, first)
            if first_key in visited:
                continue
            visited.add(first_key)
            path = [source, first]
            previous = source
            current = first
            while current not in anchors:
                forward = neighbours[current] - {previous}
                assert len(forward) == 1, (
                    f"non-anchor {current} has {len(forward)} forward choices"
                )
                target = next(iter(forward))
                edge_key = undirected_key(current, target)
                assert edge_key not in visited, (
                    f"corridor revisits edge {current}-{target}"
                )
                visited.add(edge_key)
                path.append(target)
                previous, current = current, target
            corridors.append(path)

    all_undirected = {
        undirected_key(source, target)
        for source in range(node_count)
        for target in neighbours[source]
        if source != target
    }
    assert visited == all_undirected, (
        f"{len(all_undirected - visited)} mirror edges were not assigned "
        "to a corridor"
    )

    ordered_anchor_ids = [initial_mirror] + sorted(
        node for node in anchors if node != initial_mirror
    )
    mirror_to_corridor = {
        mirror_id: corridor_id
        for corridor_id, mirror_id in enumerate(ordered_anchor_ids)
    }

    new_states = []
    new_coordinates = []
    new_pairs = []
    for corridor_id, mirror_id in enumerate(ordered_anchor_ids):
        source_state = states[mirror_id]
        new_states.append({
            **source_state,
            "id": corridor_id,
            "mirrorId": mirror_id,
            "primitiveDistance": source_state["distance"],
        })
        new_coordinates.append(layout["coordinates"][mirror_id])
        new_pairs.append(layout["mirrorPairs"][mirror_id])

    new_edges = []

    def append_macro(path: list[int]) -> None:
        steps = []
        for source, target in zip(path, path[1:]):
            witness = edges_by_arc[(source, target)][0]
            steps.append({
                "source": source,
                "target": target,
                "piece": witness["piece"],
                "direction": witness["direction"],
            })
        new_edges.append({
            "source": mirror_to_corridor[path[0]],
            "target": mirror_to_corridor[path[-1]],
            "piece": steps[0]["piece"],
            "direction": steps[0]["direction"],
            "weight": len(steps),
            "path": path,
            "steps": steps,
        })

    for path in corridors:
        append_macro(path)
        append_macro(list(reversed(path)))

    new_edges.sort(
        key=lambda edge: (
            edge["source"],
            edge["target"],
            edge["weight"],
            edge["path"],
        )
    )

    initial = mirror_to_corridor[initial_mirror]
    weighted = dijkstra(len(new_states), new_edges, initial)
    operations = unweighted_distance(len(new_states), new_edges, initial)
    for state in new_states:
        corridor_id = state["id"]
        assert weighted[corridor_id] == state["primitiveDistance"], (
            corridor_id,
            weighted[corridor_id],
            state["primitiveDistance"],
        )
        state["operationDistance"] = operations[corridor_id]

    goal_ids = [state["id"] for state in new_states if state["goal"]]
    primitive_goal_distance = min(weighted[goal] for goal in goal_ids)
    operation_goal_distance = min(operations[goal] for goal in goal_ids)

    new_graph = {
        "meta": {
            "width": graph["meta"]["width"],
            "height": graph["meta"]["height"],
            "initial": initial,
            "stateCount": len(new_states),
            "edgeCount": len(new_edges),
            "goals": goal_ids,
            "stateSpace": "forced_corridor",
            "parent": "graph.mirror.json",
            "parentStateCount": node_count,
            "parentEdgeCount": len(edges),
            "suppressedStateCount": node_count - len(new_states),
            "primitiveShortestGoalDistance": primitive_goal_distance,
            "operationShortestGoalDistance": operation_goal_distance,
        },
        "states": new_states,
        "edges": new_edges,
    }
    new_layout = {
        "source": "layout.mirror.json anchor subset",
        "source_state_space": "forced_corridor",
        "coordinates": new_coordinates,
        "mirrorPairs": new_pairs,
    }
    summary = {
        "parentStateCount": node_count,
        "parentEdgeCount": len(edges),
        "stateCount": len(new_states),
        "edgeCount": len(new_edges),
        "suppressedStateCount": node_count - len(new_states),
        "corridorCount": len(corridors),
        "maxPrimitiveWeight": max(edge["weight"] for edge in new_edges),
        "primitiveShortestGoalDistance": primitive_goal_distance,
        "operationShortestGoalDistance": operation_goal_distance,
        "initial": initial,
    }

    save_json(GRAPH_OUT, new_graph)
    save_json(LAYOUT_OUT, new_layout)
    save_json(SUMMARY_OUT, summary)
    print(json.dumps(summary, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
