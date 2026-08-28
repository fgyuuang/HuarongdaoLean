# -*- coding: utf-8 -*-
"""Build corridor visualization coordinates from the Lean-generated graph.

Lean owns corridor anchors, macro edges, paths, and primitive actions.  This
script only selects the corresponding mirror layout entries, computes
midpoints, and writes visualization metadata.
"""
from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FRONTEND = ROOT / "frontend"
GRAPH_MIRROR = FRONTEND / "graph.mirror.json"
LAYOUT_MIRROR = FRONTEND / "layout.mirror.json"
GRAPH_CORRIDOR = FRONTEND / "graph.corridor.json"
LAYOUT_OUT = FRONTEND / "layout.corridor.json"
SUMMARY_OUT = FRONTEND / "corridor-compression-summary.json"


def load_json(path: Path):
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def save_json(path: Path, data) -> None:
    path.write_text(
        json.dumps(data, ensure_ascii=False, separators=(",", ":")),
        encoding="utf-8",
    )


def main() -> None:
    mirror_graph = load_json(GRAPH_MIRROR)
    mirror_layout = load_json(LAYOUT_MIRROR)
    corridor_graph = load_json(GRAPH_CORRIDOR)

    assert corridor_graph["meta"]["stateSpace"] == "forced_corridor"
    assert corridor_graph["meta"]["generator"] == "Lean buildCorridorExport"
    assert corridor_graph["meta"]["verified"] is True
    assert corridor_graph["meta"]["parent"] == "graph.mirror.json"
    assert corridor_graph["meta"]["parentAdjacencyIntegrity"] == "sound_and_complete"
    assert corridor_graph["meta"]["parentEdgeLabelPolicy"] == (
        "one_representative_per_directed_adjacency"
    )
    assert corridor_graph["meta"]["parentStateCount"] == len(
        mirror_graph["states"]
    )
    assert corridor_graph["meta"]["parentEdgeCount"] == len(
        mirror_graph["edges"]
    )
    directed_adjacencies = {
        (edge["source"], edge["target"]) for edge in mirror_graph["edges"]
    }
    assert corridor_graph["meta"]["parentDirectedAdjacencyCount"] == len(
        directed_adjacencies
    )
    assert corridor_graph["meta"]["parentParallelEdgeCount"] == (
        corridor_graph["meta"]["parentEdgeCount"]
        - corridor_graph["meta"]["parentDirectedAdjacencyCount"]
    )
    assert len(mirror_layout["coordinates"]) == len(mirror_graph["states"])
    assert len(mirror_layout["mirrorPairs"]) == len(mirror_graph["states"])

    coordinates = []
    mirror_pairs = []
    for state in corridor_graph["states"]:
        mirror_id = state["mirrorId"]
        pair = mirror_layout["mirrorPairs"][mirror_id]
        coordinates.append(mirror_layout["coordinates"][mirror_id])
        mirror_pairs.append(
            {
                "a": [round(value, 3) for value in pair["a"][:3]],
                "b": [round(value, 3) for value in pair["b"][:3]],
                "fixed": pair["fixed"],
            }
        )

    assert len(coordinates) == len(corridor_graph["states"])
    layout = {
        "source": "layout.mirror.json Lean corridor anchor subset",
        "source_state_space": "forced_corridor",
        "coordinates": coordinates,
        "mirrorPairs": mirror_pairs,
    }
    save_json(LAYOUT_OUT, layout)

    goals = [state for state in corridor_graph["states"] if state["goal"]]
    weights = [edge["weight"] for edge in corridor_graph["edges"]]
    summary = {
        "parentStateCount": corridor_graph["meta"]["parentStateCount"],
        "parentEdgeCount": corridor_graph["meta"]["parentEdgeCount"],
        "parentDirectedAdjacencyCount": corridor_graph["meta"][
            "parentDirectedAdjacencyCount"
        ],
        "parentParallelEdgeCount": corridor_graph["meta"][
            "parentParallelEdgeCount"
        ],
        "parentAdjacencyIntegrity": corridor_graph["meta"][
            "parentAdjacencyIntegrity"
        ],
        "parentEdgeLabelPolicy": corridor_graph["meta"][
            "parentEdgeLabelPolicy"
        ],
        "stateCount": len(corridor_graph["states"]),
        "edgeCount": len(corridor_graph["edges"]),
        "suppressedStateCount": corridor_graph["meta"]["suppressedStateCount"],
        "corridorCount": len(corridor_graph["edges"]) // 2,
        "maxPrimitiveWeight": max(weights, default=0),
        "primitiveShortestGoalDistance": min(
            (state["primitiveDistance"] for state in goals), default=None
        ),
        "operationShortestGoalDistance": min(
            (state["operationDistance"] for state in goals), default=None
        ),
        "initial": corridor_graph["meta"]["initial"],
        "graphSource": "Lean buildCorridorExport",
    }
    save_json(SUMMARY_OUT, summary)
    print(json.dumps(summary, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
