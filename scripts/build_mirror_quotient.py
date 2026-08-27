# -*- coding: utf-8 -*-
"""Build a horizontal-mirror quotient of the classic Huarongdao state graph.

The quotient identifies each state with its horizontal mirror image. One
canonical old state per mirror pair is retained for rendering a concrete
board, while the quotient node is laid out at the pair midpoint. Edge labels
are lifted back to the canonical representative.
"""
from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FRONTEND = ROOT / "frontend"
GRAPH_FULL = FRONTEND / "graph.json"
LAYOUT_FULL = FRONTEND / "layout.json"
GRAPH_MIRROR_OUT = FRONTEND / "graph.mirror.json"
LAYOUT_MIRROR_OUT = FRONTEND / "layout.mirror.json"
SUMMARY_OUT = FRONTEND / "mirror-quotient-summary.json"

WIDTH = 4
HEIGHT = 5
MAX_X = WIDTH - 1

PIECE_WIDTH = [2, 2, 1, 1, 1, 1, 1, 1, 1, 1]
VERTICALS = [2, 3, 4, 5]
SOLDIERS = [6, 7, 8, 9]
DIRECTION_DELTA = {"上": (0, -1), "下": (0, 1), "左": (-1, 0), "右": (1, 0)}
MIRROR_DIRECTION = {"左": "右", "右": "左"}
REVERSE_DIRECTION = {"上": "下", "下": "上", "左": "右", "右": "左"}


def make_key(pos: list[list[int]]) -> str:
    """Match the Lean-style key used elsewhere: fixed first two pieces, then sorted groups."""
    code = lambda p: p[0] + p[1] * 4  # noqa: E731
    vertical_codes = sorted(code(pos[i]) for i in VERTICALS)
    soldier_codes = sorted(code(pos[i]) for i in SOLDIERS)
    return (
        f"{code(pos[0])};{code(pos[1])};"
        f"{','.join(map(str, vertical_codes))};"
        f"{','.join(map(str, soldier_codes))}"
    )


def canon_positions(pos: list[list[int]]) -> list[list[int]]:
    """Sort the interchangeable vertical and soldier groups to the canonical order."""
    out = [list(p) for p in pos]
    for group in (VERTICALS, SOLDIERS):
        sorted_group = sorted(out[i] for i in group)
        for i, p in zip(group, sorted_group):
            out[i] = p
    return out


def mirror_position(pos: list[int], piece: int) -> list[int]:
    x, y = pos
    return [MAX_X - (x + PIECE_WIDTH[piece] - 1), y]


def mirror_positions(pos: list[list[int]]) -> list[list[int]]:
    return canon_positions([mirror_position(p, i) for i, p in enumerate(pos)])


def apply_move(pos: list[list[int]], piece: int, direction: str) -> list[list[int]]:
    out = [list(p) for p in pos]
    dx, dy = DIRECTION_DELTA[direction]
    out[piece] = [out[piece][0] + dx, out[piece][1] + dy]
    return canon_positions(out)


def reflect_action_from_other_member(source_pos: list[list[int]], piece: int, direction: str):
    """Return piece/direction for the same move seen from the mirror state."""
    old = canon_positions(source_pos)
    mirrored = mirror_positions(old)
    src_cell = mirror_position(old[piece], piece)
    if piece not in VERTICALS and piece not in SOLDIERS:
        # Cao Cao and Guan Yu are 2-wide and horizontally fixed on the 4-wide board.
        return piece, MIRROR_DIRECTION.get(direction, direction)

    group = VERTICALS if piece in VERTICALS else SOLDIERS
    new_piece = next(
        q for q in group
        if mirrored[q] == src_cell
    )
    new_direction = MIRROR_DIRECTION.get(direction, direction)
    return new_piece, new_direction

def mirror_partner(old_id: int, old_states, state_class_key: list[str], classes: dict[str, list[int]]) -> int:
    """Return the horizontal-mirror partner of an old state, or itself when fixed."""
    candidates = classes[state_class_key[old_id]]
    if len(candidates) == 1:
        return old_id
    return next(candidate for candidate in candidates if candidate != old_id)


def load_json(path: Path):
    with path.open("r", encoding="utf-8") as fh:
        return json.load(fh)


def save_json(path: Path, data) -> None:
    with path.open("w", encoding="utf-8") as fh:
        json.dump(data, fh, ensure_ascii=False, separators=(",", ":"))
    path.write_text(path.read_text(encoding="utf-8"), encoding="utf-8")


def main() -> None:
    graph = load_json(GRAPH_FULL)
    layout = load_json(LAYOUT_FULL)

    old_states = graph["states"]
    old_edges = graph["edges"]
    old_coordinates = layout["coordinates"]
    assert len(old_states) == len(old_coordinates), "graph/layout length mismatch in full data"

    classes: dict[str, list[int]] = {}
    state_class_key: list[str] = [""] * len(old_states)
    for idx, state in enumerate(old_states):
        state_positions = canon_positions(state["positions"])
        own_key = state.get("key") or make_key(state_positions)
        mirror_key = make_key(mirror_positions(state_positions))
        key = min(own_key, mirror_key)
        state_class_key[idx] = key
        classes.setdefault(key, []).append(idx)

    canonical_from_old: dict[int, int] = {}
    canonical_key_to_index: dict[str, int] = {}
    initial_key = state_class_key[0]
    ordered_classes = [initial_key] + sorted(k for k in classes if k != initial_key)
    for new_index, key in enumerate(ordered_classes):
        canonical_from_old[min(classes[key])] = new_index
        canonical_key_to_index[key] = new_index

    new_states = []
    new_coordinates = []
    new_mirror_pairs = []
    for new_index, key in enumerate(ordered_classes):
        old_ids = classes[key]
        canonical_old = min(old_ids)
        state = old_states[canonical_old]
        min_distance = min(old_states[i]["distance"] for i in old_ids)
        goal = any(old_states[i]["goal"] for i in old_ids)
        min_goal_distance = min(old_coordinates[i][3] for i in old_ids)
        rep_coords = old_coordinates[canonical_old]
        partner_old = mirror_partner(
            canonical_old, old_states, state_class_key, classes
        )
        partner_coords = old_coordinates[partner_old]
        merged_coords = [
            (rep_coords[axis] + partner_coords[axis]) / 2
            for axis in range(3)
        ]
        new_states.append({
            "id": new_index,
            "key": key,
            "positions": canon_positions(state["positions"]),
            "distance": min_distance,
            "goal": goal,
        })
        new_coordinates.append([
            round(merged_coords[0], 3),
            round(merged_coords[1], 3),
            round(merged_coords[2], 3),
            min_goal_distance,
        ])
        new_mirror_pairs.append({
            "a": [round(rep_coords[0], 3), round(rep_coords[1], 3), round(rep_coords[2], 3)],
            "b": [round(partner_coords[0], 3), round(partner_coords[1], 3), round(partner_coords[2], 3)],
            "fixed": partner_old == canonical_old,
        })

    old_to_new: dict[int, int] = {}
    for old_id, _ in canonical_from_old.items():
        old_to_new[old_id] = canonical_from_old[old_id]

    projected: set[tuple[int, int, int, str]] = set()
    new_edges = []

    for edge in old_edges:
        old_src = edge["source"]
        old_tgt = edge["target"]
        src_class = state_class_key[old_src]
        tgt_class = state_class_key[old_tgt]
        if src_class == tgt_class:
            continue
        new_src = canonical_key_to_index[src_class]
        new_tgt = canonical_key_to_index[tgt_class]

        if old_src == min(classes[src_class]):
            piece = edge["piece"]
            direction = edge["direction"]
            actual = apply_move(old_states[old_src]["positions"], piece, direction)
        else:
            # The original edge starts from the mirror representative.  Lift it
            # so the displayed canonical representative gets a legal label.
            piece, direction = reflect_action_from_other_member(
                old_states[old_src]["positions"], edge["piece"], edge["direction"]
            )
            actual = apply_move(old_states[min(classes[src_class])]["positions"], piece, direction)

        actual_key_raw = make_key(actual)
        actual_key = min(actual_key_raw, make_key(mirror_positions(actual)))
        if actual_key != tgt_class:
            # Defensive check: mirroring a legal edge must land in the same class.
            continue

        dedupe_key = (new_src, new_tgt, piece, direction)
        if dedupe_key in projected:
            continue
        projected.add(dedupe_key)
        new_edges.append({
            "source": new_src,
            "target": new_tgt,
            "piece": piece,
            "direction": direction,
        })

    # Sort edges for deterministic output.
    new_edges.sort(key=lambda e: (e["source"], e["target"], e["piece"], e["direction"]))

    new_meta = {
        "width": WIDTH,
        "height": HEIGHT,
        "initial": old_to_new[0],
        "stateCount": len(new_states),
        "edgeCount": len(new_edges),
        "goals": [i for i, s in enumerate(new_states) if s["goal"]],
        "quotient": {
            "symmetry": "horizontal_mirror",
            "originalStateCount": len(old_states),
            "originalEdgeCount": len(old_edges),
            "mirrorClasses": len(classes),
        },
    }

    new_graph = {
        "meta": new_meta,
        "states": new_states,
        "edges": new_edges,
    }
    new_layout = {
        "source": layout.get("source", ""),
        "license": layout.get("license", ""),
        "source_quotient": "horizontal mirror quotient at mirror-pair midpoints from layout.json",
        "coordinates": new_coordinates,
        "mirrorPairs": new_mirror_pairs,
    }

    save_json(GRAPH_MIRROR_OUT, new_graph)
    save_json(LAYOUT_MIRROR_OUT, new_layout)

    summary = {
        "layoutCount": len(new_coordinates),
        "stateCount": len(new_states),
        "edgeCount": len(new_edges),
        "goals": len(new_meta["goals"]),
        "shortestGoalDistance": min(
            (s["distance"] for s in new_states if s["goal"]), default=None
        ),
        "maxDistance": max(s["distance"] for s in new_states),
        "initial": new_meta["initial"],
    }
    save_json(SUMMARY_OUT, summary)

    print(json.dumps(summary, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
