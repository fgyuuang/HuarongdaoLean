# Third-Party Notices

## Klotski-Webpage reference coordinate data (GPL-3.0-only)

The file `frontend/layout.json` contains adapted three-dimensional layout coordinates from [2swap/Klotski-Webpage](https://github.com/2swap/Klotski-Webpage) commit `6e27747b2c5b21553ab9c64855d8eb23bee76ca2`, mapped to this project's Lean-generated canonical state identifiers.

The upstream project is licensed under the GNU General Public License version 3. Only its reference `x,y,z` coordinates are adapted. Its puzzle rules, adjacency lists, distances and goal labels are not treated as project data; states and legal directed transitions remain generated and checked by this project's Lean implementation. The adapted coordinate data remains subject to GPL-3.0.

Upstream license: <https://github.com/2swap/Klotski-Webpage/blob/6e27747b2c5b21553ab9c64855d8eb23bee76ca2/LICENSE>

## swaptube structural-layout reference

The independently written `frontend/structural-layout-worker.js` is informed by the graph-spreading design in [2swap/swaptube](https://github.com/2swap/swaptube), including four-dimensional force computation, nonlinear edge forces, symmetry constraints, spatial near-field correction and dimensional compression.

The current reference tree, commit `24ed45d145dbcdaac18584cc0c3cee5cd7caf694`, is distributed under The Unlicense. This project independently adds deterministic landmark initialization, browser Worker integration, periodic spatial hashing with deterministic far-field sampling, state-based mirror detection and layout regression metrics.

Upstream license: <https://github.com/2swap/swaptube/blob/24ed45d145dbcdaac18584cc0c3cee5cd7caf694/LICENSE>

## 3d-force-graph

The file `frontend/vendor/3d-force-graph.min.js` is copied from `3d-force-graph` version 1.80.0 and is used by the complete force-directed graph mode.

`3d-force-graph` is Copyright (c) 2017 Vasco Asturiano and is distributed under the MIT License. A copy of that license is stored at `frontend/vendor/3d-force-graph.LICENSE.txt`.

Upstream project: <https://github.com/vasturiano/3d-force-graph>

## Three.js and OrbitControls

The files `frontend/vendor/three.module.min.js`, `frontend/vendor/three.core.min.js` and `frontend/vendor/OrbitControls.js` are distributed as part of Three.js and are used for WebGL rendering, cameras and orbit interaction.

Three.js is Copyright (c) 2010-2025 Three.js Authors and is distributed under the MIT License. A copy of that license is stored at `frontend/vendor/three.LICENSE.txt`.

Upstream project: <https://github.com/mrdoob/three.js>
