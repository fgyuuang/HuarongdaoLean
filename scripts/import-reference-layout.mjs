import { readFile, writeFile } from 'node:fs/promises';

const sourcePath = process.argv[2] || 'https://2swap.github.io/Klotski-Webpage/data.json';
const graphPath = process.argv[3] || 'frontend/graph.json';
const outputPath = process.argv[4] || 'frontend/layout.json';
const raw = sourcePath.startsWith('http')
  ? await (await fetch(sourcePath)).text()
  : await readFile(sourcePath, 'utf8');
const objectStart = raw.indexOf('{');
const histogramStart = raw.indexOf('var histogram_non');
const objectEnd = raw.lastIndexOf('}', histogramStart) + 1;
const reference = JSON.parse(raw.slice(objectStart, objectEnd));
const graph = JSON.parse(await readFile(graphPath, 'utf8'));

function canonicalKey(representation) {
  const cells = [...representation];
  const seen = new Set();
  const groups = { cao: [], guan: [], vertical: [], soldier: [] };
  for (let index = 0; index < cells.length; index += 1) {
    const label = cells[index];
    if (label === '.' || seen.has(label)) continue;
    seen.add(label);
    const occupied = [];
    for (let cell = 0; cell < cells.length; cell += 1) if (cells[cell] === label) occupied.push(cell);
    const xs = occupied.map(cell => cell % 4);
    const ys = occupied.map(cell => Math.floor(cell / 4));
    const code = Math.min(...ys) * 4 + Math.min(...xs);
    if (occupied.length === 4) groups.cao.push(code);
    else if (occupied.length === 2 && new Set(ys).size === 1) groups.guan.push(code);
    else if (occupied.length === 2) groups.vertical.push(code);
    else groups.soldier.push(code);
  }
  return groups.cao[0] + ';' + groups.guan[0] + ';' + groups.vertical.sort((a, b) => a - b) + ';' + groups.soldier.sort((a, b) => a - b);
}

const byKey = new Map();
for (const node of Object.values(reference)) byKey.set(canonicalKey(node.representation), node);
const missing = graph.states.filter(state => !byKey.has(state.key));
if (missing.length) throw new Error('Reference layout is missing ' + missing.length + ' Lean states');
const coordinates = graph.states.map(state => {
  const node = byKey.get(state.key);
  return [Number(node.x.toFixed(3)), Number(node.y.toFixed(3)), Number(node.z.toFixed(3)), node.solution_dist];
});
await writeFile(outputPath, JSON.stringify({ source: 'https://github.com/2swap/Klotski-Webpage', license: 'GPL-3.0', coordinates }));
console.log('Mapped ' + coordinates.length + ' reference coordinates to Lean state ids');
