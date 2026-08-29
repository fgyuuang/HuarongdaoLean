import fs from 'node:fs';
import assert from 'node:assert/strict';

const graph = JSON.parse(fs.readFileSync(new URL('../frontend/graph.json', import.meta.url), 'utf8'));
const goals = graph.states.filter(state => state.goal);

function caoBelowGuanYu(state) {
  const [cao, guan] = [state.positions[0], state.positions[1]];
  return guan[1] < cao[1] &&
    guan[0] < cao[0] + 2 &&
    cao[0] < guan[0] + 2;
}

assert.ok(goals.length > 0, 'the exported graph must contain goal states');
assert.equal(goals.every(caoBelowGuanYu), true,
  'every valid exported goal must place Cao Cao below Guan Yu');

console.log(`CaoBelowGuanYu: ${goals.length}/${goals.length} goal states satisfy vertical and horizontal alignment`);
