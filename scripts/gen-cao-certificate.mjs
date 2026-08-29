import fs from 'node:fs';

const graph = JSON.parse(fs.readFileSync(new URL('../frontend/graph.json', import.meta.url), 'utf8'));
const state = id => graph.states[id];

const pairs = [
  ['00_01', 940, 1004, 'down'],
  ['00_10', 81, 101, 'left'],
  ['01_02', 17693, 17780, 'down'],
  ['01_11', 14499, 14980, 'left'],
  ['02_03', 17851, 17967, 'down'],
  ['02_12', 17278, 17346, 'left'],
  ['03_13', 23949, 24026, 'right'],
  ['10_11', 16, 29, 'down'],
  ['10_20', 85, 106, 'right'],
  ['11_12', 16275, 16509, 'down'],
  ['11_21', 14701, 15160, 'right'],
  ['12_13', 25062, 25080, 'up'],
  ['12_22', 17255, 17329, 'right'],
  ['13_23', 23962, 24037, 'left'],
  ['20_21', 932, 990, 'down'],
  ['21_22', 17685, 17771, 'down'],
  ['22_23', 17790, 17894, 'down']
];

const directionName = {
  up: '.up', down: '.down', left: '.left', right: '.right'
};

const witnessNames = new Set();
for (const [, source, target] of pairs) {
  witnessNames.add(source);
  witnessNames.add(target);
}

const witnessDefs = [...witnessNames].sort((a, b) => a - b).map(id => {
  const positions = state(id).positions.map(([x, y]) => `⟨${x},${y}⟩`).join(', ');
  return `def classicCaoWitnessState${id} : ValidClassicState :=
  ⟨{ positions := #[${positions}] }, by
    unfold ValidState
    native_decide⟩`;
}).join('\n\n');

const pairTheorems = pairs.map(([name, source, target, direction]) => `
theorem classicCaoClassDistance_${name} :
    CaoClassConcreteDistanceOne
      (caoPositionObservation.classOf classicCaoWitnessState${source})
      (caoPositionObservation.classOf classicCaoWitnessState${target}) := by
  exact caoClassAdjacent_concreteDistance_one
    (concrete_step_caoClassAdjacent (action := ⟨.caoCao, ${directionName[direction]}⟩)
      (by
        change tryMove (classicCaoWitnessState${source}.1) .caoCao ${directionName[direction]} =
          some classicCaoWitnessState${target}.1
        native_decide)
      (by native_decide))`).join('\n\n');

const structureFields = pairs.map(([name, source, target]) =>
  `  pair_${name} : CaoClassConcreteDistanceOne
    (caoPositionObservation.classOf classicCaoWitnessState${source})
    (caoPositionObservation.classOf classicCaoWitnessState${target})`).join('\n');

const aggregateFields = pairs.map(([name]) =>
  `  pair_${name} := classicCaoClassDistance_${name}`).join('\n');

const output = `import Huarongdao.CaoProjection
import Std.Tactic

namespace Huarongdao
namespace ClassicStateSpaceKernel

/- Concrete legal representatives for the 17 geometric neighbor pairs of the
   twelve Cao Cao position classes. State ids refer to frontend/graph.json. -/
${witnessDefs}

${pairTheorems}

/-- One concrete one-step witness for each of the 17 geometric neighbor pairs. -/
structure CaoClassDistanceCertificate where
${structureFields}

/-- The bundled 17-witness certificate for the twelve-point projection. -/
theorem allCaoClassDistanceCertificates : CaoClassDistanceCertificate :=
  {
${aggregateFields}
  }

end ClassicStateSpaceKernel
end Huarongdao
`;

fs.writeFileSync(new URL('../Huarongdao/CaoProjectionCertificate.lean', import.meta.url), output);
