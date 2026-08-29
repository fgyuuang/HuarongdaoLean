import crypto from 'node:crypto';
import fs from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const frontend = path.join(root, 'frontend');
const manifestPath = path.join(frontend, 'state-space-manifest.json');
const schemaVersion = 1;

const sourceFiles = [
  'lean-toolchain',
  'lakefile.toml',
  'Huarongdao/Model.lean',
  'Huarongdao/Transition.lean',
  'Huarongdao/Enumeration.lean',
  'Huarongdao/ClassicFullSpace.lean',
  'Huarongdao/ClassicFullSpaceCertificate.lean',
  'Huarongdao/ClassicFullSpaceSoundness.lean',
  'Huarongdao/ClassicFullSpaceCompleteness.lean',
  'Huarongdao/ClassicComponentSymmetry.lean',
  'Huarongdao/ClassicComponentSymmetryCertificate.lean',
  'Huarongdao/ClassicContinuousClassCard.lean',
  'Huarongdao/ClassicFullSpaceCachedCertificate.lean',
  'scripts/state-space-cache.mjs',
  'package.json'
];

const spaces = {
  'classic-full-shape': {
    description: 'All equal-shape legal placements grouped by continuous slide component.',
    artifacts: ['frontend/full-shape-components.json'],
    certificate: 'Huarongdao.ClassicFullSpaceCertificate',
    sourceFiles: [
      'lean-toolchain',
      'lakefile.toml',
      'Huarongdao/Model.lean',
      'Huarongdao/Transition.lean',
      'Huarongdao/Enumeration.lean',
      'Huarongdao/ClassicFullSpace.lean'
    ]
  },
  'classic-shape-quotient': {
    description: 'Label quotient graph and deterministic coordinates for the classical component.',
    artifacts: ['frontend/graph.json', 'frontend/layout.json'],
    certificate: 'Huarongdao.ClassicCertificate',
    sourceFiles: [
      'lean-toolchain',
      'lakefile.toml',
      'Huarongdao/Model.lean',
      'Huarongdao/Transition.lean',
      'Huarongdao/Enumeration.lean',
      'Huarongdao/Quotient.lean',
      'ExportMain.lean'
    ]
  },
  'mirror-quotient': {
    description: 'Horizontal-mirror quotient graph, layout, and summary.',
    artifacts: [
      'frontend/graph.mirror.json',
      'frontend/layout.mirror.json',
      'frontend/mirror-quotient-summary.json'
    ],
    certificate: 'Huarongdao.MirrorQuotient',
    sourceFiles: [
      'lean-toolchain',
      'lakefile.toml',
      'Huarongdao/Model.lean',
      'Huarongdao/Transition.lean',
      'Huarongdao/Enumeration.lean',
      'Huarongdao/MirrorQuotient.lean',
      'scripts/build_mirror_quotient.py'
    ]
  },
  corridor: {
    description: 'Weighted decision skeleton with replayable corridor metadata.',
    artifacts: [
      'frontend/graph.corridor.json',
      'frontend/layout.corridor.json',
      'frontend/corridor-compression-summary.json'
    ],
    certificate: 'Huarongdao.CorridorExport',
    sourceFiles: [
      'lean-toolchain',
      'lakefile.toml',
      'Huarongdao/CorridorExport.lean',
      'scripts/build_corridor_compression.py'
    ]
  }
};

async function exists(file) {
  try {
    await fs.access(file);
    return true;
  } catch {
    return false;
  }
}

async function sha256(file) {
  const hash = crypto.createHash('sha256');
  const data = await fs.readFile(file);
  hash.update(data);
  return {
    sha256: hash.digest('hex'),
    bytes: data.byteLength
  };
}

async function fileRecord(relativePath) {
  const absolute = path.join(root, relativePath);
  if (!(await exists(absolute))) {
    return { path: relativePath, present: false };
  }
  const stat = await fs.stat(absolute);
  const digest = await sha256(absolute);
  return {
    path: relativePath,
    present: true,
    bytes: digest.bytes,
    sha256: digest.sha256,
    modifiedAt: stat.mtime.toISOString()
  };
}

async function jsonSummary(relativePath) {
  const absolute = path.join(root, relativePath);
  if (!(await exists(absolute))) return null;
  const value = JSON.parse(await fs.readFile(absolute, 'utf8'));
  if (relativePath.endsWith('full-shape-components.json')) {
    return {
      shapeStateCount: value.meta?.shapeStateCount ?? null,
      componentCount: value.meta?.componentCount ?? null,
      directedEdgeCount: value.meta?.directedEdgeCount ?? null,
      classicComponentId: value.meta?.classicComponentId ?? null,
      classicComponentSize: value.components?.find(
        component => component.id === value.meta?.classicComponentId
      )?.stateCount ?? null,
      coveredStateCount: value.meta?.coveredStateCount ?? null,
      allValid: value.meta?.allValid ?? null,
      keysUnique: value.meta?.keysUnique ?? null,
      closed: value.meta?.closed ?? null
    };
  }
  if (relativePath.endsWith('mirror-quotient-summary.json')) {
    return {
      stateCount: value.stateCount ?? null,
      edgeCount: value.edgeCount ?? null,
      goals: value.goals ?? null,
      shortestGoalDistance: value.shortestGoalDistance ?? null
    };
  }
  if (relativePath.endsWith('corridor-compression-summary.json')) {
    return {
      parentStateCount: value.parentStateCount ?? null,
      parentEdgeCount: value.parentEdgeCount ?? null,
      stateCount: value.stateCount ?? null,
      edgeCount: value.edgeCount ?? null,
      corridorCount: value.corridorCount ?? null,
      primitiveShortestGoalDistance: value.primitiveShortestGoalDistance ?? null,
      operationShortestGoalDistance: value.operationShortestGoalDistance ?? null
    };
  }
  if (path.basename(relativePath).startsWith('graph')) {
    return {
      stateCount: value.states?.length ?? null,
      edgeCount: value.edges?.length ?? null,
      meta: value.meta ?? null
    };
  }
  if (path.basename(relativePath).startsWith('layout')) {
    return {
      coordinateCount: value.coordinates?.length ?? null,
      mirrorPairCount: value.mirrorPairs?.length ?? null,
      source: value.source ?? null
    };
  }
  return null;
}

function gitRevision() {
  try {
    return execFileSync('git', ['rev-parse', 'HEAD'], {
      cwd: root,
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'ignore']
    }).trim();
  } catch {
    return null;
  }
}

async function buildManifest() {
  const source = {};
  for (const relativePath of sourceFiles) {
    source[relativePath] = await fileRecord(relativePath);
  }

  const artifactRecords = {};
  const spaceRecords = {};
  for (const [name, space] of Object.entries(spaces)) {
    const artifacts = [];
    for (const relativePath of space.artifacts) {
      const record = await fileRecord(relativePath);
      const summary = await jsonSummary(relativePath);
      if (summary) record.summary = summary;
      artifacts.push(record);
      artifactRecords[relativePath] = record;
    }
    spaceRecords[name] = {
      description: space.description,
      certificate: space.certificate,
      sourceFiles: space.sourceFiles,
      artifacts
    };
  }

  return {
    schemaVersion,
    kind: 'huarongdao-state-space-manifest',
    generatedAt: new Date().toISOString(),
    gitRevision: gitRevision(),
    toolchain: {
      lean: (await fs.readFile(path.join(root, 'lean-toolchain'), 'utf8')).trim(),
      mathlibRevision: 'v4.33.1'
    },
    policy: {
      validation: 'Lean certificates are authoritative; manifest generation never reruns them.',
      invalidation: 'Any source or artifact SHA-256 change invalidates dependent cache entries.',
      coordinates: 'Layouts are presentation artifacts keyed by the corresponding graph state order.'
    },
    source,
    spaces: spaceRecords,
    artifacts: artifactRecords
  };
}

async function writeManifest(manifest) {
  const tempPath = `${manifestPath}.tmp-${process.pid}`;
  await fs.writeFile(tempPath, `${JSON.stringify(manifest, null, 2)}\n`, 'utf8');
  await fs.rename(tempPath, manifestPath);
}

function spaceStaleReasons(previous, current, name) {
  if (!previous) return ['manifest missing'];
  if (previous.schemaVersion !== current.schemaVersion) return ['schema version changed'];
  const oldSpace = previous.spaces?.[name];
  const newSpace = current.spaces[name];
  if (!oldSpace) return ['space entry missing'];
  const reasons = [];
  for (const source of newSpace.sourceFiles ?? []) {
    if ((previous.source?.[source]?.sha256 ?? null) !==
        (current.source?.[source]?.sha256 ?? null)) {
      reasons.push(`generator source changed: ${source}`);
    }
  }
  const oldArtifacts = Object.fromEntries(
    (oldSpace.artifacts ?? []).map(artifact => [artifact.path, artifact])
  );
  for (const artifact of newSpace.artifacts) {
    if ((oldArtifacts[artifact.path]?.sha256 ?? null) !== (artifact.sha256 ?? null)) {
      reasons.push(`artifact changed: ${artifact.path}`);
    }
    if (!artifact.present) reasons.push(`artifact missing: ${artifact.path}`);
  }
  return reasons;
}

async function readManifest() {
  if (!(await exists(manifestPath))) return null;
  return JSON.parse(await fs.readFile(manifestPath, 'utf8'));
}

function printStatus(manifest, previous) {
  let invalid = false;
  console.log(`${previous ? 'CACHE CHECK' : 'CACHE MISS'} ${manifestPath}`);
  for (const [name, space] of Object.entries(manifest.spaces)) {
    const reasons = spaceStaleReasons(previous, manifest, name);
    if (reasons.length === 0) {
      console.log(`  ${name}: ready`);
    } else {
      invalid = true;
      console.log(`  ${name}: stale`);
      for (const reason of reasons) console.log(`    - ${reason}`);
    }
  }
  return invalid;
}

const command = process.argv[2] ?? 'status';
const current = await buildManifest();
const previous = await readManifest();

if (command === 'status') {
  process.exitCode = printStatus(current, previous) ? 2 : 0;
} else if (command === 'write' || command === 'refresh') {
  await writeManifest(current);
  console.log(`WROTE ${manifestPath}`);
  printStatus(current, current);
} else {
  console.error('Usage: node scripts/state-space-cache.mjs [status|write|refresh]');
  process.exitCode = 1;
}
