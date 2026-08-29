#!/usr/bin/env node
import { cp, mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const frontend = path.join(root, 'frontend');
const leanSource = path.join(root, 'Huarongdao');
const dist = path.join(root, 'dist');
const client = path.join(dist, 'client');
const server = path.join(dist, 'server');
const metadata = path.join(dist, '.openai');

await rm(dist, { recursive: true, force: true });
await mkdir(client, { recursive: true });
await cp(frontend, client, { recursive: true });

const sourceTarget = path.join(client, 'source', 'Huarongdao');
await mkdir(sourceTarget, { recursive: true });
await cp(leanSource, sourceTarget, {
  recursive: true,
  filter(sourcePath) {
    const relative = path.relative(leanSource, sourcePath);
    return relative === '' || !path.extname(sourcePath) || sourcePath.endsWith('.lean');
  },
});

await mkdir(server, { recursive: true });
await mkdir(metadata, { recursive: true });
await cp(path.join(root, 'worker', 'index.js'), path.join(server, 'index.js'));
await cp(path.join(root, '.openai', 'hosting.json'), path.join(metadata, 'hosting.json'));

const manifest = JSON.parse(await readFile(path.join(metadata, 'hosting.json'), 'utf8'));
if (!manifest.project_id) throw new Error('Missing Sites project_id');
await writeFile(path.join(metadata, 'hosting.json'), JSON.stringify(manifest, null, 2) + '\n', 'utf8');

console.log('Prepared Sites build: dist/client, dist/server/index.js and dist/.openai/hosting.json');
