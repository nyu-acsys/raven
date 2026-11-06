#!/usr/bin/env node
import { spawnSync } from 'node:child_process'
import { createRequire } from 'node:module'
import { dirname, resolve } from 'node:path'
import { pathToFileURL } from 'node:url'
import { prepareSite } from '../src/prepare.mjs'
import { sourceExtensions } from '../src/project.mjs'

const [command, ...args] = process.argv.slice(2)
if (!['dev', 'build', 'preview', 'prepare'].includes(command)) {
  throw new Error('Usage: project-docs <dev|build|preview|prepare> [VitePress options]')
}
const project = (await import(pathToFileURL(resolve('.vitepress/project.mjs')).href)).default
// VitePress caches the extension list on first use; set it before loading its CLI.
process.env.VITE_EXTRA_EXTENSIONS = sourceExtensions(project).join(',')
if (command !== 'preview') {
  const { registry, examples } = prepareSite(project)
  console.log(`site-kit: ${Object.keys(registry?.sections ?? {}).length} numbered sections, ${examples.length} source downloads`)
}
if (command !== 'prepare') {
  const require = createRequire(import.meta.url)
  const vitepress = resolve(dirname(require.resolve('vitepress/package.json')), 'bin/vitepress.js')
  const result = spawnSync(process.execPath, [vitepress, command, project.root, ...args], { stdio: 'inherit' })
  if (result.error) throw result.error
  process.exitCode = result.status ?? 1
}
