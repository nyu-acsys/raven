// Mirrors every `.rav` file under `tutorial/` into `public/`, keeping its path
// relative to the site root, so that links like `./hit_counter_pure.rav` in the
// tutorial's prose -- which point at real source files, not other pages --
// resolve to something VitePress actually serves. A page at /tutorial/01-sequential/
// links to ./hit_counter_pure.rav, so the copy has to land at
// public/tutorial/01-sequential/hit_counter_pure.rav. Run automatically via the `predev`/`prebuild` npm
// scripts; safe to re-run any time.
//
// Wipes and rebuilds the mirror from scratch on every run (rather than only
// adding/overwriting) so that moving or renaming a `.rav` file in the
// source tree doesn't leave a stale orphaned copy behind under `public/`.
import { readdirSync, statSync, mkdirSync, copyFileSync, rmSync } from 'node:fs'
import { join, dirname, relative } from 'node:path'
import { fileURLToPath } from 'node:url'

const docsRoot = dirname(dirname(fileURLToPath(import.meta.url)))
const tutorialRoot = join(docsRoot, 'tutorial')
const publicRoot = join(docsRoot, 'public')

function removeStaleRav(dir) {
  for (const entry of readdirSync(dir)) {
    const full = join(dir, entry)
    const stat = statSync(full)
    if (stat.isDirectory()) {
      removeStaleRav(full)
    } else if (entry.endsWith('.rav')) {
      rmSync(full)
    }
  }
}

function walk(dir) {
  for (const entry of readdirSync(dir)) {
    const full = join(dir, entry)
    if (full === publicRoot) continue
    const stat = statSync(full)
    if (stat.isDirectory()) {
      walk(full)
    } else if (entry.endsWith('.rav')) {
      const rel = relative(docsRoot, full)
      const dest = join(publicRoot, rel)
      mkdirSync(dirname(dest), { recursive: true })
      copyFileSync(full, dest)
    }
  }
}

removeStaleRav(publicRoot)
walk(tutorialRoot)
console.log('sync-rav: mirrored .rav files into public/')
