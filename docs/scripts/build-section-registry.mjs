// Computes the section-numbering registry: a map from every numbered
// section's stable id (`sec:foo`, written in the markdown source as a
// heading's `{#sec:foo}` anchor) to the section number it should currently
// render as (`1.1`, `5.2.3`, `A.2`, ...), its title, and the page it lives on.
//
// This is what makes numbering and cross-references symbolic rather than
// hand-typed: a heading's number is *this file's position in a list*, not
// text baked into the heading itself, and a `{{ref sec:foo}}` elsewhere in
// the tutorial resolves to whatever this computes -- so inserting, removing,
// or reordering a section can never leave a stale number or a dead link
// lying around silently.
//
// `buildRegistry()` is the reusable core, imported directly by
// `.vitepress/section-refs.mts` and called fresh on every heading/`{{ref}}`
// render -- so in-page numbers and cross-references can never go stale
// during a long-running `vitepress dev` session, even without restarting it.
// Run as a script (via the `predev`/`prebuild` npm hooks, like
// `sync-rav.mjs`), it also writes `.vitepress/section-registry.json`, which
// is what `config.mts`'s sidebar generation reads -- the sidebar's *shape*
// (which pages/sections exist at all) is site-wide `themeConfig`, exactly
// like adding a new page to the sidebar, and so, like that, needs a dev
// server restart to pick up; only the numbers/links *within* a page self-heal
// live.
//
// A numbered heading is any `##` (exactly two hashes) heading whose source
// line ends in an explicit `{#sec:some-id}` anchor -- e.g.
// `## Values and types {#sec:values-and-types}`. Headings with no such
// marker, or a marker not starting with `sec:` (ordinary custom anchors, if
// any), are left alone entirely: not numbered, not in this registry, and
// `{{ref}}` can't target them. This is deliberate -- the "Debugging
// Corner"/"Why this matters"/"Exercises"/"What's next" sections every
// chapter ends with are structural, not part of the numbered sequence, and
// keeping them unmarked is exactly how that's expressed.
import { readFileSync, readdirSync, statSync, writeFileSync } from 'node:fs'
import { join, dirname, relative, sep } from 'node:path'
import { fileURLToPath } from 'node:url'

const docsRoot = dirname(dirname(fileURLToPath(import.meta.url)))
const tutorialRoot = join(docsRoot, 'tutorial')
const outPath = join(docsRoot, '.vitepress', 'section-registry.json')

// Keyed by relativePath (POSIX-style, relative to `docs/`) with no
// extension: a chapter's own `index.md` is keyed by its directory (with a
// trailing slash, matching the clean URL VitePress gives it); a standalone
// page like an appendix is keyed by its path without `.md`.
const PART_LABELS = {
  'tutorial/getting-started/': '0',
  'tutorial/sequential/': '1',
  'tutorial/ownership/': '2',
  'tutorial/modules/': '3',
  'tutorial/ghost-and-concurrency/': '4',
  'tutorial/advanced/fork-join/': '5.1',
  'tutorial/advanced/atomic-contracts/': '5.2',
  'tutorial/advanced/iterated-star/': '5.3',
  'tutorial/advanced/prophecies/': '5.4',
  'tutorial/advanced/automation/': '5.5',
  'tutorial/appendix/resource-algebras': 'A',
  'tutorial/appendix/hardware-primitives/': 'B',
  'tutorial/appendix/from-other-tools': 'C',
}

const HEADING_RE = /^##(?!#)[ \t]+(.+?)[ \t]*\{#(sec:[A-Za-z0-9-]+)\}[ \t]*$/gm

function walk(dir, out) {
  for (const entry of readdirSync(dir)) {
    const full = join(dir, entry)
    const stat = statSync(full)
    if (stat.isDirectory()) walk(full, out)
    else if (entry.endsWith('.md')) out.push(full)
  }
}

export function buildRegistry() {
  const mdFiles = []
  walk(tutorialRoot, mdFiles)

  const sections = {}
  const pagesOrder = {}

  for (const file of mdFiles) {
    const relPosix = relative(docsRoot, file).split(sep).join('/')
    const isIndex = relPosix.endsWith('/index.md')
    const pageKey = isIndex ? relPosix.slice(0, -'index.md'.length) : relPosix.slice(0, -'.md'.length)
    const partLabel = PART_LABELS[pageKey]
    if (!partLabel) continue // page has no numbered sections (overview pages, appendices D/E)

    const urlPath = isIndex ? `/${pageKey}` : `/${pageKey}.html`

    const content = readFileSync(file, 'utf-8')
    const ids = []
    let match
    let n = 0
    HEADING_RE.lastIndex = 0
    while ((match = HEADING_RE.exec(content))) {
      n += 1
      const [, title, id] = match
      if (sections[id]) {
        throw new Error(`Duplicate section id ${id} (also used on ${sections[id].path})`)
      }
      const number = `${partLabel}.${n}`
      sections[id] = { number, title, path: urlPath, anchor: id }
      ids.push(id)
    }
    pagesOrder[urlPath] = ids
  }

  return { sections, pagesOrder }
}

// Only write the JSON snapshot when run directly as a script (the
// `predev`/`prebuild` hooks), not when imported by `section-refs.mts`.
if (import.meta.url === `file://${process.argv[1]}`) {
  const { sections, pagesOrder } = buildRegistry()
  writeFileSync(outPath, JSON.stringify({ sections, pagesOrder }, null, 2) + '\n')
  console.log(`section-registry: ${Object.keys(sections).length} numbered sections across ${Object.keys(pagesOrder).length} pages`)
}
