// Wires two things into markdown-it, both driven by the section-numbering
// registry (`../scripts/build-section-registry.mjs`):
//
// 1. Numbering: a `##` heading with an explicit `{#sec:some-id}` anchor
//    (VitePress's own anchor plugin already turns that into the heading's
//    `id` and strips the marker from the rendered text, before this runs)
//    gets its registry-computed number ("1.1", "5b.3", ...) rendered right
//    after the opening tag. The number is never hand-typed in the heading
//    itself -- inserting, removing, or reordering a numbered section
//    elsewhere in the same chapter is exactly what the registry is
//    recomputed from.
// 2. Cross-references: `{{ref sec:some-id}}` anywhere in prose expands to a
//    real hyperlink to that section, with its *current* number as the link
//    text (`§1.1`). Referencing an id that doesn't exist in the registry
//    (a typo, or a section that got renamed/removed) throws and fails the
//    build -- a broken cross-reference should never silently render as
//    dead or stale text.
//
// The registry is recomputed fresh for every page render (once per render,
// cached on that render's own `env` object below -- never across renders),
// rather than read once from a JSON snapshot at startup. That's deliberate:
// a JSON-snapshot version went stale mid-`vitepress dev` session whenever a
// heading's `{#sec:...}` marker changed without a server restart, which is
// exactly the silent-drift failure mode this whole mechanism exists to rule
// out. Scanning the dozen-odd tutorial pages is cheap enough that doing it
// on every render is not worth trading away that guarantee for.
import { buildRegistry } from '../scripts/build-section-registry.mjs'

const REF_OPEN = '{{ref '

function registryFor(env: any) {
  if (!env.__sectionRegistry) env.__sectionRegistry = buildRegistry()
  return env.__sectionRegistry
}

export function installSectionRefs(md: any, { base }: { base: string }) {
  // Numbering is injected purely at the renderer level -- no token surgery
  // needed, so it works identically whether the heading's first inline
  // token is plain text, code, or anything else.
  const defaultHeadingOpen =
    md.renderer.rules.heading_open ||
    ((tokens: any, idx: number, options: any, _env: any, self: any) => self.renderToken(tokens, idx, options))
  md.renderer.rules.heading_open = (tokens: any, idx: number, options: any, env: any, self: any) => {
    const token = tokens[idx]
    const rendered = defaultHeadingOpen(tokens, idx, options, env, self)
    if (token.tag !== 'h2') return rendered
    const { sections } = registryFor(env)
    const section = sections[token.attrGet('id')]
    return section ? `${rendered}<span class="section-number">${section.number}</span> ` : rendered
  }

  md.inline.ruler.push('section-ref', (state: any, silent: boolean) => {
    if (state.src.slice(state.pos, state.pos + REF_OPEN.length) !== REF_OPEN) return false
    const close = state.src.indexOf('}}', state.pos)
    if (close === -1) return false
    const id = state.src.slice(state.pos + REF_OPEN.length, close).trim()
    const { sections } = registryFor(state.env)
    const section = sections[id]
    if (!section) {
      throw new Error(
        `{{ref ${id}}} does not match any numbered section in the section registry ` +
        `(near byte ${state.pos} of ${state.env?.relativePath ?? '(unknown file)'})`
      )
    }
    if (!silent) {
      const open = state.push('link_open', 'a', 1)
      open.attrSet('href', `${base}${section.path.slice(1)}#${section.anchor}`)
      const text = state.push('text', '', 0)
      text.content = `§${section.number}`
      state.push('link_close', 'a', -1)
    }
    state.pos = close + 2
    return true
  })
}
