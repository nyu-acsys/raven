const REF_OPEN = '{{ref '

/** A registry is shared within a render and rebuilt for the next render. */
export function installSectionRefs(md, { buildRegistry }) {
  const registryKey = Symbol('section-registry')
  const registryFor = env => env[registryKey] ??= buildRegistry()
  md.core.ruler.before('block', 'section-registry', state => {
    delete state.env[registryKey]
  })
  const defaultHeadingOpen = md.renderer.rules.heading_open
    || ((tokens, idx, options, _env, self) => self.renderToken(tokens, idx, options))

  md.renderer.rules.heading_open = (tokens, idx, options, env, self) => {
    const token = tokens[idx]
    const rendered = defaultHeadingOpen(tokens, idx, options, env, self)
    if (token.tag === 'h1') {
      const { pages } = registryFor(env)
      const page = Object.values(pages).find(page => page.file === env.relativePath)
      return page ? `${rendered}Appendix ${md.utils.escapeHtml(page.label)}: ` : rendered
    }
    if (token.tag !== 'h2') return rendered
    const section = registryFor(env).sections[token.attrGet('id')]
    return section
      ? `${rendered}<span class="section-number">${md.utils.escapeHtml(section.number)}</span> `
      : rendered
  }

  md.inline.ruler.push('section-ref', (state, silent) => {
    if (state.src.slice(state.pos, state.pos + REF_OPEN.length) !== REF_OPEN) return false
    const close = state.src.indexOf('}}', state.pos)
    if (close === -1) return false
    const id = state.src.slice(state.pos + REF_OPEN.length, close).trim()
    const { sections, pages } = registryFor(state.env)
    const appendix = id.startsWith('app:')
    const entry = appendix ? pages[id] : sections[id]
    if (!entry) {
      throw new Error(
        `{{ref ${id}}} does not match any ${appendix ? 'appendix' : 'numbered section'} in the section registry `
        + `(near byte ${state.pos} of ${state.env?.relativePath ?? '(unknown file)'})`
      )
    }
    if (!silent) {
      const open = state.push('link_open', 'a', 1)
      // VitePress's link renderer adds the deployment base exactly once.
      open.attrSet('href', `${entry.path}${appendix ? '' : `#${entry.anchor}`}`)
      const text = state.push('text', '', 0)
      text.content = appendix ? `Appendix ${entry.label}` : `§${entry.number}`
      state.push('link_close', 'a', -1)
    }
    state.pos = close + 2
    return true
  })
}
