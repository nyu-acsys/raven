import { readFileSync, realpathSync } from 'node:fs'
import { basename, isAbsolute, relative, resolve, sep } from 'node:path'
import { installSectionRefs } from './refs.mjs'

function pagePath(value) {
  if (typeof value !== 'string' || !value || isAbsolute(value) || /[\\:?#]/.test(value)) {
    throw new Error(`Expected a relative Markdown page path, got ${JSON.stringify(value)}`)
  }
  if (value.replace(/\/$/, '').split('/').some(part => !part || part === '..' || part === '.')) {
    throw new Error(`A numbered page must stay inside the site: ${value}`)
  }
  const path = value.endsWith('.md') ? value.slice(0, -'.md'.length) : value
  if (path === 'index') return ''
  return path.endsWith('/index') ? path.slice(0, -'index'.length) : path
}

function appendixLabel(index) {
  let label = ''
  for (let n = index + 1; n > 0; n = Math.floor((n - 1) / 26)) {
    label = String.fromCharCode(65 + (n - 1) % 26) + label
  }
  return label
}

function inside(root, file) {
  const path = relative(root, file)
  return path !== '..' && !path.startsWith(`..${sep}`) && !isAbsolute(path)
}

export function sectionItems({ sections, pagesOrder }, page, labels) {
  return (pagesOrder[page] ?? []).map(id => {
    const section = sections[id]
    const label = labels[id]
    if (!label) throw new Error(`Missing sidebar label for ${id} (${page})`)
    return { text: `${section.number}. ${label}`, link: `${page}#${section.anchor}` }
  })
}

/** Numbered pages and appendices are explicit; other site content is not scanned. */
export function createSections({ root, chapters = [], appendices = [] }) {
  const siteRoot = realpathSync(root)
  const paths = new Set()
  const appendixIds = new Set()
  const pages = [...chapters.map(chapter => {
    if (typeof chapter.label !== 'string' || !chapter.label) {
      throw new Error(`Expected a section label for ${chapter.path}`)
    }
    return { path: pagePath(chapter.path), label: chapter.label }
  }), ...appendices.map((appendix, index) => {
    const path = pagePath(appendix.path)
    const suppliedId = appendix.id ?? basename(path.replace(/\/$/, ''))
    if (typeof suppliedId !== 'string' || !/^(app:)?[A-Za-z0-9-]+$/.test(suppliedId)) {
      throw new Error(`Invalid appendix id: ${JSON.stringify(suppliedId)}`)
    }
    const id = suppliedId.startsWith('app:') ? suppliedId : `app:${suppliedId}`
    if (appendixIds.has(id)) throw new Error(`Duplicate appendix id ${id}`)
    appendixIds.add(id)
    return { path, label: appendixLabel(index), id }
  })]
  for (const page of pages) {
    if (paths.has(page.path)) throw new Error(`Duplicate numbered page ${page.path}`)
    paths.add(page.path)
  }

  function buildRegistry() {
    const sections = {}
    const pagesOrder = {}
    const appendices = {}
    for (const page of pages) {
      const directory = page.path === '' || page.path.endsWith('/')
      const file = directory ? `${page.path}index.md` : `${page.path}.md`
      const fullPath = resolve(siteRoot, file)
      let content
      try {
        if (!inside(siteRoot, realpathSync(fullPath))) {
          throw new Error('the page resolves outside the site')
        }
        content = readFileSync(fullPath, 'utf-8')
      } catch (error) {
        throw new Error(`Cannot read numbered page ${file}: ${error.message}`, { cause: error })
      }
      const urlPath = directory ? `/${page.path}` : `/${page.path}.html`
      if (page.id) appendices[page.id] = { label: page.label, path: urlPath, file }
      const ids = []
      const headings = /^##(?!#)[ \t]+(.+?)[ \t]*\{#(sec:[A-Za-z0-9-]+)\}[ \t]*$/gm
      for (const [, title, id] of content.matchAll(headings)) {
        if (sections[id]) {
          throw new Error(`Duplicate section id ${id} (also used on ${sections[id].path})`)
        }
        sections[id] = {
          number: `${page.label}.${ids.length + 1}`, title, path: urlPath, anchor: id
        }
        ids.push(id)
      }
      pagesOrder[urlPath] = ids
    }
    return { sections, pagesOrder, pages: appendices }
  }

  return {
    buildRegistry,
    install(md) {
      installSectionRefs(md, { buildRegistry })
    }
  }
}
