import { existsSync, readFileSync } from 'node:fs'
import { isAbsolute, relative, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'
import { defineConfig, mergeConfig } from 'vitepress'
import { siteBase, sourceExtensions } from './project.mjs'

export { siteBase, sourceExtensions } from './project.mjs'

/** VitePress 1.x can report base-prefixed page links as dead before removing the base. */
export function existingBasePage(root, base, url) {
  if (base === '/' || !url.startsWith(base)) return false
  const page = url.slice(base.length).replace(/[?#].*$/, '').replace(/\.html$/, '')
  const target = resolve(root, `${page.endsWith('/') ? page + 'index' : page}.md`)
  const path = relative(root, target)
  return path !== '..' && !path.startsWith('../') && !path.startsWith('..\\')
    && !isAbsolute(path) && existsSync(target)
}

export function defineProjectSite(project, config) {
  const base = siteBase(project)
  const extensions = sourceExtensions(project)
  const languages = (project.grammars ?? []).map(({ file, aliases }) => {
    const path = file instanceof URL ? fileURLToPath(file) : resolve(project.root, file)
    const grammar = JSON.parse(readFileSync(path, 'utf8'))
    return aliases ? { ...grammar, aliases } : grammar
  })
  const merged = mergeConfig({
    base,
    srcExclude: ['node_modules/**', 'scripts/**', 'site-kit/**'],
    // Installed theme packages import CSS and must pass through Vite's SSR bundler.
    vite: { ssr: { noExternal: ['@nyu-acsys/docs-kit'] } },
    markdown: { languages },
    ignoreDeadLinks: [
      ...(extensions.length ? [new RegExp(`\\.(?:${extensions.join('|')})$`)] : []),
      url => existingBasePage(project.root, base, url)
    ]
  }, config)
  const configureMarkdown = merged.markdown.config
  merged.markdown.config = md => {
    project.sections?.install(md)
    configureMarkdown?.(md)
  }
  return defineConfig(merged)
}
