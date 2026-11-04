import { mkdirSync, writeFileSync } from 'node:fs'
import { join } from 'node:path'
import { syncExamples } from './examples.mjs'

export function prepareSite(project) {
  const registry = project.sections?.buildRegistry()
  if (registry) {
    const directory = join(project.root, '.vitepress')
    mkdirSync(directory, { recursive: true })
    writeFileSync(join(directory, 'section-registry.json'), JSON.stringify(registry, null, 2) + '\n')
  }
  const examples = syncExamples({
    root: project.root,
    sources: project.exampleSources ?? [],
    extensions: project.sourceExtensions ?? [],
    adoptIdentical: project.adoptIdenticalExamples ?? false
  })
  return { registry, examples }
}
