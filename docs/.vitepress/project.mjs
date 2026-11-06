import { fileURLToPath } from 'node:url'
import { createSections } from '@nyu-acsys/docs-kit/sections'

const root = fileURLToPath(new URL('../', import.meta.url))
const sections = createSections({
  root,
  chapters: [
    { path: 'tutorial/getting-started/', label: '0' },
    { path: 'tutorial/sequential/', label: '1' },
    { path: 'tutorial/ownership/', label: '2' },
    { path: 'tutorial/modules/', label: '3' },
    { path: 'tutorial/ghost-and-concurrency/', label: '4' },
    { path: 'tutorial/advanced/fork-join/', label: '5.1' },
    { path: 'tutorial/advanced/atomic-contracts/', label: '5.2' },
    { path: 'tutorial/advanced/iterated-star/', label: '5.3' },
    { path: 'tutorial/advanced/prophecies/', label: '5.4' }
  ],
  appendices: [
    { path: 'tutorial/appendix/resource-algebras' },
    { path: 'tutorial/appendix/hardware-primitives/' },
    { path: 'tutorial/appendix/stdlib-types/' },
    { path: 'tutorial/appendix/advanced-modules/' },
    { path: 'tutorial/appendix/automation/' },
    { path: 'tutorial/appendix/overloading/' },
    { path: 'tutorial/appendix/well-founded-orders/' },
    { path: 'tutorial/appendix/from-other-tools' },
    { path: 'tutorial/appendix/extension-api' },
    { path: 'tutorial/appendix/where-next' }
  ]
})

export default {
  root,
  pagesBase: '/raven/',
  sourceExtensions: ['rav'],
  exampleSources: ['tutorial'],
  adoptIdenticalExamples: true,
  grammars: [{ file: new URL('./raven.tmLanguage.json', import.meta.url), aliases: ['raven'] }],
  sections
}
