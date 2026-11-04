# Shared project documentation infrastructure

This package extends VitePress 1.6 without replacing its default theme. It supplies
section numbering, symbolic references, source downloads, sidebar styling and a
portable build launcher. Project content, navigation, language grammars, assets
and palette remain in the consuming site.

Raven uses this directory through a local `file:site-kit` dependency. Another
repository can use the same package from a pinned source checkout inside its
documentation directory, or install a tarball produced by `npm pack ./site-kit`.
The source revision should be pinned independently of the verifier dependency.
No verifier checkout or executable is required at build or runtime.

## Site configuration

The launcher reads `.vitepress/project.mjs` from the documentation directory:

```js
import { fileURLToPath } from 'node:url'
import { createSections } from '@nyu-acsys/docs-kit/sections'

const root = fileURLToPath(new URL('../', import.meta.url))

export default {
  root,
  pagesBase: '/caravan/',
  sourceExtensions: ['ml', 'mli', 'proof'],
  exampleSources: ['examples'],
  sections: createSections({
    root,
    chapters: [{ path: 'getting-started/', label: '0' }],
    appendices: []
  })
}
```

Omit `sections` for a landing-only site. Numbered page paths are site-relative
directories ending in `/`, or Markdown basenames with an optional `.md` suffix.
Appendices receive letters in configured order. Their stable reference IDs default
to `app:<basename>` and can be supplied explicitly with `id`.

The site's `.vitepress/config.mts` contains its ordinary VitePress settings:

```js
import { defineProjectSite } from '@nyu-acsys/docs-kit/config'
import project from './project.mjs'

export default defineProjectSite(project, {
  title: 'Caravan',
  description: 'Verification for multicore OCaml',
  themeConfig: {
    logo: '/logo-small.png',
    nav: [{ text: 'Get started', link: '/getting-started/' }]
  }
})
```

Custom highlighting grammars are configured with
`grammars: [{ file: new URL('./proof.json', import.meta.url), aliases: ['proof'] }]`.
Pass VitePress's standard built-in languages through `markdown.languages` as usual.
Additional configuration is merged with the shared defaults.

Use the shared theme in `.vitepress/theme/index.ts`, followed by the site's own
CSS overrides:

```js
import Theme from '@nyu-acsys/docs-kit/theme'
import './palette.css'
export default Theme
```

The shared stylesheet contains layout conventions only. Set VitePress's brand
variables, such as `--vp-c-brand-1`, in `palette.css`, with separate `.dark`
overrides where needed.

## Writing and building

An explicitly marked second-level heading, `## Ownership {#sec:ownership}`, gets
its configured chapter number and position. `{{ref sec:ownership}}` links to that
number; `{{ref app:automation}}` links to an appendix. Duplicate or unresolved IDs
fail the build. References in Markdown code spans and fenced examples remain literal.
The registry is recomputed for each page render, so edits refresh references in
development. Changes to chapter order or sidebar structure require a dev-server
restart, like other site configuration changes.

Add these commands to the consuming site's `package.json`:

```json
{
  "scripts": {
    "dev": "project-docs dev",
    "build": "project-docs build",
    "preview": "project-docs preview"
  }
}
```

Run `npm ci`, then `npm run dev` or `npm run build`. Set `GITHUB_PAGES=true` for a
production subpath build; otherwise the base is `/`. Additional arguments are
forwarded to VitePress, for example `npm run dev -- --host 127.0.0.1`.
The launcher sets the source-extension environment before VitePress starts,
avoiding cached link-rewriting settings and shell-specific environment syntax.

Source downloads retain paths relative to the documentation root. Only explicitly
configured source roots and extensions are mirrored into `public/`. An ownership
manifest removes stale generated copies without deleting other public files.
Source symlinks are skipped. Existing public files are preserved; an unmanaged
collision fails unless `adoptIdenticalExamples` explicitly permits adopting an
identical copy from an earlier build tool.

Ignore these generated files in the consuming repository:

```gitignore
node_modules/
.vitepress/cache/
.vitepress/dist/
.vitepress/section-registry.json
.vitepress/examples-manifest.json
public/**/*.ml
public/**/*.mli
public/**/*.proof
```

Use `public/**/*.rav` for Raven examples. Exclude a fetched package's source
directory from VitePress content; the built-in `site-kit/**` exclusion covers
Raven's local dependency. Pin VitePress and its dependency overrides in the
consuming site's lockfile. This package does not upgrade the generator implicitly.

From Raven's `docs/` directory, `npm test` checks the shared infrastructure and
`GITHUB_PAGES=true npm run build` checks the production site.
