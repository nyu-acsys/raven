import { defineConfig } from 'vitepress'
import { readFileSync } from 'node:fs'
import { fileURLToPath } from 'node:url'

// Without this, VitePress treats any relative link ending in an extension it
// doesn't recognize as an internal page link and rewrites it by appending
// `.html` -- e.g. `./hit_counter_pure.rav` becomes `./hit_counter_pure.rav.html`,
// a 404, since no such file exists. `.rav` is a real source file, not a page;
// this tells VitePress's link-rewriting to leave it (and anything else with
// this extension) alone.
//
// Set in *two* places, redundantly, on purpose: `package.json`'s scripts set
// this as a real shell env var (`VITE_EXTRA_EXTENSIONS=rav vitepress ...`),
// which is what actually matters for `vitepress dev` -- the extension list
// is a lazily-initialized, process-lifetime-cached value, computed on first
// use, so a mutation here can lose the race against whatever markdown gets
// rendered first during dev-server startup. Setting it before the process
// even starts avoids that race entirely. The assignment here is a fallback,
// for the (currently theoretical) case of someone invoking `vitepress`
// directly rather than through the npm scripts -- harmless either way, and
// `.env` files don't help here, since they aren't auto-loaded into the
// Node-side build process the way they are for client code.
process.env.VITE_EXTRA_EXTENSIONS = 'rav'

// Vendored from raven-lang/syntaxes/raven.tmLanguage.json (the same grammar
// that drives syntax highlighting in the VS Code extension) so that code
// blocks in the tutorial render identically to what a reader sees in their
// own editor. If the VS Code extension's grammar changes, re-copy it here --
// there's no automated sync yet.
const ravenGrammarPath = fileURLToPath(
  new URL('./raven.tmLanguage.json', import.meta.url)
)
const ravenGrammar = JSON.parse(readFileSync(ravenGrammarPath, 'utf-8'))
ravenGrammar.aliases = ['raven']

// GitHub Pages serves this site from https://nyu-acsys.github.io/raven/ --
// a subpath, not the domain root -- so every root-relative URL needs a
// '/raven/' prefix there. Locally (`npm run dev`/`preview`), there's no
// subpath, so base stays '/'. The deploy workflow (.github/workflows/
// deploy-docs.yml) sets GITHUB_PAGES=true for the production build only.
const base = process.env.GITHUB_PAGES ? '/raven/' : '/'

export default defineConfig({
  // The site root is `docs/` itself: `index.md` is the project landing page and the
  // tutorial lives under `tutorial/`, so it is served at /tutorial/ rather than at the
  // root. Everything else in this directory is build machinery rather than content.
  srcExclude: ['node_modules/**', 'scripts/**', 'ext/**'],
  title: 'Raven',
  description:
    'An intermediate verification language and SMT-based deductive verifier for concurrent programs.',
  base,

  head: [
    ['link', { rel: 'icon', type: 'image/png', href: `${base}favicon.png` }]
  ],

  markdown: {
    languages: [ravenGrammar]
  },

  // `.rav` files are real source, linked directly from the prose (e.g.
  // `./hit_counter_pure.rav`) so a reader can open the exact code being
  // discussed -- but they aren't VitePress pages, so the dead-link checker
  // doesn't know about them. `scripts/sync-rav.mjs` (run via `predev`/
  // `prebuild`) mirrors every `.rav` file into `public/` at the same
  // relative path, which is what actually makes these links resolve when
  // clicked; this just tells the checker they're expected.
  ignoreDeadLinks: [/\.rav$/],

  themeConfig: {
    logo: '/logo.png',

    nav: [
      { text: 'Tutorial', link: '/tutorial/' },
      { text: 'Get Started', link: '/tutorial/00-getting-started/' },
      { text: 'GitHub', link: 'https://github.com/nyu-acsys/raven' }
    ],

    // Scoped to /tutorial/ so the tutorial's contents don't follow the reader onto the
    // landing page or any other top-level page added later.
    sidebar: {
      '/tutorial/': [
      {
        text: 'The Raven Tutorial',
        items: [{ text: 'Contents', link: '/tutorial/' }]
      },
      {
        text: '0. Getting Started',
        link: '/tutorial/00-getting-started/',
        collapsed: true,
        items: [
          { text: 'Install', link: '/tutorial/00-getting-started/#install' },
          { text: 'Your first .rav file', link: '/tutorial/00-getting-started/#your-first-rav-file' },
          { text: 'Breaking it on purpose', link: '/tutorial/00-getting-started/#breaking-it-on-purpose' },
          { text: 'Two kinds of red', link: '/tutorial/00-getting-started/#two-kinds-of-red' },
          { text: 'Debugging Corner', link: '/tutorial/00-getting-started/#debugging-corner-reading-what-the-editor-tells-you' },
          { text: "What's next", link: "/00-getting-started/#what-s-next" }
        ]
      },
      {
        text: '1. Sequential Raven',
        link: '/tutorial/01-sequential/',
        collapsed: true,
        items: [
          { text: '1. Values and types', link: '/tutorial/01-sequential/#_1-values-and-types' },
          { text: '2. func vs. proc', link: '/tutorial/01-sequential/#_2-functions-func-vs-procedures-proc' },
          { text: '3. Contracts on pure code', link: '/tutorial/01-sequential/#_3-contracts-on-pure-code' },
          { text: '4. Control flow', link: '/tutorial/01-sequential/#_4-control-flow-recursion-and-loops' },
          { text: '5. A more interesting termination measure', link: '/tutorial/01-sequential/#_5-a-more-interesting-termination-measure' },
          { text: '6. Algebraic data types', link: '/tutorial/01-sequential/#_6-algebraic-data-types' },
          { text: '7. Quantifiers, briefly', link: '/tutorial/01-sequential/#_7-quantifiers-briefly' },
          { text: 'Why this matters for concurrency', link: '/tutorial/01-sequential/#why-this-matters-for-concurrency' },
          { text: 'Debugging Corner', link: '/tutorial/01-sequential/#debugging-corner' },
          { text: 'Exercises', link: '/tutorial/01-sequential/#exercises' },
          { text: "What's next", link: "/01-sequential/#what-s-next" }
        ]
      },
      {
        text: '2. Ownership and Resources',
        link: '/tutorial/02-ownership/',
        collapsed: true,
        items: [
          { text: '1. Fields and the heap', link: '/tutorial/02-ownership/#_1-fields-and-the-heap' },
          { text: '2. own is a resource, not a fact', link: '/tutorial/02-ownership/#_2-own-is-a-resource-not-a-fact' },
          { text: '3. Separating conjunction', link: '/tutorial/02-ownership/#_3-separating-conjunction' },
          { text: '4. Fractional permissions', link: '/tutorial/02-ownership/#_4-fractional-permissions' },
          { text: '5. Procedure contracts, revisited', link: '/tutorial/02-ownership/#_5-procedure-contracts-revisited' },
          { text: '6. Anti-aliasing, for free', link: '/tutorial/02-ownership/#_6-anti-aliasing-for-free' },
          { text: 'Why this matters for concurrency', link: '/tutorial/02-ownership/#why-this-matters-for-concurrency' },
          { text: 'Debugging Corner', link: '/tutorial/02-ownership/#debugging-corner' },
          { text: 'Exercises', link: '/tutorial/02-ownership/#exercises' },
          { text: "What's next", link: "/02-ownership/#what-s-next" }
        ]
      },
      {
        text: '3. The Module System',
        link: '/tutorial/03-modules/',
        collapsed: true,
        items: [
          { text: '1. Interfaces and modules', link: '/tutorial/03-modules/#_1-interfaces-and-modules' },
          { text: '2. Implementing an interface', link: '/tutorial/03-modules/#_2-implementing-an-interface' },
          { text: '3. Abstract predicates as a spec boundary', link: '/tutorial/03-modules/#_3-abstract-predicates-as-a-specification-boundary' },
          { text: '4. Lemmas and axioms', link: '/tutorial/03-modules/#_4-lemmas-and-axioms' },
          { text: '5. Functors', link: '/tutorial/03-modules/#_5-functors' },
          { text: '6. import', link: '/tutorial/03-modules/#_6-import' },
          { text: '7. Rolling your own well-founded order', link: '/tutorial/03-modules/#_7-rolling-your-own-well-founded-order' },
          { text: 'Why this matters for concurrency', link: '/tutorial/03-modules/#why-this-matters-for-concurrency' },
          { text: 'Debugging Corner', link: '/tutorial/03-modules/#debugging-corner' },
          { text: 'Exercise', link: '/tutorial/03-modules/#exercise' },
          { text: "What's next", link: "/03-modules/#what-s-next" }
        ]
      },
      {
        text: '4. Ghost Code and Basic Concurrency',
        link: '/tutorial/04-ghost-and-concurrency/',
        collapsed: true,
        items: [
          { text: '1–2. Threads and atomic primitives', link: '/tutorial/04-ghost-and-concurrency/#_1–2-threads-and-atomic-primitives' },
          { text: '3. The problem shared invariants solve', link: '/tutorial/04-ghost-and-concurrency/#_3-the-problem-shared-invariants-solve' },
          { text: '4. Shared invariants', link: '/tutorial/04-ghost-and-concurrency/#_4-shared-invariants' },
          { text: '5. Ghost fields and resource algebras', link: '/tutorial/04-ghost-and-concurrency/#_5-ghost-fields-and-resource-algebras' },
          { text: '6. Frame-preserving updates', link: '/tutorial/04-ghost-and-concurrency/#_6-frame-preserving-updates' },
          { text: 'Why this matters going forward', link: '/tutorial/04-ghost-and-concurrency/#why-this-matters-going-forward' },
          { text: 'Debugging Corner', link: '/tutorial/04-ghost-and-concurrency/#debugging-corner' },
          { text: 'Exercise', link: '/tutorial/04-ghost-and-concurrency/#exercise' },
          { text: "What's next", link: "/04-ghost-and-concurrency/#what-s-next" }
        ]
      },
      {
        text: '5. Scaling Up',
        collapsed: true,
        items: [
          { text: 'Overview', link: '/tutorial/05-advanced/' },
          { text: '5a. Capstone: Fork/Join', link: '/tutorial/05-advanced/fork-join/' },
          { text: '5b. Atomic Contracts', link: '/tutorial/05-advanced/atomic-contracts/' },
          { text: '5c. Iterated Separating Conjunctions', link: '/tutorial/05-advanced/iterated-star/' },
          { text: '5d. Automation Features', link: '/tutorial/05-advanced/automation/' }
        ]
      },
      {
        text: 'Appendices',
        collapsed: true,
        items: [
          { text: 'A. Resource Algebras, Formally', link: '/tutorial/appendix/resource-algebras' },
          { text: 'B. Coming From Viper, Dafny, or Iris', link: '/tutorial/appendix/from-other-tools' },
          { text: 'C. The Extension API', link: '/tutorial/appendix/extension-api' },
          { text: 'D. Where to Go Next', link: '/tutorial/appendix/where-next' }
        ]
      }
      ]
    },

    socialLinks: [
      { icon: 'github', link: 'https://github.com/nyu-acsys/raven' }
    ]
  }
})
