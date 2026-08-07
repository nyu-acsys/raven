import { defineConfig } from 'vitepress'
import { existsSync, readFileSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { installSectionRefs } from './section-refs.mts'

// The same registry that drives in-page numbering and {{ref}} (see
// section-refs.mts) also drives the sidebar's numbered entries below, so a
// section's number and anchor can never drift out of sync between the two --
// the failure mode that kept recurring by hand before this existed. Only the
// *label* stays hand-picked: a heading's full title is sometimes too long or
// too markdown-heavy (backticks, parentheses) for a nav item, so
// `SIDEBAR_LABELS` supplies the short running head instead; `numberedItems`
// throws if a numbered section is missing one, so an added section can't
// silently end up with no sidebar entry.
const sectionRegistryPath = fileURLToPath(new URL('./section-registry.json', import.meta.url))
const { sections, pagesOrder } = JSON.parse(readFileSync(sectionRegistryPath, 'utf-8'))

const SIDEBAR_LABELS: Record<string, string> = {
  'sec:install': 'Install',
  'sec:first-rav-file': "Your first .rav file",
  'sec:breaking-it-on-purpose': 'Breaking it on purpose',
  'sec:two-kinds-of-red': 'Two kinds of red',

  'sec:values-and-types': 'Values and types',
  'sec:func-vs-proc': 'func vs. proc',
  'sec:contracts-pure-code': 'Contracts on pure code',
  'sec:control-flow': 'Control flow',
  'sec:termination-measure': 'A more interesting termination measure',
  'sec:algebraic-data-types': 'Algebraic data types',
  'sec:quantifiers': 'Quantifiers, briefly',

  'sec:fields-and-heap': 'Fields and the heap',
  'sec:own-resource-not-fact': 'own is a resource, not a fact',
  'sec:separating-conjunction': 'Separating conjunction',
  'sec:fractional-permissions': 'Fractional permissions',
  'sec:proc-contracts-revisited': 'Procedure contracts, revisited',
  'sec:anti-aliasing': 'Anti-aliasing, for free',
  'sec:bundling-pred': 'Bundling resources with pred',

  'sec:interfaces-and-modules': 'Interfaces and modules',
  'sec:implementing-interface': 'Implementing an interface',
  'sec:abstract-predicates': 'Abstract predicates as a spec boundary',
  'sec:lemmas-and-axioms': 'Lemmas and axioms',
  'sec:functors': 'Functors',
  'sec:implicit-functor-instantiation': 'Implicit functor instantiation',
  'sec:import': 'import',
  'sec:well-founded-order': 'Rolling your own well-founded order',

  'sec:threads-and-atomics': 'Threads and atomic primitives',
  'sec:shared-invariants-problem': 'The problem shared invariants solve',
  'sec:shared-invariants': 'Shared invariants',
  'sec:ghost-fields-resource-algebras': 'Ghost fields and resource algebras',
  'sec:frame-preserving-updates': 'Frame-preserving updates',
  'sec:ghost-blocks-erasure': 'Ghost blocks and the erasure guarantee',

  'sec:shape-of-problem': 'The shape of the problem',
  'sec:plan-transferring-ownership': 'A plan for transferring ownership',
  'sec:why-it-fails': 'Why it fails',
  'sec:idea-a-token': 'The idea: a token',
  'sec:making-token-real': 'Making the token real',
  'sec:auto-predicates': 'More automation with auto predicates',

  'sec:linearizability-to-client': 'Linearizability, stated to a client',
  'sec:au-mechanics': 'The mechanics: bindAU/openAU/abortAU/commitAU',
  'sec:token-direct': 'Threading a token through a retry loop directly',
  'sec:composing-atomic-contracts': 'Composing atomic contracts',

  'sec:the-isc': 'The ISC',
  'sec:addressing-abstract': "Addressing, and why it's abstract",
  'sec:injectivity-side-condition': 'The injectivity side condition',
  'sec:touching-one-slot': 'Touching one slot, without disturbing the rest',

  'sec:predicting-the-future': "Predicting a value that hasn't been decided yet",
  'sec:reading-the-coin': "A coin that already knows its own answer",
  'sec:future-dependent-linearization': 'A linearization point that depends on the future',
  'sec:the-helping-protocol': 'The helping protocol',
  'sec:counter-invariant': 'The counter\'s invariant, and an ISC over a set',
  'sec:get-predict-register': 'get: predict, register, maybe finish on the spot',
  'sec:bump-all-helping': 'incr and bump_all: helping on someone else\'s behalf',

  'sec:implicit-parameters': 'Implicit parameters',
  'sec:implicit-ghost-parameters': 'Implicit ghost parameters',
  'sec:witness-computation': 'Witness computation',
  'sec:bind-statement': 'The bind statement',
  'sec:auto-lemmas-predicates': 'auto lemmas and predicates',
  'sec:triggers-revisited': 'Triggers, revisited',
  'sec:assert-with': 'assert ... with',

  'sec:ra-definition': 'The definition',
  'sec:ra-interface': 'The interface a custom RA implements',
  'sec:ra-worked-examples': 'Worked examples: Excl and DisjSet',

  'sec:from-viper': 'From Viper',
  'sec:from-dafny': 'From Dafny',
  'sec:from-iris': 'From Iris'
}

function numberedItems(pageKey: string) {
  const ids: string[] = pagesOrder[pageKey] ?? []
  return ids.map((id) => {
    const section = sections[id]
    const label = SIDEBAR_LABELS[id]
    if (!label) throw new Error(`No SIDEBAR_LABELS entry for ${id} (${pageKey}) -- add one in config.mts`)
    return { text: `${section.number}. ${label}`, link: `${pageKey}#${section.anchor}` }
  })
}

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
    languages: [ravenGrammar],
    config: (md) => installSectionRefs(md, { base })
  },

  // `.rav` files are real source, linked directly from the prose (e.g.
  // `./hit_counter_pure.rav`) so a reader can open the exact code being
  // discussed -- but they aren't VitePress pages, so the dead-link checker
  // doesn't know about them. `scripts/sync-rav.mjs` (run via `predev`/
  // `prebuild`) mirrors every `.rav` file into `public/` at the same
  // relative path, which is what actually makes these links resolve when
  // clicked; this just tells the checker they're expected.
  //
  // The second entry works around a real bug in VitePress 1.6.4's own dead-link
  // checker (independent of the vite/esbuild overrides above -- reproduced with
  // vite reverted to the version VitePress declares support for): for a
  // directory-style link (this tutorial's normal cross-chapter convention, e.g.
  // `[Part 3](../modules/)`), the already `base`-prefixed, rendered href (e.g.
  // `/raven/tutorial/modules/`) gets `index` appended and then only its leading
  // `/` stripped before being checked against `pages`, which are `base`-agnostic
  // -- so the `base` segment (`raven`) is still in there, `pages` never
  // contains it, and every such link is misreported as dead, but only on a
  // `base: '/raven/'` build (`GITHUB_PAGES=true`), which local `npm run build`
  // doesn't exercise. Re-verifies the link itself (strips `base` and the
  // trailing `/index` back to a real directory under `tutorial/`) rather than
  // ignoring anything of this shape, so a genuinely dead folder link still
  // fails the build. Worth removing on the next VitePress upgrade, once fixed
  // upstream.
  ignoreDeadLinks: [
    /\.rav$/,
    (url: string) => {
      if (!url.startsWith(base) || !url.endsWith('/index')) return false
      const dir = url.slice(base.length, -'/index'.length)
      return existsSync(fileURLToPath(new URL(`../${dir}/index.md`, import.meta.url)))
    }
  ],

  themeConfig: {
    logo: '/logo-small.png',

    nav: [
      { text: 'Tutorial', link: '/tutorial/' },
      { text: 'Get Started', link: '/tutorial/getting-started/' },
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
        link: '/tutorial/getting-started/',
        collapsed: true,
        items: [
          ...numberedItems('/tutorial/getting-started/'),
          { text: 'Debugging Corner', link: '/tutorial/getting-started/#debugging-corner-reading-what-the-editor-tells-you' },
          { text: "What's next", link: "/tutorial/getting-started/#what-s-next" }
        ]
      },
      {
        text: '1. Sequential Raven',
        link: '/tutorial/sequential/',
        collapsed: true,
        items: [
          ...numberedItems('/tutorial/sequential/'),
          { text: 'Why this matters for concurrency', link: '/tutorial/sequential/#why-this-matters-for-concurrency' },
          { text: 'Debugging Corner', link: '/tutorial/sequential/#debugging-corner' },
          { text: 'Exercises', link: '/tutorial/sequential/#exercises' },
          { text: "What's next", link: "/tutorial/sequential/#what-s-next" }
        ]
      },
      {
        text: '2. Ownership and Resources',
        link: '/tutorial/ownership/',
        collapsed: true,
        items: [
          ...numberedItems('/tutorial/ownership/'),
          { text: 'Why this matters for concurrency', link: '/tutorial/ownership/#why-this-matters-for-concurrency' },
          { text: 'Debugging Corner', link: '/tutorial/ownership/#debugging-corner' },
          { text: 'Exercises', link: '/tutorial/ownership/#exercises' },
          { text: "What's next", link: "/tutorial/ownership/#what-s-next" }
        ]
      },
      {
        text: '3. The Module System',
        link: '/tutorial/modules/',
        collapsed: true,
        items: [
          ...numberedItems('/tutorial/modules/'),
          { text: 'Why this matters for concurrency', link: '/tutorial/modules/#why-this-matters-for-concurrency' },
          { text: 'Debugging Corner', link: '/tutorial/modules/#debugging-corner' },
          { text: 'Exercise', link: '/tutorial/modules/#exercise' },
          { text: "What's next", link: "/tutorial/modules/#what-s-next" }
        ]
      },
      {
        text: '4. Ghost Code and Basic Concurrency',
        link: '/tutorial/ghost-and-concurrency/',
        collapsed: true,
        items: [
          ...numberedItems('/tutorial/ghost-and-concurrency/'),
          { text: 'Why this matters going forward', link: '/tutorial/ghost-and-concurrency/#why-this-matters-going-forward' },
          { text: 'Debugging Corner', link: '/tutorial/ghost-and-concurrency/#debugging-corner' },
          { text: 'Exercise', link: '/tutorial/ghost-and-concurrency/#exercise' },
          { text: "What's next", link: "/tutorial/ghost-and-concurrency/#what-s-next" }
        ]
      },
      {
        text: '5. Scaling Up',
        collapsed: true,
        items: [
          { text: 'Overview', link: '/tutorial/advanced/' },
          {
            text: '5.1. Capstone: Fork/Join',
            link: '/tutorial/advanced/fork-join/',
            collapsed: true,
            items: [
              ...numberedItems('/tutorial/advanced/fork-join/'),
              { text: 'Why this matters for concurrency', link: '/tutorial/advanced/fork-join/#why-this-matters-for-concurrency' },
              { text: "What's next", link: '/tutorial/advanced/fork-join/#what-s-next' }
            ]
          },
          {
            text: '5.2. Atomic Contracts',
            link: '/tutorial/advanced/atomic-contracts/',
            collapsed: true,
            items: [
              ...numberedItems('/tutorial/advanced/atomic-contracts/'),
              { text: 'Debugging Corner', link: '/tutorial/advanced/atomic-contracts/#debugging-corner' },
              { text: "What's next", link: '/tutorial/advanced/atomic-contracts/#what-s-next' }
            ]
          },
          {
            text: '5.3. Iterated Separating Conjunctions',
            link: '/tutorial/advanced/iterated-star/',
            collapsed: true,
            items: [
              ...numberedItems('/tutorial/advanced/iterated-star/'),
              { text: 'Debugging Corner', link: '/tutorial/advanced/iterated-star/#debugging-corner' },
              { text: 'Exercise', link: '/tutorial/advanced/iterated-star/#exercise' },
              { text: "What's next", link: '/tutorial/advanced/iterated-star/#what-s-next' }
            ]
          },
          {
            text: '5.4. Capstone: Prophecies',
            link: '/tutorial/advanced/prophecies/',
            collapsed: true,
            items: [
              ...numberedItems('/tutorial/advanced/prophecies/'),
              { text: 'Beyond counters: the same protocol elsewhere', link: '/tutorial/advanced/prophecies/#beyond-counters-the-same-protocol-elsewhere' },
              { text: 'Debugging Corner', link: '/tutorial/advanced/prophecies/#debugging-corner' },
              { text: "What's next", link: '/tutorial/advanced/prophecies/#what-s-next' }
            ]
          },
          {
            text: '5.5. Automation Features',
            link: '/tutorial/advanced/automation/',
            collapsed: true,
            items: [
              ...numberedItems('/tutorial/advanced/automation/'),
              { text: 'Debugging Corner', link: '/tutorial/advanced/automation/#debugging-corner-my-proof-just-hangs' },
              { text: "What's next", link: '/tutorial/advanced/automation/#what-s-next' }
            ]
          }
        ]
      },
      {
        text: 'Appendices',
        collapsed: true,
        items: [
          {
            text: 'A. Resource Algebras, Formally',
            link: '/tutorial/appendix/resource-algebras',
            collapsed: true,
            items: numberedItems('/tutorial/appendix/resource-algebras.html')
          },
          {
            text: 'B. Coming From Viper, Dafny, or Iris',
            link: '/tutorial/appendix/from-other-tools',
            collapsed: true,
            items: numberedItems('/tutorial/appendix/from-other-tools.html')
          },
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
