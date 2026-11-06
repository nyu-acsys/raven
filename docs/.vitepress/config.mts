import { defineProjectSite, siteBase } from '@nyu-acsys/docs-kit/config'
import { sectionItems } from '@nyu-acsys/docs-kit/sections'
import project from './project.mjs'

const registry = project.sections.buildRegistry()
const { pages } = registry
const base = siteBase(project)

// Numbering comes from project.mjs; short navigation labels remain site-specific.
const SIDEBAR_LABELS: Record<string, string> = {
  'sec:install': 'Install',
  'sec:first-rav-file': "Your first .rav file",
  'sec:breaking-it-on-purpose': 'Breaking it on purpose',
  'sec:two-kinds-of-red': 'Two kinds of red',
  'sec:strict-mode': 'Strict mode: reviewing assumptions',

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
  'sec:sealing': 'Sealing modules',
  'sec:import': 'import',

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
  'sec:inline-predicates': 'More automation with inline predicates',

  'sec:linearizability-to-client': 'Linearizability, stated to a client',
  'sec:au-mechanics': 'The mechanics: bindAU/openAU/abortAU/commitAU',
  'sec:token-direct': 'Threading a token through a retry loop directly',
  'sec:composing-atomic-contracts': 'Composing atomic contracts',
  'sec:atomic-call-during-invariant-access': 'Atomic calls during invariant accesses',

  'sec:the-isc': 'The ISC',
  'sec:addressing': 'Addressing',
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
  'sec:auto-lemmas': 'auto lemmas',
  'sec:triggers-revisited': 'Triggers, revisited',
  'sec:inline': 'Inline predicates and functions',
  'sec:assert-with': 'assert ... with',

  'sec:ra-definition': 'The definition',
  'sec:ra-interface': 'The interface a custom RA implements',
  'sec:ra-worked-examples': 'Worked examples: Excl and DisjSet',

  'sec:what-the-library-gives': 'What the library gives you',
  'sec:anatomy': 'Anatomy of a primitive',
  'sec:fetch-and-max': 'Worked example: fetch-and-max',
  'sec:dcas': 'Worked example: two locations at once',
  'sec:atomic-block-standalone': 'atomic { } on its own',
  'sec:stdlib-instances': 'Getting an instance',
  'sec:stdlib-option': 'Options',
  'sec:stdlib-list': 'Lists',
  'sec:stdlib-seq': 'Sequences',
  'sec:stdlib-array': 'Arrays',
  'sec:module-inference-details': 'Eligibility and inference',
  'sec:module-instance-identity': 'Instance identity',
  'sec:module-generative-factories': 'Generative factories',
  'sec:module-default-values': 'Generic default values',
  'sec:module-type-arguments': 'Types as interface arguments',
  'sec:module-sealed-views': 'Sealing modules and individual instances',
  'sec:module-checked-views': 'Checked module views',
  'sec:overload-resolution': 'Choosing a definition',
  'sec:overload-imports': 'Imports and shadowing',
  'sec:overload-symbols': 'Symbolic infix functions',
  'sec:overload-operators': 'Fixed operator notation',
  'sec:overload-patterns': 'Index, range, and update patterns',
  'sec:overload-literals': 'Enumeration literals',
  'sec:ackermann-termination': "Ackermann's lexicographic measure",
  'sec:well-founded-order': 'Defining a custom order',
  'sec:ghost-termination': 'Termination of ghost code',
  'sec:predicate-termination-measure': 'Structural predicate measures',
  'sec:trust-boundary': 'Where the trust boundary is',
  'sec:when-extension-api': 'When you need the Extension API',

  'sec:from-viper': 'From Viper',
  'sec:from-dafny': 'From Dafny',
  'sec:from-iris': 'From Iris'
}

// Short sidebar labels for the appendices, whose letters come from the registry.
const APPENDIX_LABELS: Record<string, string> = {
  'app:resource-algebras': 'Resource Algebras, Formally',
  'app:hardware-primitives': 'Adding a Hardware Primitive',
  'app:from-other-tools': 'Coming From Viper, Dafny, or Iris',
  'app:extension-api': 'The Extension API',
  'app:stdlib-types': 'Standard Library Data Types',
  'app:advanced-modules': 'Advanced Module Features',
  'app:automation': 'Automation Features',
  'app:overloading': 'Function and Operator Overloading',
  'app:well-founded-orders': 'Well-Founded Orders',
  'app:where-next': 'Where to Go Next'
}

function numberedItems(pageKey: string) {
  return sectionItems(registry, pageKey, SIDEBAR_LABELS)
}

function appendixItems() {
  return Object.entries(pages)
    .sort(([, p1]: any, [, p2]: any) => p1.label.localeCompare(p2.label))
    .map(([id, page]: [string, any]) => {
      const label = APPENDIX_LABELS[id]
      if (!label) throw new Error(`No APPENDIX_LABELS entry for ${id} -- add one in config.mts`)
      const item = { text: `${page.label}. ${label}`, link: page.path.replace(/\.html$/, '') }
      const items = numberedItems(page.path)
      if (id === 'app:automation') {
        items.push({ text: 'Debugging Corner', link: `${page.path}#debugging-corner-my-proof-just-hangs` })
      }
      return items.length > 0 ? { ...item, collapsed: true, items } : item
    })
}

export default defineProjectSite(project, {
  srcExclude: ['ext/**'],
  title: 'Raven',
  description:
    'An intermediate verification language and SMT-based deductive verifier for concurrent programs.',
  head: [
    ['link', { rel: 'icon', type: 'image/png', href: `${base}favicon.png` }]
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
            text: '5.1. Resource Algebras in Practice',
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
            text: '5.4. Prophecies',
            link: '/tutorial/advanced/prophecies/',
            collapsed: true,
            items: [
              ...numberedItems('/tutorial/advanced/prophecies/'),
              { text: 'Beyond counters: the same protocol elsewhere', link: '/tutorial/advanced/prophecies/#beyond-counters-the-same-protocol-elsewhere' },
              { text: 'Debugging Corner', link: '/tutorial/advanced/prophecies/#debugging-corner' },
              { text: "What's next", link: '/tutorial/advanced/prophecies/#what-s-next' }
            ]
          }
        ]
      },
      {
        text: 'Appendices',
        collapsed: true,
        items: appendixItems()
      }
      ]
    },

    socialLinks: [
      { icon: 'github', link: 'https://github.com/nyu-acsys/raven' }
    ]
  }
})
