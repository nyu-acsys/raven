import assert from 'node:assert/strict'
import { existsSync, mkdirSync, mkdtempSync, readFileSync, renameSync, rmSync, symlinkSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { dirname, join } from 'node:path'
import test from 'node:test'
import { syncExamples } from '../src/examples.mjs'

function fixture(t) {
  const root = mkdtempSync(join(tmpdir(), 'site-kit-examples-'))
  t.after(() => rmSync(root, { recursive: true, force: true }))
  function write(name, text) {
    const path = join(root, name)
    mkdirSync(dirname(path), { recursive: true })
    writeFileSync(path, text)
  }
  return { root, write, sync: options => syncExamples({ root, sources: ['tutorial'], extensions: ['rav'], ...options }) }
}

test('mirrors selected examples and updates only manifest-owned outputs', t => {
  const f = fixture(t)
  f.write('tutorial/first.rav', 'first')
  f.write('tutorial/chapter/second.rav', 'second')
  f.write('tutorial/chapter/index.md', 'not a download')
  f.write('public/manual.rav', 'unmanaged Raven source')
  f.write('public/handwritten.ml', 'unmanaged OCaml source')
  const names = ['tutorial/chapter/second.rav', 'tutorial/first.rav']
  assert.deepEqual(f.sync(), names)
  assert.deepEqual(f.sync(), names)
  assert.equal(readFileSync(join(f.root, 'public/tutorial/chapter/second.rav'), 'utf8'), 'second')
  assert.equal(existsSync(join(f.root, 'public/tutorial/chapter/index.md')), false)
  renameSync(join(f.root, 'tutorial/first.rav'), join(f.root, 'tutorial/renamed.rav'))
  f.write('tutorial/chapter/second.rav', 'edited')
  assert.deepEqual(f.sync(), ['tutorial/chapter/second.rav', 'tutorial/renamed.rav'])
  assert.equal(existsSync(join(f.root, 'public/tutorial/first.rav')), false)
  assert.equal(readFileSync(join(f.root, 'public/tutorial/chapter/second.rav'), 'utf8'), 'edited')
  assert.deepEqual(f.sync({ sources: [] }), [])
  assert.equal(existsSync(join(f.root, 'public/tutorial/renamed.rav')), false)
  assert.equal(readFileSync(join(f.root, 'public/manual.rav'), 'utf8'), 'unmanaged Raven source')
  assert.equal(readFileSync(join(f.root, 'public/handwritten.ml'), 'utf8'), 'unmanaged OCaml source')
})

test('supports separate content roots, OCaml files and another public directory', t => {
  const f = fixture(t)
  f.write('guide/example.ml', 'implementation')
  f.write('guide/example.mli', 'interface')
  f.write('guide/example.proof', 'proof')
  f.write('guide/example.rav', 'excluded')
  f.write('examples/single.ml', 'another implementation')
  assert.deepEqual(f.sync({ sources: ['guide', 'examples/single.ml'], extensions: ['.ml', '.mli', '.proof'], publicDir: 'static' }), [
    'examples/single.ml', 'guide/example.ml', 'guide/example.mli', 'guide/example.proof'
  ])
  assert.equal(readFileSync(join(f.root, 'static/guide/example.proof'), 'utf8'), 'proof')
  assert.equal(existsSync(join(f.root, 'public')), false)
})

test('rejects traversal, overlapping roots and unmanaged destination collisions before writing', t => {
  const f = fixture(t)
  f.write('tutorial/first.rav', 'source')
  for (const sources of [['../outside'], [f.root], ['.'], ['public'], ['tutorial/public']]) {
    const options = sources[0] === 'tutorial/public' ? { publicDir: 'tutorial' } : {}
    assert.throws(() => f.sync({ sources, ...options }))
  }
  assert.throws(() => f.sync({ publicDir: '../outside' }))
  f.write('public/tutorial/first.rav', 'handwritten')
  assert.throws(() => f.sync(), /unmanaged public file/)
  assert.equal(readFileSync(join(f.root, 'public/tutorial/first.rav'), 'utf8'), 'handwritten')
  assert.equal(existsSync(join(f.root, '.vitepress/examples-manifest.json')), false)
})

test('rejects invalid manifest paths before deleting any files', t => {
  const f = fixture(t)
  f.write('tutorial/first.rav', 'source')
  f.write('outside.rav', 'preserved')
  f.write('.vitepress/examples-manifest.json', JSON.stringify({ version: 1, publicDir: 'public', files: ['../outside.rav'] }))
  assert.throws(() => f.sync(), /escapes its root/)
  assert.equal(readFileSync(join(f.root, 'outside.rav'), 'utf8'), 'preserved')
  assert.equal(existsSync(join(f.root, 'public/tutorial')), false)
})

test('keeps ownership tied to its public directory', t => {
  const f = fixture(t)
  f.write('tutorial/first.rav', 'source')
  f.sync()
  f.write('static/tutorial/first.rav', 'unmanaged')
  assert.throws(() => f.sync({ publicDir: 'static' }), /another public directory/)
  assert.equal(readFileSync(join(f.root, 'static/tutorial/first.rav'), 'utf8'), 'unmanaged')
})

test('adopts identical old generated files only when requested', t => {
  const f = fixture(t)
  f.write('tutorial/first.rav', 'identical')
  f.write('public/tutorial/first.rav', 'identical')
  assert.throws(() => f.sync(), /unmanaged public file/)
  assert.deepEqual(f.sync({ adoptIdentical: true }), ['tutorial/first.rav'])
  assert.equal(existsSync(join(f.root, 'public/.site-kit-examples.json')), false)
  assert.deepEqual(f.sync({ sources: [] }), [])
  assert.equal(existsSync(join(f.root, 'public/tutorial/first.rav')), false)

  f.write('public/tutorial/first.rav', 'different')
  assert.throws(() => f.sync({ adoptIdentical: true }), /unmanaged public file/)
  assert.equal(readFileSync(join(f.root, 'public/tutorial/first.rav'), 'utf8'), 'different')
})

test('skips source symlinks and rejects destination symlinks', { skip: process.platform === 'win32' }, t => {
  const f = fixture(t)
  f.write('tutorial/first.rav', 'source')
  f.write('other.rav', 'external source')
  symlinkSync(join(f.root, 'other.rav'), join(f.root, 'tutorial/linked.rav'))
  assert.deepEqual(f.sync(), ['tutorial/first.rav'])
  assert.equal(existsSync(join(f.root, 'public/tutorial/linked.rav')), false)
  rmSync(join(f.root, 'public/tutorial/first.rav'))
  symlinkSync(join(f.root, 'other.rav'), join(f.root, 'public/tutorial/first.rav'))
  assert.throws(() => f.sync(), /ordinary file/)
  assert.equal(readFileSync(join(f.root, 'other.rav'), 'utf8'), 'external source')
})
