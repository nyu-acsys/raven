import { copyFileSync, lstatSync, mkdirSync, readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs'
import { dirname, extname, isAbsolute, join, relative, resolve, sep } from 'node:path'

function contained(root, path) {
  const name = relative(root, path)
  return name === '' || (!isAbsolute(name) && name !== '..' && !name.startsWith(`..${sep}`))
}

function resolveWithin(root, name) {
  if (typeof name !== 'string' || name.length === 0 || isAbsolute(name)) {
    throw new Error(`Expected a relative example path: ${name}`)
  }
  const path = resolve(root, name)
  if (!contained(root, path)) throw new Error(`Example path escapes its root: ${name}`)
  return path
}

// Destination directories must not redirect generated writes through symlinks.
function checkDirectory(root, directory) {
  const components = relative(root, directory).split(sep).filter(Boolean)
  let path = root
  for (const component of components) {
    path = join(path, component)
    const stat = lstatSync(path, { throwIfNoEntry: false })
    if (stat) {
      if (stat.isSymbolicLink() || !stat.isDirectory()) {
        throw new Error(`Example destination is not an ordinary directory: ${path}`)
      }
    }
  }
}

function readManifest(siteRoot, publicRoot, path) {
  const stat = lstatSync(path, { throwIfNoEntry: false })
  if (!stat) return []
  if (!stat.isFile()) throw new Error('Example manifest must be an ordinary file')
  const manifest = JSON.parse(readFileSync(path, 'utf8'))
  if (manifest?.version !== 1 || !Array.isArray(manifest.files)) {
    throw new Error('Invalid example manifest')
  }
  if (manifest.publicDir !== relative(siteRoot, publicRoot).split(sep).join('/')) {
    throw new Error('Example manifest belongs to another public directory')
  }
  return [...new Set(manifest.files.map(name => {
    const path = resolveWithin(publicRoot, name)
    if (path === publicRoot) {
      throw new Error(`Invalid generated example path: ${name}`)
    }
    return relative(publicRoot, path).split(sep).join('/')
  }))]
}

/** Mirror selected example files, keeping their site-relative paths and removing stale generated copies. */
export function syncExamples({ root, sources, extensions, publicDir = 'public', manifest = '.vitepress/examples-manifest.json', adoptIdentical = false }) {
  if (typeof root !== 'string' || !Array.isArray(sources) || !Array.isArray(extensions)) {
    throw new Error('Example mirroring requires root, sources and extensions')
  }
  const siteRoot = resolve(root)
  if (!lstatSync(siteRoot).isDirectory()) throw new Error('Example root must be an ordinary directory')
  const publicRoot = resolveWithin(siteRoot, publicDir)
  if (publicRoot === siteRoot) throw new Error('Example public directory must be below the site root')
  const allowed = new Set(extensions.map(extension => {
    if (typeof extension !== 'string' || !/^\.?[a-zA-Z0-9][a-zA-Z0-9_-]*$/.test(extension)) {
      throw new Error(`Invalid example extension: ${extension}`)
    }
    return extension.startsWith('.') ? extension : `.${extension}`
  }))
  const roots = sources.map(source => {
    const path = resolveWithin(siteRoot, source)
    if (path === siteRoot || contained(path, publicRoot) || contained(publicRoot, path)) {
      throw new Error(`Example source overlaps the site root or public directory: ${source}`)
    }
    return path
  })
  const manifestPath = resolveWithin(siteRoot, manifest)
  if (manifestPath === siteRoot || contained(publicRoot, manifestPath) || roots.some(source => contained(source, manifestPath))) {
    throw new Error('Example manifest must be outside source and public directories')
  }
  checkDirectory(siteRoot, publicRoot)
  checkDirectory(siteRoot, dirname(manifestPath))
  const files = new Map()
  function visit(path) {
    const stat = lstatSync(path)
    if (stat.isSymbolicLink()) return
    if (stat.isDirectory()) {
      for (const name of readdirSync(path).sort()) visit(join(path, name))
    } else if (stat.isFile() && allowed.has(extname(path))) {
      files.set(relative(siteRoot, path).split(sep).join('/'), path)
    }
  }
  for (const source of roots) {
    let ancestor = source
    let symlink = false
    while (ancestor !== siteRoot) {
      if (lstatSync(ancestor).isSymbolicLink()) { symlink = true; break }
      ancestor = dirname(ancestor)
    }
    if (!symlink) visit(source)
  }
  const previous = readManifest(siteRoot, publicRoot, manifestPath)
  const owned = new Set(previous)
  const current = [...files.keys()].sort()
  for (const name of new Set([...previous, ...current])) {
    const destination = resolveWithin(publicRoot, name)
    checkDirectory(publicRoot, dirname(destination))
    const stat = lstatSync(destination, { throwIfNoEntry: false })
    if (stat) {
      if (!stat.isFile()) throw new Error(`Example destination is not an ordinary file: ${name}`)
      if (!owned.has(name) && !(adoptIdentical && readFileSync(destination).equals(readFileSync(files.get(name))))) {
        throw new Error(`Refusing to replace an unmanaged public file: ${name}`)
      }
    }
  }
  mkdirSync(publicRoot, { recursive: true })
  for (const name of current) {
    const destination = resolveWithin(publicRoot, name)
    mkdirSync(dirname(destination), { recursive: true })
    copyFileSync(files.get(name), destination)
  }
  for (const name of previous) {
    if (!files.has(name)) rmSync(resolveWithin(publicRoot, name), { force: true })
  }
  mkdirSync(dirname(manifestPath), { recursive: true })
  writeFileSync(manifestPath, JSON.stringify({
    version: 1,
    publicDir: relative(siteRoot, publicRoot).split(sep).join('/'),
    files: current
  }, null, 2) + '\n')
  return current
}
