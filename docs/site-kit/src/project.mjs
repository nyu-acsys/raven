export function sourceExtensions(project) {
  const extensions = project.sourceExtensions ?? []
  if (!extensions.every(extension => typeof extension === 'string' && /^[a-zA-Z0-9]+$/.test(extension))) {
    throw new Error('Source extensions must be names without a leading dot')
  }
  return [...new Set(extensions)]
}

export function siteBase(project, pages = process.env.GITHUB_PAGES === 'true') {
  const base = pages ? project.pagesBase : '/'
  if (typeof base !== 'string' || !/^\/(?:[^/]+\/)*$/.test(base)
    || base.split('/').some(part => part === '.' || part === '..' || /[?#%\\]/.test(part))) {
    throw new Error('The Pages base must be an absolute URL path ending in /')
  }
  return base
}
