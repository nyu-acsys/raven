// Extends the default theme purely to load custom.css -- no component
// overrides. This is the standard, documented way to add site-wide CSS to
// VitePress without forking any part of the default theme.
import DefaultTheme from 'vitepress/theme'
import './custom.css'

export default DefaultTheme
