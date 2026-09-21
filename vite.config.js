import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'
import path from 'path'
import uploadPlugin from './vite-upload-plugin.js'

// https://vite.dev/config/
export default defineConfig({
  plugins: [react(), uploadPlugin()],
  resolve: {
    alias: {
      '@': path.resolve(__dirname, './src'),
    },
  },
  server: {
    host: '0.0.0.0',
    port: 4040,
  },
  preview: {
    host: '0.0.0.0',
    port: 4040,
    allowedHosts: ['portfolio.techpenta.com'],
  },
})
