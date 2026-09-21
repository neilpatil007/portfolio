/** @type {import('tailwindcss').Config} */
export default {
  content: [
    "./index.html",
    "./src/**/*.{js,jsx,ts,tsx}",
  ],
  theme: {
    extend: {
      fontFamily: {
        calendas: ['"Calendas Plus"', 'serif'],
        azeretMono: ['"Azeret Mono"', 'monospace'],
      },
    },
  },
  plugins: [],
}
