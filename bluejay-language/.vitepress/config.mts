import { defineConfig } from 'vitepress'
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const __dirname = dirname(fileURLToPath(import.meta.url))

// https://vitepress.dev/reference/site-config
export default defineConfig({
    title: "Bluejay",
    srcDir: resolve(__dirname, '../../docs'),
    base: "/",
    description: "Next level type safety",
    themeConfig: {
        // https://vitepress.dev/reference/default-theme-config
        nav: [
            { text: 'Home', link: '/' },
            { text: "API Reference", link: "/_html/index.html", target: "_blank" }
        ],

        sidebar: [
            {
                text: "Language",
                items: [
                    { text: "Bluejay", link: "/language/bluejay" }
                ]
            },
            {
                text: 'Implementation',
                items: [
                    { text: 'Z3', link: '/implementation/z3' },
                    { text: 'SMT', link: '/implementation/smt' },
                ]
            },
            {
                text: "Spec",
                items: [
                    { text: "Commentary", link: "/spec/commentary" },
                    { text: "Desugar", link: "/spec/desugar" },
                    { text: "Embed", link: "/spec/embed" },
                    { text: "Type Erasure", link: "/spec/type_erasure" },
                ]
            }
        ],

        socialLinks: [
            { icon: 'github', link: 'https://github.com/vuejs/vitepress' }
        ]
    }
})
