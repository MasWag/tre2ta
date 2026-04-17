import fs from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";

import { marked } from "marked";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, "..", "..");
const sourcePath = path.join(repoRoot, "doc", "construction.md");
const outputPath = process.argv[2]
  ? path.resolve(process.argv[2])
  : path.join(repoRoot, "site", "construction", "index.html");

const markdown = await fs.readFile(sourcePath, "utf8");
const content = marked.parse(markdown);

const html = `<!doctype html>
<html lang="en">
  <head>
    <meta charset="UTF-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1.0" />
    <title>tre2ta construction</title>
    <style>
      :root {
        color-scheme: light;
        font-family: "Iowan Old Style", "Palatino Linotype", "URW Palladio L", serif;
        line-height: 1.6;
        background: #f6f2e7;
        color: #1f1a14;
      }

      * {
        box-sizing: border-box;
      }

      body {
        margin: 0;
        padding: 3rem 1.25rem 4rem;
        background:
          radial-gradient(circle at top, rgba(153, 109, 61, 0.12), transparent 32rem),
          #f6f2e7;
      }

      main {
        max-width: 54rem;
        margin: 0 auto;
        padding: 2rem 2.2rem;
        background: rgba(255, 252, 245, 0.92);
        border: 1px solid rgba(92, 61, 33, 0.18);
        border-radius: 18px;
        box-shadow: 0 20px 50px rgba(92, 61, 33, 0.08);
      }

      h1,
      h2,
      h3 {
        line-height: 1.2;
        margin-top: 1.8em;
      }

      h1 {
        margin-top: 0;
        font-size: clamp(2rem, 4vw, 2.7rem);
      }

      a {
        color: #8a3f10;
      }

      code,
      pre {
        font-family: "SFMono-Regular", "Menlo", "Consolas", monospace;
      }

      code {
        padding: 0.1rem 0.3rem;
        background: rgba(92, 61, 33, 0.08);
        border-radius: 4px;
      }

      pre {
        overflow-x: auto;
        padding: 1rem 1.1rem;
        background: #241b13;
        color: #f8efe5;
        border-radius: 10px;
      }

      pre code {
        padding: 0;
        background: transparent;
        color: inherit;
      }

      blockquote {
        margin: 1.2rem 0;
        padding-left: 1rem;
        border-left: 4px solid rgba(138, 63, 16, 0.3);
        color: #4d3f31;
      }

      table {
        width: 100%;
        border-collapse: collapse;
      }

      th,
      td {
        padding: 0.6rem;
        border: 1px solid rgba(92, 61, 33, 0.18);
        text-align: left;
      }
    </style>
  </head>
  <body>
    <main>
      ${content}
    </main>
  </body>
</html>
`;

await fs.mkdir(path.dirname(outputPath), { recursive: true });
await fs.writeFile(outputPath, html);
