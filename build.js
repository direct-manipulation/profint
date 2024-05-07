import * as esbuild from "esbuild";
import path from "node:path";
import * as fs from "node:fs";

const demoDir = "demo";
const pubDir = path.join(demoDir, "public");

let woffResolver = {
  name: "woff-resolver",
  setup(build) {
    let woffFiles = new Map();
    build.onResolve({ filter: /\.woff2?$/ }, args => {
      woffFiles.set(args.path, args.resolveDir);
      return {
        external: true,
        path: path.join("public", args.path),
      };
    });
    build.onEnd(result => {
      if (woffFiles.size > 0) {
        fs.mkdirSync(pubDir, { recursive: true });
        woffFiles.forEach((wDir, wName) => {
          const src = path.join(wDir, wName);
          const dst = path.join(pubDir, wName);
          fs.copyFileSync(src, dst);
        });
      }
    });
  },
}

await esbuild.build({
  entryPoints: ["src/demo/demo.js"],
  bundle: true,
  outfile: path.join(demoDir, "demo.js"),
  format: "esm",
  plugins: [woffResolver],
  logLevel: "info",
});
