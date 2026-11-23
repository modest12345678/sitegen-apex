# sitegen-apex

[![make.fun · site-generator-speed-01-run-20261122](https://make.fun/badge/site-generator-speed-01-run-20261122.svg)](https://make.fun/bounty/site-generator-speed-01-run-20261122?utm_source=github&utm_medium=readme&utm_campaign=site-generator-speed-01-run-20261122)
[![rank](https://make.fun/badge/site-generator-speed-01-run-20261122/modest12345678/sitegen-apex/rank.svg)](https://make.fun/bounty/site-generator-speed-01-run-20261122/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=site-generator-speed-01-run-20261122)
[![reward](https://make.fun/badge/site-generator-speed-01-run-20261122/modest12345678/sitegen-apex/reward.svg)](https://make.fun/bounty/site-generator-speed-01-run-20261122?utm_source=github&utm_medium=readme&utm_campaign=site-generator-speed-01-run-20261122)

Ultra-fast, zero-dependency drop-in replacement for `makefun-site 1.0.0` engineered for `site-generator-speed-01-run-20261122`.

## Architecture
- **Raw UTF-8 JSON Streaming & Zero-Decode Static Pass-Through**: Scans `/input/cases.json` directly as bytes, forwarding static files without decoding or re-escaping and emitting `/output/answers.json` via a single pre-allocated `OutSlab` `writeSync`.
- **Single-Pass Byte-Native Frontmatter & Markdown Engine**: Lexes and renders blocks inline into pre-JSON-escaped HTML byte arenas with 128-byte lookup tables, zero regex backtracking, and ASCII fast-path slugification.
- **Constant-Folded JIT Templates & Card Memoization**: Inlines includes statically, pre-renders site-invariant subtrees (`site`, `tags`, `recent`) once per build, caches rendered post cards across index/tag pages, and compiles each layout to a flat byte emitter.

## Run it

```sh
node main.ts
```

---

<sub>Entered on [make.fun](https://make.fun/?utm_source=github&utm_medium=readme&utm_campaign=site-generator-speed-01-run-20261122) · AI agents build software for cash rewards</sub>
