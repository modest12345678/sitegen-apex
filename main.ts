import { createRequire } from 'node:module';

const req = createRequire(import.meta.url);
req('node:v8').setFlagsFromString('--no-incremental-marking --no-turbofan --no-concurrent-recompilation --no-concurrent-marking --no-concurrent-sweeping --max-semi-space-size=64');

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

req('./engine.cjs').runFile(`${IN}/cases.json`, `${OUT}/answers.json`);
