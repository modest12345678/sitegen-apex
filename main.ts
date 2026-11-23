require('node:v8').setFlagsFromString(
  '--no-incremental-marking --no-turbofan --maglev-filter=K* --invocation-count-for-maglev=200 --no-concurrent-recompilation --no-concurrent-marking --no-concurrent-sweeping --no-concurrent-osr --max-semi-space-size=64'
);

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

require('./engine.cjs').runFile(IN + '/cases.json', OUT + '/answers.json');
