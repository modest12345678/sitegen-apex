require('node:v8').setFlagsFromString(
  '--no-incremental-marking --no-turbofan --invocation-count-for-maglev=1800 --invocation-count-for-maglev-osr=1800 --no-concurrent-recompilation --no-concurrent-marking --no-concurrent-sweeping'
);

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

require('./engine.cjs').runFile(IN + '/cases.json', OUT + '/answers.json');
