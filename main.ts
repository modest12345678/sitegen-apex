require('node:v8').setFlagsFromString(
  '--no-incremental-marking --no-maglev --turbo-filter=KT_* --no-concurrent-recompilation --no-concurrent-marking --no-concurrent-sweeping --no-use-osr --max-semi-space-size=64'
);

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

require('./engine.cjs').runFile(IN + '/cases.json', OUT + '/answers.json');
