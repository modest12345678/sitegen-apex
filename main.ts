require('node:v8').setFlagsFromString(
  '--no-incremental-marking --no-turbofan --invocation-count-for-maglev=800 --invocation-count-for-maglev-osr=800 --no-concurrent-recompilation --no-concurrent-marking --no-concurrent-sweeping --no-concurrent-osr --no-maglev-build-code-on-background --no-maglev-deopt-data-on-background --no-maglev-destroy-on-background'
);

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

require('./engine.cjs').runFile(IN + '/cases.json', OUT + '/answers.json');
