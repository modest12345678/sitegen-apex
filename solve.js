import { createRequire } from 'node:module';

const req = createRequire(import.meta.url);
export const { run } = req('./engine.cjs');
