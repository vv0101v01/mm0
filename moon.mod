// vv0101v01/golden —— seven-federation merged module (F1..F5 in-flight, F6 elim, F7 super)
name = "vv0101v01/golden"

version = "0.3.0"

readme = "README.md"

repository = "https://github.com/vv0101v01/mm0"

license = "Apache-2.0"

keywords = [
  "cubical",
  "elimination",
  "smith-normal-form",
  "superalgebra",
  "homology",
  "ledger",
]

preferred_target = "wasm-gc"

description = "golden (cubical-hermitian) merged with notebook (tensorlab): exact algebra + modular elimination + Z2-graded superalgebra + cross-run hash-chained ledger, governed by the seven-boundary scorecard."

import {
  "moonbitlang/async@0.22.5",
}
