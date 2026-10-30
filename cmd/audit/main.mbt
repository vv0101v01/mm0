///| ## `cmd/audit` —— 唯一入口：預設印報告，`--quick` / `--jsonl` / `--sig` / `--verify`
///
///|   1. 無引數：本輪全部量測；`--full` 追加耗時段（三界剪枝／團數／Carlet 窮舉）；
///|   2. `--quick`：≤ 2 秒的 CI 閘門（四條會壞掉且難查的等式）；
///|   3. `--jsonl [--seal H]`：本紀元的帳本行（`ledger/audit.sh` 落盤用）；
///|   4. `--verify L1 L2 …`：驗證一份完整帳本（首行 = 創世或紀元封條）。

///| 本輪的邊界 payload。`kind = boundary` 是能力邊界判定，`measurable` 是新增的可算量。
///| payload 必須 JSONL 安全（`;` 分隔、無引號逗號）。改動任何一條 ⇒ 帳本自動開新紀元。
fn payloads() -> Array[(String, String, String)] {
  [
    ("B1-schema", "boundary", "levels=least-fixpoint;infeasible-witness=cycle;schema=guarded"),
    ("B2-dsystem", "boundary", "gf2-rank=tseitin;clique-rank-bound=rank(I+Abar)=exact"),
    ("B3-persistence", "boundary", "ledger=hash-chain;verify=adaptive-start;jsonl=replay"),
    ("B4-exact-algebra", "boundary", "levels=L0..L6;carry=exact;rat=exact;qzeta=exact"),
    ("B5-decision", "boundary", "anf-order-free=true;weight=3^k;degree-from-derivatives"),
    ("B6-homotopy", "boundary", "H1RP2=Z/2;uct-verified;torsion-cert=auto"),
    ("B7-hou", "boundary", "finite-carrier-unify=rank-formula;hot-reload=journaled"),
    ("G3-spectral", "measurable", "spectrum=exact-charpoly;eigen=exact"),
    ("G5-anf", "measurable", "mobius=exact;support=normalized"),
    ("G6-nonabelian", "measurable", "S3-torsors-on-S1=3-conj-classes;linear-H2-count=6;disk=1"),
    ("G7-sparsity", "measurable", "n=20;deg=3;subspace=1351-of-1048576;lookups=9921;2113x"),
    ("G8-selector", "measurable", "deriv-vs-mobius-vs-affine;crossover-4-5-6"),
    ("G9-invariance", "measurable", "two-models-per-space-agree;T2-S1-RP2-wedge"),
    ("R1-hopf", "measurable", "gysin=uct-agree;pi1=0-for-d=1;pi1=Z/2-for-d=2"),
    ("R2-infinity", "measurable", "reuse-kills-H1-on-wedge;fresh-preserves-H1;kan-not-reached"),
    ("R3-milp-carlet", "measurable", "LP-gap=2;AI-bound-n<=4;Maj5..8-reach-ceil;K33-LP=9/2"),
    ("R4-postnikov", "measurable", "H5-KZ3-F2=1;Sq2-nonzero;odd-torsion=0;Z/2-vs-Z/4-open"),
    ("R5-torsion", "measurable", "reidemeister-exact-Qzeta;L71-ne-L72;p=5-7-11-13-agree"),
    ("R6-bnb", "measurable", "three-bounds-sound;nodes-45-to-9;LP-needs-x-le-1"),
    ("R7-selector", "measurable", "deriv-vs-mobius-vs-affine;crossover-4-5-6;binom-overflow-fixed"),
    ("R8-torsion-cert", "measurable", "auto-z-c-k;verified;RP2-k=2;L7-k=7;free-none"),
    ("R9-refine", "measurable", "false-twin-sound;K3-true-twin-counterexample;components-3"),
    ("R10-invariance", "measurable", "two-models-per-space-agree;univalence-shadow"),
    ("R11-b1prime", "measurable", "ordinal-levels;strict-lift-5of5;cumulative-fails-E1-E2;limit-omega-solvable"),
    ("R12-inv-gate", "measurable", "registry-4-invariants;rejects-single-model;rejects-mismatch"),
    ("R13-brunerie", "measurable", "beta=+2;coker-times-beta=Z-2;pi4-S3=Z-2;moore-dictionary"),
    ("R14-tetra", "measurable", "S3-kan-at-dim-3;missing-4-horns=5;obstruction-at-n+1"),
    ("R15-ladder", "measurable", "kan-to-groupoid-to-pi1-to-H1-to-chain;free-group-gap"),
    ("R16-coeff-regression", "measurable", "cup-uct-bockstein-probes;steenrod-division"),
    ("R17-aw-cup-bridge", "measurable", "dimH1-Q-vs-F2-RP2=0-vs-1;cup-rank-Q-vs-F2-RP2=0-vs-1;graded-comm=up-to-coboundary"),
    ("R18-spectral-cert", "measurable", "certified=float-when-nondegenerate;degenerate-endpoint=undecided;witten-index=4of4"),
    ("R19-berezinian-cech", "measurable", "jac-det=-t^-(m+1);ber-degree=n-m-1;cech-chi=d+1-on-P1"),
    ("R20-morse-bars", "measurable", "5-spaces;monotone;jump-one-dim;euler-by-order-and-by-value;betti-over-Q"),
    ("R21-dedup", "measurable", "10-names-unified-in-exact-algebra;cross-package-dups-30-to-21;binom-divergence-found"),
    ("R22-abort-contracts", "measurable", "apex-bridge-0-aborts;tree-202-classified;gate-in-tools-abort_audit"),
    ("R23-visibility", "measurable", "7-models-x-6-rings;q-blind-count=4-of-7;root-cause-G1"),
  ]
}

///|

fn build_ledger(seal : String) -> @sledger.SLedger {
  let l = if seal == "" {
    @sledger.sled_new()
  } else {
    @sledger.sled_new_sealed(seal)
  }
  for p in payloads() {
    let _ = @sledger.sled_record(l, p.0, p.1, p.2)
  }
  l
}

///|

fn sig_of() -> String {
  let mut s = ""
  for p in payloads() {
    s = "\{s}\{p.0}:\{p.2};"
  }
  @sledger.sha256_hex(s)
}

///| 印出一個探針的第一行（併入回歸用：只要它還在跑，套件就沒被搬壞）。
fn first_line(tag : String, lines : Array[String]) -> Unit {
  if lines.length() > 0 {
    println("  \{tag} " + lines[0])
  } else {
    println("  \{tag} （空）")
  }
}

///| ≤ 2 秒的 CI 閘門：四條「壞了會很難查」的等式。
fn quick() -> Unit {
  let mut ok = true
  // 1. 撓率證書：L(7) 必須自動給出 k=7 且逐條通過
  let certs = @coeff.torsion_certificates([1, 1, 1], [[], [[0]], [[7]]], 12)
  if certs.length() != 1 || !@coeff.cert_verified(certs[0]) || certs[0].k != 7 {
    ok = false
  }
  // 2. 三界分支定界：K(3×3) 必須給 ω=3，且與暴力一致
  let g = @opt.graph_new(9)
  for i = 0; i < 9; i = i + 1 {
    for j = 0; j < 9; j = j + 1 {
      if i / 3 != j / 3 {
        @opt.graph_add(g, i, j)
      }
    }
  }
  if @opt.bnb(g, 7)[0] != 3 || @opt.clique_number_brute(g) != 3 {
    ok = false
  }
  // 3. 呈現無關性：T² 的兩個模型必須逐項一致
  let a = @bridge.inv_of_cw("simplex", @bridge.cw_of_faces(@bridge.t2_faces()))
  let b = @bridge.inv_of_cw("cw", @coeff.cc_from_attaching([1, 2, 1], [[], [[0, 0]], [[0, 0]]]))
  if !@bridge.models_agree(a, b) {
    ok = false
  }
  // 4. 撓率必須分開 L(7,1) 與 L(7,2)
  if @homotopy.torsion_same(7, 1, 2) {
    ok = false
  }
  // 5. B1′：序數吸收律、嚴格 Lift 五條、不變量閘門
  if !@bridge.ord_eq(@bridge.ord_add(@bridge.ord_one(), @bridge.ord_omega()), @bridge.ord_omega()) {
    ok = false
  }
  if !@bridge.lift_strict_all() {
    ok = false
  }
  let (gate_ok, _gate_msg) = @bridge.invariance_gate(@bridge.registered_invariants())
  if !gate_ok {
    ok = false
  }
  // 6. Brunerie 數把 π₄(S³) 釘成 Z/2
  if @homotopy.group_of_d(@homotopy.whitehead_hopf()) != "Z/2" {
    ok = false
  }
  // 7. 3-截斷：S³ 補滿 3-角但缺 5 個 4-角
  if @higher.horns_missing_count(@higher.sset_trunc_s3(), 3) != 0 {
    ok = false
  }
  if @higher.horns_missing_count(@higher.sset_trunc_s3(), 4) != 5 {
    ok = false
  }
  println("QUICK ok=\{ok}（撓率證書／三界剪枝／呈現無關性／撓率分離／B1′／Brunerie／3-截斷）")
}

///|

fn report(full : Bool) -> Unit {
  println("== R1 Hopf 纖維化 ==")
  for l in @homotopy.hopf_probe() {
    println(l)
  }
  println("")
  println("== R5 Reidemeister 撓率 ==")
  for l in @homotopy.torsion_probe() {
    println(l)
  }
  println("")
  println("== R4 Postnikov k-invariant ==")
  for l in @homotopy.postnikov_probe() {
    println(l)
  }
  println("")
  println("== R2 ∞-groupoid ==")
  for l in @higher.infinity_probe() {
    println(l)
  }
  println("")
  println("== G6 非阿貝爾 Čech H¹ ==")
  for l in @bridge.nonabelian_probe() {
    println(l)
  }
  println("")
  println("== G7 事前稀疏性判定（n = 16） ==")
  for l in @bridge.sparsity_probe_n(16) {
    println(l)
  }
  println("")
  println("== G8 表示選擇器 ==")
  for l in @bridge.selector_probe() {
    println(l)
  }
  println("")
  println("== R8 撓率證書：自動找 z 與 c（backlog §7-5） ==")
  for l in @coeff.torsion_cert_probe() {
    println(l)
  }
  println("")
  println("== R9 孿生／分量前處理（backlog §7-8） ==")
  for l in @opt.refine_probe() {
    println(l)
  }
  println("")
  println("== G9 呈現無關性（單值性的計算影子） ==")
  for l in @bridge.invariance_probe() {
    println(l)
  }
  println("")
  println("== R11 B1′ 層級代數（方案 B）：序數層級 + 嚴格 Lift ==")
  for l in @bridge.level_algebra_probe() {
    println(l)
  }
  println("")
  println("== R12 B1′-3 不變量登記表與閘門 ==")
  for l in @bridge.gate_selftest() {
    println(l)
  }
  println("")
  println("== R13 B6 殘餘：Brunerie 數把 π₄(S³) 釘成 Z/2 ==")
  for l in @homotopy.brunerie_probe() {
    println(l)
  }
  println("")
  println("== R14 ∞-groupoid 的 3-截斷（tetra） ==")
  for l in @higher.tetra_probe() {
    println(l)
  }

  if full {
    println("")
  println("")
  println("== R15 截斷階梯：Kan → groupoid → π₁ → H₁ → 鏈複形 ==")
  for r in @higher.ladder() {
    println(@higher.ladder_show(r))
  }
  println("  " + @higher.cyclicity_witness())
  let (gap_a, gap_b) = @higher.free_group_gap()
  println("  自由群間隙：Hom(自由群, S₃) 計數 下界=0 上界=\{gap_a}／實際=\{gap_b}")
  println("")
  println("== R19 可見性表：7 模型 × 6 環（B4／B6 的共同根因 G1） ==")
  for l in @coeff.visibility_probe() {
    println(l)
  }
  println("")
  println("== R16 係數環與高階操作回歸（併入後） ==")
  for l in @coeff.cup_probe() {
    println(l)
  }
  for l in @coeff.uct_probe() {
    println(l)
  }
  for l in @coeff.bockstein_probe() {
    println(l)
  }
  for l in @homotopy.steenrod_probe() {
    println(l)
  }
  for l in @homotopy.division_probe() {
    println(l)
  }
  println("")
  println("== R17 併入回歸：B1–B7 各自的探針第一行 ==")
  first_line("B1", @bridge.b1_probe())
  first_line("B2", @bridge.b2_probe())
  first_line("B3", @bridge.b3_probe())
  first_line("B4", @bridge.b4_probe())
  first_line("B6", @bridge.b6_probe())
  first_line("B5", @bridge.b5_probe())
  first_line("B7", @bridge.b7_probe())
  first_line("G3", @bridge.g3_probe())
  first_line("G5", @bridge.g5_probe())
  let (cup_t, cup_w) = @bridge.coeff_cup_split()
  let (bock_ok, bock_total) = @bridge.coeff_bockstein_ok()
  let (uct_ok, uct_total) = @bridge.coeff_uct_pass()
  println(
    "  coeff: UCT=\{uct_ok}/\{uct_total} Bockstein=\{bock_ok}/\{bock_total} cup 非零對數 T^2=\{cup_t} wedge=\{cup_w}",
  )
  first_line("G7", @bridge.sparsity_probe())
    println("")
    println("== R6 三界合流剪枝 ==")
    for l in @opt.bnb_probe() {
      println(l)
    }
    println("")
    println("== R3 團數三界 ==")
    for l in @opt.clique_diag() {
      println(l)
    }
    println("")
    for l in @opt.clique_probe() {
      println(l)
    }
    println("")
    println("== R3 Carlet 代數免疫度 ==")
    for l in @opt.carlet_probe() {
      println(l)
    }
    println("")
    println("== R18 橋 18：接 golden 的 AW 杯積環（ℚ vs F₂） ==")
    for l in @bridge.aw_cup_bridge_probe() {
      println(l)
    }
    println("")
    println("== R18 橋 20：譜流的區間認證（super ↔ cubical） ==")
    for l in @bridge.spectral_cert_probe() {
      println(l)
    }
    println("")
    println("== R18 橋 21：Berezinian 與 ℙ¹ 的 Čech 上同調（super ↔ scheme） ==")
    for l in @bridge.berezinian_probe() {
      println(l)
    }
    println("")
    println("== R18 Morse 指標流的區間化（§7-3 殘餘） ==")
    for l in @homotopy.morse_probe() {
      println(l)
    }
  }
}

///|

fn main {
  let raw = @env.args()
  let args : Array[String] = []
  for i = 1; i < raw.length(); i = i + 1 {
    args.push(raw[i])
  }
  if args.length() >= 1 && args[0] == "--quick" {
    quick()
    return
  }
  if args.length() >= 1 && args[0] == "--sig" {
    println(sig_of())
    return
  }
  if args.length() >= 1 && args[0] == "--jsonl" {
    let mut seal = ""
    if args.length() >= 3 && args[1] == "--seal" {
      seal = args[2]
    }
    let l = build_ledger(seal)
    let txt = @sledger.sled_jsonl(l)
    println(txt)
    return
  }
  if args.length() >= 1 && args[0] == "--verify" {
    let lines : Array[String] = []
    for i = 1; i < args.length(); i = i + 1 {
      if args[i] != "" {
        lines.push(args[i])
      }
    }
    let (ok, n) = @sledger.sled_parse_lines_chain(lines)
    println("VERIFY ok=\{ok} records=\{n}")
    return
  }
  report(args.length() >= 1 && args[0] == "--full")
}
