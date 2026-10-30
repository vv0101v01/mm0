///|
/// 五聯邦共同的最小證書形狀。它只統一呈現與總控，不把五個聯邦
/// 各自更豐富的原生證書型別抹平。
pub(all) struct BridgeCertificate {
  source : String
  name : String
  ok : Bool
  detail : String
}

///|
pub fn bridge_certificate(
  source : String,
  name : String,
  ok : Bool,
  detail~ : String = "",
) -> BridgeCertificate {
  { source, name, ok, detail, }
}

///|
pub fn certificate_of_cubical(result : @cub.CheckResult) -> BridgeCertificate {
  {
    source: "cubical",
    name: result.name,
    ok: result.ok,
    detail: if result.ok {
      "passed"
    } else {
      "failed"
    },
  }
}

///|
pub fn certificate_of_symlib(cert : @sym.Cert) -> BridgeCertificate {
  { source: "symlib", name: cert.name, ok: cert.holds, detail: cert.detail, }
}

///|
pub fn certificate_of_semiring_law(
  name : String,
  report : @semialg.LawReport,
) -> BridgeCertificate {
  { source: "semiring", name, ok: report.ok(), detail: report.summary(), }
}

///|
pub fn certificates_all_ok(certs : Array[BridgeCertificate]) -> Bool {
  for cert in certs {
    guard cert.ok else { return false }
  }
  true
}

///|
pub fn certificate_summary(certs : Array[BridgeCertificate]) -> String {
  let mut passed = 0
  for cert in certs {
    if cert.ok {
      passed = passed + 1
    }
  }
  "\{passed}/\{certs.length()} certificates passed"
}

///|
/// 五聯邦原生證書與全部跨聯邦橋、幾何—邏輯精細圖譜、大一統定理之總證書列。
pub fn bridge_certificates() -> Array[BridgeCertificate] {
  let out = bridge_base_certificates()
  for c in grand_unification_certificates() {
    out.push(c)
  }
  out
}

///|
fn bridge_base_certificates() -> Array[BridgeCertificate] {
  let cub_res : @cub.CheckResult = {
    name: "ua/coe definitional NbE, canonical ROBDD & adjoint equivalence fibers",
    ok: @cub.check_coe_definitional() &&
    @cub.check_bdd_canonical() &&
    @cub.check_adjoint_equivalence_and_fibers(),
  }
  let c4_graph = @sym.Graph::from_edges(4, [(0, 1), (1, 2), (2, 3), (3, 0)])
  let c4_certs = @sym.prove_graph(
    c4_graph,
    @sym.Perm::from_img([1, 2, 3, 0]),
    32,
  )
  let mut c4_ok = c4_certs.length() > 0
  for c in c4_certs {
    if !c.holds {
      c4_ok = false
    }
  }
  let sym_native = if c4_certs.length() > 0 {
    certificate_of_symlib(
      @sym.cert(
        "C4 automorphism & Schreier–Sims proof suite (\{c4_certs.length()} native certs)",
        c4_ok,
        c4_certs[0].detail,
      ),
    )
  } else {
    bridge_certificate("symlib", "C4 proof suite", false, detail="empty")
  }
  [
    certificate_of_cubical(cub_res),
    sym_native,
    bridge_certificate(
      "bridge",
      "Perm ↔ Wiring/Equiv & Unitary Representation (S4 round trip)",
      check_perm_wiring_bridge(),
    ),
    bridge_certificate(
      "bridge",
      "weighted graph and matrix symmetry",
      check_graph_symmetry_bridges(),
    ),
    bridge_certificate(
      "bridge",
      "semiring free category ↔ symlib FinCat",
      check_free_category_bridge(),
    ),
    bridge_certificate(
      "bridge",
      "tropical assignment, exact permanent/determinant and QPoly tropicalization",
      check_tropical_bridges(),
    ),
    certificate_of_semiring_law(
      "FaceClass BDD quotient semiring laws",
      face_semiring_law_report(),
    ),
  ]
}
