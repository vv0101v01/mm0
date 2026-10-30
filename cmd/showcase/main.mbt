///|
fn main {
  println(
    "Golden Grand Unification — Five-Federation Architecture & Synthesis",
  )
  println("===================================================================")
  println("-- Five Autonomous Mathematical Federations --")
  let feds = @bridge.five_federation_descriptors()
  let mut fed_passed = 0
  for fed in feds {
    if fed.live_health_ok {
      fed_passed = fed_passed + 1
    }
    let st = if fed.live_health_ok { "PASS" } else { "FAIL" }
    println("[\{st}] federation \{fed.slug}: \{fed.summary}")
  }
  println("-- Complete K_5 Cross-Federation Pairwise Bridges (10/10) --")
  let k5_edges = @bridge.verify_k5_federation_bridges()
  let mut k5_passed = 0
  for edge in k5_edges {
    if edge.holds {
      k5_passed = k5_passed + 1
    }
    let st = if edge.holds { "PASS" } else { "FAIL" }
    println("[\{st}] \{edge.id}: \{edge.bridge_theorem}")
    println("        \{edge.quantitative_witness}")
  }
  println("-- Unified Certificate Ledger --")
  let certificates = @bridge.bridge_certificates()
  let mut atlas_passed = 0
  let mut pentagon_ok = false
  let mut six_ok = false
  for cert in certificates {
    let status = if cert.ok { "PASS" } else { "FAIL" }
    println("[\{status}] \{cert.source}: \{cert.name}")
    if cert.detail != "" {
      println("        \{cert.detail}")
    }
    if cert.source == "atlas" && cert.ok {
      atlas_passed = atlas_passed + 1
    } else if cert.source == "bridge/unification" {
      if cert.name.contains("Pentagon") {
        pentagon_ok = cert.ok
      } else if cert.name.contains("Six-Pillar") {
        six_ok = cert.ok
      }
    }
  }
  println(@bridge.certificate_summary(certificates))
  let all_certs_ok = @bridge.certificates_all_ok(certificates)
  let unif_ok = fed_passed == 5 &&
    k5_passed == 10 &&
    pentagon_ok &&
    six_ok &&
    atlas_passed == 18 &&
    all_certs_ok
  println(
    "five-federation unification: federations=\{fed_passed}/5, K5_bridges=\{k5_passed}/10, pentagon=\{pentagon_ok}, six_pillar=\{six_ok}, atlas=\{atlas_passed}/18, all_ok=\{unif_ok}",
  )
  let cycle = @sgraph.Graph::build(4, [0, 1, 2, 3], [1, 2, 3, 0], [1, 1, 1, 1])
  let report = match @bridge.weighted_graph_report(cycle, 32) {
    Ok(r) => r
    Err(e) => {
      println("weighted_graph_report 失敗：\{e}")
      abort("showcase failed")
    }
  }
  println(
    "directed weighted C4: weighted symmetries=\{report.weighted_symmetry_count}, reachable pairs=\{report.reachable_pairs}, finite-distance sum=\{report.finite_distance_sum}",
  )
  println(
    "symmetry-average projector: projector=\{@cub.is_projector(report.symmetry_projector)}, trace=\{@cub.mat_trace_re(report.symmetry_projector)}",
  )
  let rotation = @sym.Perm::from_img([1, 2, 3, 0])
  let wiring_ok = match @bridge.perm_equiv(rotation) {
    Err(_) => false
    Ok(eq) =>
      match @bridge.perm_of_wiring(eq.wiring) {
        Some(back) => back.equal(rotation)
        None => false
      }
  }
  println("Perm → cubical Equiv → Perm round trip: \{wiring_ok}")
  guard all_certs_ok && wiring_ok && unif_ok else { abort("showcase failed") }
}
