///| metric 的驗證測試：度量公理、Gromov–Hausdorff 距離的度量性與 1-Lipschitz 不變量、

///|
/// 子空間界、Vietoris–Rips 同調（圈圖 S¹ 型、收縮、Euler 恆等式）。
fn tri3(a : Int32, b : Int32, c : Int32) -> @metric.MSpace {
  @metric.mspace_build(3, [a, b, c])
}

///|
test "[Ax-Metric] 圈圖/線性度量通過公理；違反三角不等者被拒" {
  for n in [3, 4, 5, 6, 7, 8] {
    assert_eq(@metric.check_metric(@metric.mspace_cycle(n, 1)), true)
    assert_eq(@metric.check_metric(@metric.mspace_cycle(n, 2)), true)
  }
  let line = @metric.mspace_from_points([0, 3, 7, 10])
  assert_eq(@metric.check_metric(line), true)
  assert_eq(@metric.diam(line), 10)
  // (1,1,3) 違反三角不等式
  assert_eq(@metric.check_metric(tri3(1, 1, 3)), false)
}

///|
test "[T-GH-Metric] d_GH 的對稱性、三角不等式、d_GH=0 ⟺ 雙射等距" {
  let spaces : Array[@metric.MSpace] = [
    tri3(1, 1, 1),
    tri3(1, 1, 2),
    tri3(1, 2, 2),
    tri3(2, 2, 2),
    tri3(1, 1, 1),
    tri3(2, 3, 4),
  ]
  assert_eq(@metric.check_gh_axioms(spaces), true)
  // 自反
  assert_eq(@metric.gh2(spaces[0], spaces[0]), 0)
  // 縮放 2 倍：直徑差 = 2 給出下界，雙射達到，故 2·d_GH = 2
  assert_eq(@metric.gh2(tri3(1, 1, 2), tri3(2, 2, 4)), 2)
  assert_eq(@metric.gh2(tri3(1, 1, 1), tri3(2, 2, 2)), 1)
  // 相同空間的不同標記仍是等距
  assert_eq(@metric.is_isometric(tri3(1, 2, 2), tri3(2, 1, 2)), true)
  assert_eq(@metric.gh2(tri3(1, 2, 2), tri3(2, 1, 2)), 0)
}

///|
test "[T-GH-Lip] |diam X - diam Y| ≤ 2 d_GH(X,Y)（演變下的 1-Lipschitz 恆定關係）" {
  let spaces : Array[@metric.MSpace] = [
    tri3(1, 1, 1),
    tri3(1, 1, 2),
    tri3(1, 2, 2),
    tri3(2, 2, 2),
    tri3(2, 3, 4),
  ]
  let mut ok_all = true
  for a in spaces {
    for b in spaces {
      if !@metric.check_diam_lipschitz(a, b) {
        ok_all = false
      }
    }
  }
  assert_eq(ok_all, true)
  // 在上面的縮放例子上取等號
  assert_eq(@metric.diam(tri3(2, 2, 4)) - @metric.diam(tri3(1, 1, 2)), 2)
}

///|
test "[T-GH-Sub] 子空間界：4 點圈取 3 點/2 點子集" {
  let c4 = @metric.mspace_cycle(4, 1)
  assert_eq(@metric.check_subspace_bound(c4, [0, 1, 2]), true)
  assert_eq(@metric.check_subspace_bound(c4, [0, 2]), true)
  let c5 = @metric.mspace_cycle(5, 1)
  assert_eq(@metric.check_subspace_bound(c5, [0, 1, 2]), true)
  assert_eq(@metric.check_subspace_bound(c5, [0, 3]), true)
  // 4 點圈取其本身：ε = 0 且 d_GH = 0
  assert_eq(@metric.check_subspace_bound(c4, [0, 1, 2, 3]), true)
}

///|
test "[T-VR-Cycle][T-VR-Euler] β1 = 1（r=1，同倫 S¹）、收縮後為 0、Euler 恆等式" {
  for n in [4, 5, 6, 7, 8] {
    assert_eq(@metric.check_cycle_theorem(n), true)
  }
}

///|
test "[T-VR-Fill] n=3 的圈在 r=1 已被實心三角形填滿（β1 = 0）" {
  assert_eq(@metric.check_fill_edge_case(), true)
}
