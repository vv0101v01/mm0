///| 第九輪去重後，`exact/algebra` 的整數小工具必須有自己的一份測試 ——
///| 這些函式被 9 個套件共用，一旦分岔就是全樹的錯。

///| `int_pow`：小指數與 0 次方。
test "intutil: int_pow" {
  assert_eq(int_pow(2, 10), 1024)
  assert_eq(int_pow(7, 0), 1)
  assert_eq(int_pow(3, 5), 243)
  assert_eq(int_pow(-2, 3), -8)
}

///| `int_binom`：對稱性、邊界與 `C(−1, 0) = 1`（bridge 版與 score 版過去在這裡分岔）。
test "intutil: int_binom agrees on the edge cases" {
  assert_eq(int_binom(5, 2), 10)
  assert_eq(int_binom(5, 3), 10)
  assert_eq(int_binom(0, 0), 1)
  assert_eq(int_binom(4, 0), 1)
  assert_eq(int_binom(4, 5), 0)
  assert_eq(int_binom(4, -1), 0)
  // 廣義二項式：`C(−1, 0) = 1`（`super/score` 的展平對稱性靠這條）
  assert_eq(int_binom(-1, 0), 1)
  // `C(20,8) = 125970` 遠小於飽和值；舊的 Int32 實作會算成 19447
  assert_eq(int_binom(20, 8), 125970)
  // 飽和：`C(40,20) ≈ 1.38e11` ⇒ 飽和到 2e9
  assert_eq(int_binom(40, 20), 2000000000)
}

///| `int_sort`：升冪、穩定、不改輸入。
test "intutil: int_sort" {
  let xs : Array[Int32] = [3, -1, 2, 2, 0]
  let ys = int_sort(xs)
  assert_eq(ys, [-1, 0, 2, 2, 3])
  assert_eq(xs, [3, -1, 2, 2, 0]) // 輸入未被改動
  assert_eq(int_sort([]), [])
}

///| `int_lsr`：邏輯右移（高位補 0），不是算術右移。
test "intutil: int_lsr is logical" {
  assert_eq(int_lsr(8, 1), 4)
  assert_eq(int_lsr(-1, 1), 2147483647)
  assert_eq(int_lsr(-1, 0), -1)
  // n 取模 32：與舊實作一致
  assert_eq(int_lsr(1, 32), 1)
}

///| `int_mod_inv`：`a·a⁻¹ ≡ 1`，含大素數（乘積超過 `Int32`）。
test "intutil: int_mod_inv" {
  let p = 46351
  let inv = int_mod_inv(46350, p)
  assert_eq(inv, 46350)
  assert_eq(((46350L * inv.to_int64()) % p.to_int64()).to_int(), 1)
  assert_eq(int_mod_inv(3, 7), 5) // 3·5 = 15 ≡ 1 (mod 7)
  assert_eq(int_mod_inv(-1, 7), 6)
}

///| 向量／矩陣小工具。
test "intutil: vectors and matrices" {
  assert_true(int_vec_eq([1, 2], [1, 2]))
  assert_false(int_vec_eq([1, 2], [2, 1]))
  assert_false(int_vec_eq([1], [1, 2]))
  assert_true(int_vec_is_zero([0, 0]))
  assert_false(int_vec_is_zero([0, 1]))
  assert_eq(int_vec_scale([1, 2], 3), [3, 6])
  assert_eq(int_mat_vec([[2, 3]], [1, 1]), [5])
  assert_eq(int_mat_vec([[1, 0], [0, 1]], [4, 5]), [4, 5])
}
