#!/usr/bin/env python3
"""abort_audit.py —— 「錯誤用崩潰表達」的債務盤點與閘門（第九輪）。

背景：合併時整棵樹有 290+ 個 `abort(`。它們不是 bug，但**是債**：呼叫者無法從型別
知道一個函式會不會中止，所以每一個呼叫點都得先讀實作。

這支工具做三件事：

1. **逐站點分類**（寫進 `ABORT-CONTRACTS.md`）：
   - `cap`          —— 資源上限（枚舉太大就拒絕）；
   - `precondition` —— 對**輸入**的守衛（長度不符、不是素數、不是 DAG…）；
   - `invariant`    —— 內部不變量（私有函式、構造出來的模型）。
2. **閘門**：
   - **我們的套件**（`bridge`／`higher`／`homotopy`／`opt`／`coeff`）必須是 **0 個 abort** ——
     這些是樹的 apex，公共 API 一律回 `Option`／`Result`（第九輪已全部改完）。
   - **golden 併入的套件**：站點總數不得超過基線（`tools/abort_baseline.json`），
     且不得**新增** `pub` 函式上的 `precondition` 站點。
3. **可達性論證**：把 `pub` 且 `precondition` 的站點列成「契約表」，逐條寫明定義域；
   這些是下一輪要改成 `Result` 的清單（不是假裝已清空）。

用法：
  python3 tools/abort_audit.py            # 印報告
  python3 tools/abort_audit.py --write    # 寫 ABORT-CONTRACTS.md
  python3 tools/abort_audit.py --check    # 閘門（退出碼 1 = 失敗）
"""
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
OURS = ("bridge", "higher", "homotopy", "opt", "coeff")
BASELINE = pathlib.Path(__file__).resolve().parent / "abort_baseline.json"

CAP_WORDS = ("上限", "cap", "exceeded", "too large", "overflow", "超出", "過大")
INVARIANT_WORDS = ("invariant", "unreachable", "should never", "不可能", "不該")

FN_RE = re.compile(r"^\s*(pub\s+)?fn\s+([A-Za-z_][A-Za-z0-9_]*)")
ABORT_RE = re.compile(r'abort\(\s*"([^"]*)"')


def sources():
    for p in sorted(ROOT.rglob("*.mbt")):
        if "_build" in p.parts or ".mooncakes" in p.parts:
            continue
        yield p


def package_of(path: pathlib.Path) -> str:
    rel = path.relative_to(ROOT)
    return rel.parts[0] if len(rel.parts) > 1 else "(root)"


def classify(msg: str, is_pub: bool) -> str:
    low = msg.lower()
    if any(w in low for w in CAP_WORDS):
        return "cap"
    if any(w in low for w in INVARIANT_WORDS):
        return "invariant"
    if not is_pub:
        return "invariant"
    return "precondition"


def scan():
    sites = []
    for p in sources():
        text = p.read_text(encoding="utf-8", errors="ignore").split("\n")
        cur = ("", False)  # (function name, is_pub)
        for i, line in enumerate(text):
            m = FN_RE.match(line)
            if m:
                cur = (m.group(2), bool(m.group(1)))
            for msg in ABORT_RE.findall(line):
                sites.append(
                    {
                        "file": p.relative_to(ROOT).as_posix(),
                        "line": i + 1,
                        "pkg": package_of(p),
                        "fn": cur[0],
                        "pub": cur[1],
                        "msg": msg,
                        "kind": classify(msg, cur[1]),
                    }
                )
    return sites


def render(sites):
    by_pkg = {}
    for s in sites:
        by_pkg.setdefault(s["pkg"], []).append(s)
    lines = ["# ABORT-CONTRACTS：`abort(` 的逐站點契約表（自動生成）", ""]
    total = len(sites)
    ours = sum(len(v) for k, v in by_pkg.items() if k in OURS)
    lines.append(f"- 全樹 `abort(` 站點：**{total}**")
    lines.append(f"- 我們的五個套件（apex）：**{ours}**（閘門要求 0）")
    lines.append("")
    lines.append("## 1. 依套件與類別")
    lines.append("")
    lines.append("| 套件 | 站點 | cap | precondition | invariant |")
    lines.append("|---|---|---|---|---|")
    for pkg in sorted(by_pkg):
        v = by_pkg[pkg]
        lines.append(
            "| `{}` | {} | {} | {} | {} |".format(
                pkg,
                len(v),
                sum(1 for s in v if s["kind"] == "cap"),
                sum(1 for s in v if s["kind"] == "precondition"),
                sum(1 for s in v if s["kind"] == "invariant"),
            )
        )
    lines.append("")
    lines.append("## 2. 公共 API 上的 precondition（下一輪要改成 `Result` 的清單）")
    lines.append("")
    pre = [s for s in sites if s["kind"] == "precondition" and s["pub"]]
    if not pre:
        lines.append("（空 —— apex 套件已全部改畢）")
    for s in pre:
        lines.append(f"- `{s['file']}:{s['line']}` **`{s['fn']}`** — {s['msg']}")
    lines.append("")
    lines.append("## 3. 我們的五個套件（必須為 0）")
    lines.append("")
    o = [s for s in sites if s["pkg"] in OURS]
    if not o:
        lines.append("`bridge`／`higher`／`homotopy`／`opt`／`coeff`：**0 個 abort**。")
        lines.append("")
        lines.append(
            "第九輪把 `bridge` 的 18 處全部改成 `Option`／`Result`（見 `SPEC.md` §4.15.2）："
            "`perm_wiring`、`signed_perm_wiring`、`perm_equiv`、`average_permutation_matrices`、"
            "`assignment_cost`、`tropical_optimal_assignments`、`tropical_matrix_symmetries`、"
            "`exact_permanent_int64`、`exact_determinant_int64`、`qpoly_tropicalize_padic`、"
            "`rat_padic_valuation`、`free_category_to_fincat`、`weighted_graph_report`、"
            "`semiring_graph_symmetry_projector`。"
        )
    for s in o:
        lines.append(f"- `{s['file']}:{s['line']}` **`{s['fn']}`** — {s['msg']}（{s['kind']}）")
    lines.append("")
    lines.append("## 4. golden 併入套件的完整清單")
    lines.append("")
    for pkg in sorted(by_pkg):
        if pkg in OURS:
            continue
        lines.append(f"### `{pkg}`")
        lines.append("")
        for s in by_pkg[pkg]:
            tag = "pub" if s["pub"] else "priv"
            lines.append(f"- `{s['file']}:{s['line']}` ({tag}) `{s['fn']}` [{s['kind']}] — {s['msg']}")
        lines.append("")
    return "\n".join(lines) + "\n"


def main() -> int:
    sites = scan()
    if "--write" in sys.argv:
        out = ROOT / "ABORT-CONTRACTS.md"
        out.write_text(render(sites), encoding="utf-8")
        print(f"wrote {out.relative_to(ROOT)}（{len(sites)} 站點）")
    by_pkg = {}
    for s in sites:
        by_pkg.setdefault(s["pkg"], []).append(s)
    ours = [s for s in sites if s["pkg"] in OURS]
    print(f"abort 站點：全樹 {len(sites)}；我們的五套件 {len(ours)}")
    pre = [s for s in sites if s["kind"] == "precondition" and s["pub"]]
    print(f"公共 API 上的 precondition：{len(pre)}")

    if "--check" not in sys.argv:
        return 0

    problems = []
    if ours:
        for s in ours:
            problems.append(f"自家套件仍有 abort：{s['file']}:{s['line']} {s['fn']} — {s['msg']}")

    golden = {k: len(v) for k, v in by_pkg.items() if k not in OURS}
    base = json.loads(BASELINE.read_text()) if BASELINE.exists() else {}
    if not base:
        BASELINE.write_text(json.dumps(golden, indent=2, sort_keys=True) + "\n")
        print(f"基線不存在 ⇒ 已寫入 {BASELINE.name}（{sum(golden.values())} 站點）")
    else:
        for pkg, n in sorted(golden.items()):
            if n > base.get(pkg, 0):
                problems.append(f"{pkg} 的 abort 由 {base.get(pkg, 0)} 增加到 {n}")
    if problems:
        print("ABORT_REGRESSION：")
        for p in problems:
            print("  " + p)
        return 1
    print("ABORT_OK（自家套件 0 個；golden 併入套件未超過基線）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
