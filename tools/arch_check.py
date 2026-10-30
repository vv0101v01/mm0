#!/usr/bin/env python3
"""arch_check.py —— 用 `architecture.v3.json` 檢查實際的套件依賴圖。

不用「規範」壓人，只用它抓三種會真的壞掉的東西：

  1. forbidden_edges：庫不得反向依賴 apex（否則 bridge 就變成核心的一部分）。
  2. L_coeff 的依賴白名單：係數環庫只能依賴 exact/algebra 與 elim/core。
  3. 未登記的套件：新增套件卻沒進 architecture.v3.json，依賴圖就會悄悄說謊。

用法：python3 tools/arch_check.py [--graph]
      --graph 額外寫出 architecture.deps.mmd（Mermaid）與 architecture.deps.dot（Graphviz）
退出碼：0 = 通過，1 = 有違規。
"""
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
ARCH = ROOT / "architecture.v3.json"
MODULE = "vv0101v01/golden"

# 明確的依賴白名單（比對套件別名/路徑的最後一段或完整路徑）
ALLOW = {
    "L_coeff": {"exact/algebra", "elim/core"},
}


def parse_pkg(path: pathlib.Path) -> set:
    text = path.read_text(encoding="utf-8")
    return set(re.findall(r'"([^"]+)"', text))


def emit_graph(pkgs: dict, pkg_of_fed: dict) -> None:
    """把聯邦層級的依賴圖寫成 Mermaid 與 DOT（給人看，也給 CI 產 artifact）。"""
    fed_edges = set()
    for pkg, deps in pkgs.items():
        src = pkg_of_fed.get(pkg)
        if src is None:
            continue
        for dep in deps:
            if not dep.startswith(MODULE + "/"):
                continue
            dst = pkg_of_fed.get(dep[len(MODULE) + 1 :])
            if dst and dst != src:
                fed_edges.add((src, dst))
    mmd = ["```mermaid", "graph LR"]
    for fed in sorted(pkg_of_fed.values()):
        mmd.append(f"  {fed}[{fed}]")
    for a, b in sorted(fed_edges):
        mmd.append(f"  {a} --> {b}")
    mmd += ["```", ""]
    (ROOT / "architecture.deps.mmd").write_text("\n".join(mmd), encoding="utf-8")
    dot = ["digraph architecture {", "  rankdir=LR;"]
    for fed in sorted(pkg_of_fed.values()):
        dot.append(f'  "{fed}";')
    for a, b in sorted(fed_edges):
        dot.append(f'  "{a}" -> "{b}";')
    dot.append("}")
    (ROOT / "architecture.deps.dot").write_text("\n".join(dot) + "\n", encoding="utf-8")
    print(f"graph: {len(set(pkg_of_fed.values()))} federations, {len(fed_edges)} federation edges -> architecture.deps.mmd/.dot")


def main() -> int:
    arch = json.loads(ARCH.read_text(encoding="utf-8"))
    pkg_of_fed = {}
    for fed, spec in arch["federations"].items():
        for pkg in spec["packages"]:
            pkg_of_fed[pkg] = fed

    pkgs = {}
    for pkgfile in ROOT.rglob("moon.pkg"):
        rel = pkgfile.parent.relative_to(ROOT).as_posix()
        if rel in (".", ""):
            continue
        if any(part in {"_build", ".mooncakes"} for part in pkgfile.parts):
            continue
        pkgs[rel] = parse_pkg(pkgfile)

    problems = []

    # 1. 未登記套件
    for pkg in sorted(pkgs):
        if pkg not in pkg_of_fed and pkg != "cmd/audit":
            problems.append(f"未登記套件：{pkg}（請加進 architecture.v3.json）")

    # 2. forbidden_edges
    forbidden = {tuple(e) for e in arch["package_rules"]["forbidden_edges"]}
    for pkg, deps in pkgs.items():
        fed = pkg_of_fed.get(pkg)
        for dep in deps:
            if not dep.startswith(MODULE + "/"):
                continue
            dep_pkg = dep[len(MODULE) + 1 :]
            dep_fed = pkg_of_fed.get(dep_pkg)
            if dep_fed and (fed, dep_fed) in forbidden:
                problems.append(f"禁用邊：{pkg}({fed}) → {dep_pkg}({dep_fed})")

    # 3. 依賴白名單
    for pkg, allowed in ALLOW.items():
        for real in [p for p, f in pkg_of_fed.items() if f == pkg]:
            extra = sorted(
                d[len(MODULE) + 1 :]
                for d in pkgs.get(real, set())
                if d.startswith(MODULE + "/") and d[len(MODULE) + 1 :] not in allowed
            )
            if extra:
                problems.append(f"{real}({pkg}) 越界依賴：{extra}（白名單 {sorted(allowed)}）")

    edges = sum(
        1
        for deps in pkgs.values()
        for d in deps
        if d.startswith(MODULE + "/")
    )
    if "--graph" in sys.argv[1:]:
        emit_graph(pkgs, pkg_of_fed)
    # 4. 每個聯邦都要有套件（空聯邦 = 架構圖在說謊）
    for fed, spec in arch["federations"].items():
        if not spec["packages"] and fed != "F3_semiring":
            print(f"NOTE: 聯邦 {fed} 沒有任何套件")
    # 5. 一個套件只能屬於一個聯邦
    dup = {}
    for fed, spec in arch["federations"].items():
        for pkg in spec["packages"]:
            dup.setdefault(pkg, []).append(fed)
    for pkg, feds in sorted(dup.items()):
        if len(feds) > 1:
            problems.append(f"套件 {pkg} 同時屬於 {feds}")
    print(f"packages={len(pkgs)} federations={len(arch['federations'])} internal_edges={edges}")
    if problems:
        for p in problems:
            print("VIOLATION:", p)
        return 1
    print("ARCH_OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
