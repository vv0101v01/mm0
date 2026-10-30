#!/usr/bin/env python3
"""doc_audit.py —— 公共介面的文檔覆蓋率審計（backlog §7-2 的替代實作）。

golden 的 `audit_spec.py` 檢查的是「每個符號都被分到一個規格家族」；
合併樹沒有那張家族表，但有更基礎的一條：**每個 `pub` 項都要有 `///|` 文檔**，
且文檔的第一行要說「這是什麼」。沒有文檔的公共符號，就是下一個使用者會誤用的地方。

用法：python3 tools/doc_audit.py [--check]
退出碼：0 = 通過（無缺文檔），1 = 有缺。
"""
import re
import sys
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
# 只對**本輪新增**的套件強制（新代碼不許沒有文檔）；舊套件照實報告但不擋閘門。
STRICT = {"higher", "homotopy", "opt"}
PAT = re.compile(r"^\s*pub\s+(fn|struct|enum|let|type|trait)\s+([A-Za-z_][A-Za-z0-9_]*)")

def scan(path):
    lines = path.read_text(encoding="utf-8").splitlines()
    missing = []
    total = 0
    for i, line in enumerate(lines):
        m = PAT.match(line)
        if not m:
            continue
        total += 1
        j = i - 1
        while j >= 0 and lines[j].strip() == "":
            j -= 1
        if j < 0 or not (lines[j].lstrip().startswith("///") or lines[j].lstrip().endswith("*/")):
            missing.append((m.group(1), m.group(2), i + 1))
    return total, missing

def main():
    check = "--check" in sys.argv[1:]
    rows = []
    bad = 0
    for pkg_dir in sorted(p for p in ROOT.iterdir() if p.is_dir() and (p / "moon.pkg").exists()):
        pkg = pkg_dir.relative_to(ROOT).as_posix()
        total = 0
        missing = []
        for f in sorted(pkg_dir.glob("*.mbt")):
            t, miss = scan(f)
            total += t
            missing += [(f.name, k, n, ln) for k, n, ln in miss]
        if total:
            rows.append((pkg, total, len(missing), missing))
            if missing and pkg.split("/")[0] in STRICT:
                bad += len(missing)
    print(f"{'package':28s} pub  doc  missing")
    for pkg, total, nmiss, _ in rows:
        print(f"{pkg:28s} {total:4d} {total - nmiss:4d} {nmiss:6d}")
    if bad:
        print(f"\nSTRICT 套件缺文檔數：{bad}")
        for pkg, _, _, miss in rows:
            if miss and pkg.split("/")[0] in STRICT:
                for f, kind, name, ln in miss[:8]:
                    print(f"  {pkg}/{f}:{ln}  pub {kind} {name}")
    ok = bad == 0
    print("DOC_OK" if ok else "DOC_MISSING")
    return 0 if ok else (1 if check else 0)

if __name__ == "__main__":
    sys.exit(main())
