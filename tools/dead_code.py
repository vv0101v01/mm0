#!/usr/bin/env python3
"""dead_code.py —— 死碼與重複的審計（第七輪的減債工具）。

三份清單：

1. **未被引用**：`pub fn` 的名字在整棵樹裡只出現在它的定義處。
   圖書館的公開 API 本來就會有這種情況，所以這份清單**不自動判死**；
   它用來回答「哪些名字是真正沒人用的」。
2. **跨套件重複**：同一個函式名在 ≥ 2 個套件裡各有一份實作。
   同名不代表一定是壞事（各套件自帶小工具很常見），但**同一個演算法寫三遍**就是債。
3. **守衛中止**：`abort(` 的分佈。這些是邊界檢查，不是 bug；但數量多的套件
   意味著「錯誤用崩潰表達」，值得在下一次重構時改成結果型別。

用法：
  python3 tools/dead_code.py            # 印報告
  python3 tools/dead_code.py --write    # 同時寫 DEAD-CODE.md
  python3 tools/dead_code.py --check    # 只檢查「自家套件」是否有新增死碼，超出基線就退出 1

基線檔：tools/dead_code_baseline.json（自家套件的未引用 pub 名單）。
"""
import json
import pathlib
import re
import sys
from collections import Counter, defaultdict

ROOT = pathlib.Path(__file__).resolve().parent.parent
OURS = ("higher", "homotopy", "opt", "coeff", "bridge")
BASELINE = pathlib.Path(__file__).resolve().parent / "dead_code_baseline.json"


def sources():
    for p in sorted(ROOT.rglob("*.mbt")):
        if "_build" in p.parts or ".mooncakes" in p.parts:
            continue
        yield p


def main():
    texts = {p: p.read_text(errors="ignore") for p in sources()}
    alltext = "\n".join(texts.values())
    words = Counter(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", alltext))

    defs = defaultdict(list)
    for p, t in texts.items():
        for m in re.finditer(r"^\s*(pub\s+)?fn\s+([A-Za-z_][A-Za-z0-9_]*)", t, re.M):
            defs[m.group(2)].append((p.relative_to(ROOT).as_posix(), bool(m.group(1))))

    unused_pub, unused_priv = [], []
    for name, occ in sorted(defs.items()):
        if words[name] > len(occ):
            continue
        entry = (occ[0][0], name)
        if any(pub for _, pub in occ):
            unused_pub.append(entry)
        else:
            unused_priv.append(entry)

    dups = {n: sorted({p for p, _ in o}) for n, o in defs.items() if len({p for p, _ in o}) > 1}

    aborts = Counter()
    for p, t in texts.items():
        c = t.count("abort(")
        if c:
            aborts[p.relative_to(ROOT).as_posix().split("/")[0] if "/" in p.relative_to(ROOT).as_posix() else "(root)"] += c

    ours_unused = [e for e in unused_pub if e[0].split("/")[0] in OURS]

    print(f"檔案 {len(texts)}／行 {alltext.count(chr(10))}")
    print(f"未被引用的 pub fn：{len(unused_pub)}；私有 fn：{len(unused_priv)}")
    print(f"跨套件同名定義：{len(dups)}")
    print(f"自家套件未引用 pub：{len(ours_unused)}")
    for p, n in ours_unused:
        print("   ", p, n)
    print("abort( 分佈（前 6）：", aborts.most_common(6))

    if "--write" in sys.argv:
        lines = ["# DEAD-CODE：死碼與重複清冊（自動生成）", "",
                 f"- 掃描：{len(texts)} 個 `.mbt`／{alltext.count(chr(10))} 行",
                 f"- 未被引用的 `pub fn`：**{len(unused_pub)}**（多為 golden 併入的公開 API）",
                 f"- 私有未被引用：**{len(unused_priv)}**",
                 f"- 跨套件同名定義：**{len(dups)}**",
                 "", "## 1. 跨套件同名定義（同一演算法多份實作）", "",
                 "| 名稱 | 出現在 |", "|---|---|"]
        for n, ps in sorted(dups.items())[:40]:
            lines.append(f"| `{n}` | {', '.join(ps)} |")
        lines += ["", "## 2. 未被引用的公開符號（前 60）", "", "| 檔案 | 符號 |", "|---|---|"]
        for p, n in unused_pub[:60]:
            lines.append(f"| `{p}` | `{n}` |")
        lines += ["", "## 3. 守衛中止分佈", "", "| 套件 | `abort(` |", "|---|---|"]
        for k, v in aborts.most_common():
            lines.append(f"| {k} | {v} |")
        lines += ["", "## 判定", "",
                  "- 「未被引用」≠ 死碼：golden 併入的公開 API 保留是**規格**，不是債。",
                  "- 真正的債是第 1 節：同名同義的實作散在 2–3 個套件（例：`vec_scale` 三份、`mat_vec` 三份、`sort_ints` 兩份）。",
                  "- 第七輪已刪掉 12 個真正沒人用的自家函式；基線見 `tools/dead_code_baseline.json`。", ""]
        (ROOT / "DEAD-CODE.md").write_text("\n".join(lines), encoding="utf-8")
        print("寫出 DEAD-CODE.md")

    if "--check" in sys.argv:
        baseline = json.loads(BASELINE.read_text()) if BASELINE.exists() else {"ours": []}
        known = {tuple(x) for x in baseline["ours"]}
        new = [e for e in ours_unused if tuple(e) not in known]
        if new:
            print("DEAD_CODE_REGRESSION：自家套件出現新的未引用 pub：")
            for p, n in new:
                print("   ", p, n)
            return 1
        print(f"DEAD_CODE_OK（基線 {len(known)} 條，無新增）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
