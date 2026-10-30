#!/bin/sh
# audit.sh —— 跨執行七邊界帳本（宿主適配器層；純核心在 MoonBit 的 super/sledger）
#
#   sh ledger/audit.sh append   # 記錄本次審計（payload 變更 ⇒ 自動開新紀元），隨後全鏈驗證
#   sh ledger/audit.sh verify   # 只驗證 ledger/BOUNDARY.jsonl
#   sh ledger/audit.sh rotate   # 強制封存當前鏈、開新紀元
#   sh ledger/audit.sh show     # 印出帳本
#   sh ledger/audit.sh head     # 印出鏈頭（可作為外部錨定值）
#
# 設計：wasm-gc 沒有 fs API，故「落盤」由 shell 完成；
#       雜湊、鏈驗證、JSONL 解析全在 MoonBit（super/sledger）內，
#       核心保持純函數，宿主只提供 append/dedupe/archive 這三件作業系統的事。
#
# 紀元（era）：payload 定義一改（新一輪量測），舊鏈就不能被續接，只能被封存。
#   新紀元的創世記錄把舊鏈頭 hash 放進 prev，兩個紀元被硬綁在一起。
set -e
cd "$(dirname "$0")/.."
LEDGER=ledger/BOUNDARY.jsonl
SIGFILE=ledger/ERA_SIG
SEALFILE=ledger/ERA_SEAL
mkdir -p ledger/archive
touch "$LEDGER"

head_hash() { tail -n 1 "$LEDGER" | sed -n 's/.*"hash":"\([0-9a-f]*\)".*/\1/p'; }

# 目前紀元的封條（無封條則輸出空字串）
cur_seal() { cat "$SEALFILE" 2>/dev/null || true; }

# 依封條重新產生本紀元的 12 行，寫入 $1
emit() {
  S=$(cur_seal)
  if [ -n "$S" ]; then
    moon run cmd/audit -- --jsonl --seal "$S" | grep -v '^$' > "$1"
  else
    moon run cmd/audit -- --jsonl | grep -v '^$' > "$1"
  fi
  # 形狀檢查：帳本每一行都必須是 JSONL。`moon run` 的輸出若被別的東西污染
  # （例如 `cmd/audit` 暫時是印報告的版本），寧可失敗，也不要把報告寫進帳本。
  if [ ! -s "$1" ] || grep -qv '^{' "$1"; then
    echo "EMIT_NOT_JSONL"; exit 1
  fi
}

rotate() {
  if [ -s "$LEDGER" ]; then
    H=$(head_hash)
    if [ -z "$H" ]; then echo "LEDGER_UNPARSABLE"; exit 1; fi
    STAMP=$(date -u +%Y%m%dT%H%M%SZ)
    cp "$LEDGER" "ledger/archive/BOUNDARY.$STAMP.jsonl"
    printf '%s\n' "$H" > ledger/archive/SEAL.$STAMP
    echo "ERA_ROTATE sealed=$H archived=ledger/archive/BOUNDARY.$STAMP.jsonl"
    printf '%s' "$H" > "$SEALFILE"   # 新紀元：以舊鏈頭為封條
  else
    rm -f "$SEALFILE"
  fi
  emit "$LEDGER"
  moon run cmd/audit -- --sig > "$SIGFILE"
}

case "${1:-verify}" in
  append)
    NEW_SIG=$(moon run cmd/audit -- --sig)
    OLD_SIG=$(cat "$SIGFILE" 2>/dev/null || echo none)
    if [ "$NEW_SIG" != "$OLD_SIG" ]; then
      echo "PAYLOAD_CHANGED old=$OLD_SIG new=$NEW_SIG"
      rotate
    else
      emit /tmp/boundary_new.jsonl
      while IFS= read -r line; do
        [ -z "$line" ] && continue
        if ! grep -qxF "$line" "$LEDGER"; then
          printf '%s\n' "$line" >> "$LEDGER"
        fi
      done < /tmp/boundary_new.jsonl
    fi
    ;;
  rotate)
    rotate
    ;;
  show)
    cat "$LEDGER"; exit 0 ;;
  head)
    head_hash; exit 0 ;;
esac

if [ ! -s "$LEDGER" ]; then
  echo "LEDGER_EMPTY"; exit 1
fi
# 驗證器的契約：傳入完整帳本（首行 = 創世或紀元封條）
moon run cmd/audit -- --verify $(cat "$LEDGER")
