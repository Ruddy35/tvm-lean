#!/usr/bin/env python3
"""Compare the decoder audit outputs of the model and C++ (see run.sh). Writes a Markdown summary."""
import collections, sys
out, J = sys.argv[1], int(sys.argv[2])
STEP = ((1 << 24) + J - 1) // J
print("# Сравнение декодеров: модель против C++\n")
for tail in ("tail0", "tail1"):
    total = mism = 0
    groups = collections.Counter()   # (prefix16, cpp_len, lean_len) -> count
    examples = {}
    valid_c = valid_l = 0
    for i in range(J):
        with open(f"{out}/cpp-len-{tail}-{i}.txt") as fc, open(f"{out}/lean-len-{tail}-{i}.txt") as fl:
            v = i * STEP
            for lc, ll in zip(fc, fl):
                c, l = int(lc), int(ll)
                total += 1
                valid_c += c > 0; valid_l += l > 0
                if c != l:
                    mism += 1
                    key = (v >> 8, c, l)
                    groups[key] += 1
                    examples.setdefault(key, v)
                v += 1
    print(f"## Хвост `{tail}`\n")
    print(f"- значений: {total}; допустимых по C++: {valid_c}; по модели: {valid_l}")
    print(f"- расхождений длины/допустимости: **{mism}**")
    if groups:
        print(f"- групп по 16-битному префиксу: {len(groups)}\n")
        print("| префикс (16 бит) | длина C++ | длина модели | значений | пример (24 бит) |")
        print("|---|---|---|---|---|")
        for (p, c, l), n in sorted(groups.items())[:300]:
            print(f"| {p:04X} | {c} | {l} | {n} | {examples[(p, c, l)]:06X} |")
    print()
# instructions: the full text of the decoded instruction (the model prints in the C++ dump format)
def load(path):
    d = {}
    for line in open(path):
        parts = line.rstrip("\n").split(" ", 2)
        if len(parts) >= 2:
            d[int(parts[0])] = (int(parts[1]), " ".join(parts[2].split()) if len(parts) > 2 else "")
    return d
for tail in ("tail0", "tail1"):
    c, l = load(f"{out}/cpp-name-{tail}.txt"), load(f"{out}/lean-name-{tail}.txt")
    both = [v for v in c if v in l and c[v][0] > 0 and l[v][0] > 0]
    diff = [v for v in both if c[v][1] != l[v][1]]
    print(f"## Запись инструкций, хвост `{tail}` (значения v % 256 = 0)\n")
    print(f"- допустимых у обеих сторон: {len(both)}; запись различается: **{len(diff)}**\n")
    if diff:
        print("| значение (24 бит) | C++ | модель |")
        print("|---|---|---|")
        for v in diff[:400]:
            print(f"| {v:06X} | `{c[v][1]}` | `{l[v][1]}` |")
        print()
