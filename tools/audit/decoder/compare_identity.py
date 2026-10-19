#!/usr/bin/env python3
"""Compare the outputs of identity_all.sh: C++ dump of every original value vs C++ dump of the
model's re-encoding. Writes a Markdown summary with mismatch groups."""
import collections, sys
out, J = sys.argv[1], int(sys.argv[2])
norm = lambda t: " ".join(t.split())
print("# Тождество инструкций на всех 2^24 значениях: C++ (исходный код) против C++ (пересборка модели)\n")
for tail in ("tail0", "tail1"):
    valid = compared = noenc = missing = 0
    groups = collections.Counter(); ex = {}
    for i in range(J):
        reasm = {}
        with open(f"{out}/cpp-reasm-{tail}-{i}.txt") as f:
            for line in f:
                a = line.rstrip("\n").split(" ", 1)
                if a and a[0].isdigit():
                    reasm[int(a[0])] = norm(a[1]) if len(a) > 1 else ""
        with open(f"{out}/cpp-name-{tail}-{i}.txt") as f:
            for line in f:
                a = line.rstrip("\n").split(" ", 2)
                if len(a) < 2 or not a[0].isdigit() or a[1] == "0":
                    continue
                v = int(a[0]); orig = norm(a[2]) if len(a) > 2 else ""
                valid += 1
                r = reasm.get(v)
                if r is None:
                    missing += 1; continue
                if r == "NOENC":
                    noenc += 1; continue
                compared += 1
                if r != orig:
                    key = ((orig.split() or ["(empty)"])[0], (r.split() or ["(empty)"])[0])
                    groups[key] += 1
                    ex.setdefault(key, (v, orig, r))
    print(f"## Хвост `{tail}`\n")
    print(f"- допустимых по C++: {valid}; сравнено: {compared}; модель не пересобрала: {noenc}; "
          f"нет в выводе модели: {missing}")
    print(f"- записи различаются: **{sum(groups.values())}** в {len(groups)} группах\n")
    if groups:
        print("| C++ (исходный) | C++ (пересборка) | значений | пример |")
        print("|---|---|---|---|")
        for k, n in groups.most_common(200):
            v, o, r = ex[k]
            print(f"| {k[0]} | {k[1]} | {n} | {v:06X}: `{o}` → `{r}` |")
        print()
