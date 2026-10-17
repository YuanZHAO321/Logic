#!/usr/bin/env python3
"""关系性质判别

给出一个有限关系（若干有序对），判别其界域、逆界域、范限、反逆，
以及三类基本性质（各有正、反、准三种，共九种）与项目对应情形：
  自反 / 不自反 / 准自反     aRa 对范限每一分子皆真 / 皆假 / 有真有假
  对称 / 反对称 / 准对称     aRb 则必 bRa / 则必非 bRa / 不一定
  传达 / 反传达 / 准传达     aRb 且 bRc 则必 aRc / 则必非 aRc / 不一定
  一对一 / 一对多 / 多对一 / 多对多

注意：有限的实例只能显示"这一组对"的情形。逻辑上说一种关系对称或传达，
是对一切可能情形而言的；实例最有用的是举出反例（一个反例即足以否定）。
"反对称"指 aRb 则必非 bRa（即今日所谓 asymmetric），与今日教科书中
"antisymmetric"（aRb 且 bRa 则 a=b）不同。

用法：
  python relations.py "老大,老二 老二,老三 老大,老三"
  python relations.py "甲,乙 乙,甲 乙,丙" --universe 甲 乙 丙 丁   # 自反性改就讨论界域判定
"""

import argparse
import sys


def parse_pairs(text):
    pairs = []
    for chunk in text.replace("；", " ").replace(";", " ").split():
        for sep in (",", "，", ">", "-", "→"):
            if sep in chunk:
                a, b = chunk.split(sep, 1)
                pairs.append((a.strip(), b.strip()))
                break
        else:
            sys.exit(f"无法解析有序对 '{chunk}'：请写作 a,b")
    return pairs


def analyze(pairs, universe=()):
    R = set(pairs)
    domain = sorted({a for a, _ in R})
    converse_domain = sorted({b for _, b in R})
    field = sorted(set(domain) | set(converse_domain))  # 范限 = 界域与逆界域之逻辑和
    out = {"界域": domain, "逆界域": converse_domain, "范限": field,
           "反逆": sorted((b, a) for a, b in R)}

    base = sorted(set(field) | set(universe)) if universe else field
    where = "讨论界域" if universe else "范限"
    refl = [a for a in base if (a, a) in R]
    if len(refl) == len(base):
        out["自反性"] = ("自反", f"{where}中每一分子 a 皆有 aRa")
    elif not refl:
        out["自反性"] = ("不自反", f"{where}中没有一个分子 a 有 aRa")
    else:
        miss = [a for a in base if (a, a) not in R]
        out["自反性"] = ("准自反", f"{refl[0]}R{refl[0]} 成立而 {miss[0]}R{miss[0]} 不成立")

    sym = [(a, b) for a, b in R if (b, a) in R]
    asym = [(a, b) for a, b in R if (b, a) not in R]
    if not asym:
        out["对称性"] = ("对称", "凡 aRb 皆有 bRa")
    elif not sym:
        out["对称性"] = ("反对称", "凡 aRb 皆无 bRa")
    else:
        a, b = sym[0]
        c, d = asym[0]
        out["对称性"] = ("准对称", f"{a}R{b} 且 {b}R{a}；但 {c}R{d} 而无 {d}R{c}")

    chains = [(a, b, c) for a, b in R for b2, c in R if b == b2]
    trans = [t for t in chains if (t[0], t[2]) in R]
    intrans = [t for t in chains if (t[0], t[2]) not in R]
    if not chains:
        out["传达性"] = ("传达（亦反传达；无 aRb、bRc 之链，二者皆空真）", "无可检验之链")
    elif not intrans:
        out["传达性"] = ("传达", "凡 aRb 且 bRc 皆有 aRc")
    elif not trans:
        a, b, c = intrans[0]
        out["传达性"] = ("反传达", f"凡 aRb 且 bRc 皆无 aRc，如 {a}R{b}、{b}R{c} 而无 {a}R{c}")
    else:
        a, b, c = trans[0]
        x, y, z = intrans[0]
        out["传达性"] = ("准传达", f"{a}R{b}、{b}R{c} 有 {a}R{c}；但 {x}R{y}、{y}R{z} 而无 {x}R{z}")

    many_right = any(sum(1 for x, _ in R if x == a) > 1 for a in domain)  # 一个前项对多个后项
    many_left = any(sum(1 for _, y in R if y == b) > 1 for b in converse_domain)
    out["对应"] = {(False, False): "一对一", (True, False): "一对多",
                  (False, True): "多对一", (True, True): "多对多"}[(many_right, many_left)]
    return out


def main():
    ap = argparse.ArgumentParser(description="关系性质判别")
    ap.add_argument("pairs", help='有序对，如 "a,b b,c a,c"')
    ap.add_argument("--universe", nargs="*", default=(),
                    help="讨论界域的分子（含不出现在任何对中者）；给出时自反性就界域判定")
    args = ap.parse_args()
    res = analyze(parse_pairs(args.pairs), args.universe)
    for key in ("界域", "逆界域", "范限"):
        print(f"{key}：{{{', '.join(res[key])}}}")
    print("反逆：" + "  ".join(f"{a}R{b}" for a, b in res["反逆"]))
    for key in ("自反性", "对称性", "传达性"):
        name, why = res[key]
        print(f"{key}：{name}（{why}）")
    print(f"项目对应：{res['对应']}")
    print("\n提醒：以上只就所给实例而言；判定一种关系'在逻辑上'是否对称、传达，须顾及一切可能情形。")


if __name__ == "__main__":
    main()
