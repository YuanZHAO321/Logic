#!/usr/bin/env python3
"""定言语句（A/E/I/O）推论检验器 —— 类演算思路，以"范恩区域"穷举模型。

思路：n 个词端把讨论界域切成 2^n 个区域；一个"模型"就是指定哪些区域有分子。
一个推论有效 ⟺ 在每一个使前题皆真的模型中，结论亦真（不许有一例外）。
无效时，脚本给出反例模型（哪些区域有分子），并构造一组具体的"个体"作反例。

三种存在意含的读法（"对待关系至少有三种说法"）：
  boolean      现代读法：A: S-P=0, E: SP=0, I: SP≠0, O: S-P≠0（全谓语句无存在意含）
  ae         A!/E! 读法：全谓语句另外断说主词有分子（A!: S-P=0 且 S≠0）
  traditional  传统读法：预设出现的每一词端都有分子（传统对待方形、24 个有效式）

用法：
  python categorical.py syllogism AAA-1          # 检验一个三段式（式+格）
  python categorical.py syllogism EIO-2 --mode boolean
  python categorical.py list [--mode traditional] # 列出全部有效式
  python categorical.py immediate O               # 位换、质换、换质位等直接推论
  python categorical.py immediate A --all         # 列出所有可推出的直接结论
  python categorical.py square --mode ae        # 对待关系表（给定一式真/假，其余如何）
  python categorical.py relation A O              # 两式之间的对待关系
"""

import argparse
import itertools
import sys
import unicodedata

MODES = ("boolean", "ae", "traditional")
MODE_NAMES = {
    "boolean": "现代(布尔)读法",
    "ae": "A!/E! 读法",
    "traditional": "传统读法(词端皆有分子)",
}
FORM_NAMES = {"A": "全谓肯定", "E": "全谓否定", "I": "偏谓肯定", "O": "偏谓否定"}
# 词端普及情形：(主位, 宾位)，〇=普及，︶=未普及
DIST = {"A": (True, False), "E": (True, True), "I": (False, False), "O": (False, True)}
FIGURES = {
    1: (("M", "H"), ("G", "M")),
    2: (("H", "M"), ("G", "M")),
    3: (("M", "H"), ("M", "G")),
    4: (("H", "M"), ("M", "G")),
}
TRADITIONAL_NAMES = {
    "AAA-1": "Barbara", "EAE-1": "Celarent", "AII-1": "Darii", "EIO-1": "Ferio",
    "AAI-1": "Barbari", "EAO-1": "Celaront",
    "EAE-2": "Cesare", "AEE-2": "Camestres", "EIO-2": "Festino", "AOO-2": "Baroco",
    "EAO-2": "Cesaro", "AEO-2": "Camestrop",
    "AAI-3": "Darapti", "IAI-3": "Disamis", "AII-3": "Datisi", "EAO-3": "Felapton",
    "OAO-3": "Bocardo", "EIO-3": "Ferison",
    "AAI-4": "Bramantip", "AEE-4": "Camenes", "IAI-4": "Dimaris", "EAO-4": "Fesapo",
    "EIO-4": "Fresison", "AEO-4": "Camenop",
}
TERM_ROLE = {"G": "小词", "H": "大词", "M": "共词"}


def pad(text, width):
    """按显示宽度补空格（中文字符占两格）。"""
    w = sum(2 if unicodedata.east_asian_width(ch) in "WF" else 1 for ch in text)
    return text + " " * max(width - w, 1)


# ---------------------------------------------------------------- 语义核心

class Lit:
    """词端：name 为类名，pos=False 表示其补类"非name"。"""

    def __init__(self, name, pos=True):
        self.name, self.pos = name, pos

    def neg(self):
        return Lit(self.name, not self.pos)

    def __str__(self):
        return self.name if self.pos else "非" + self.name

    def __eq__(self, other):
        return (self.name, self.pos) == (other.name, other.pos)

    def __hash__(self):
        return hash((self.name, self.pos))


class Stmt:
    def __init__(self, form, subj, pred):
        self.form, self.subj, self.pred = form, subj, pred

    def text(self, marks=False):
        s, p = str(self.subj), str(self.pred)
        if marks:
            ds, dp = DIST[self.form]
            s += "〇" if ds else "︶"
            p += "〇" if dp else "︶"
        return {
            "A": f"凡{s}是{p}", "E": f"没有{s}是{p}",
            "I": f"有些{s}是{p}", "O": f"有些{s}不是{p}",
        }[self.form]

    def code(self):
        return f"{self.subj} {self.form.lower()} {self.pred}"

    def lits(self):
        return [self.subj, self.pred]


def member(region, idx, lit):
    return region[idx[lit.name]] == lit.pos


def true_in(stmt, model, idx, mode):
    """model: 有分子的区域之集合。"""
    def some(cond):
        return any(cond(r) for r in model)

    s, p = stmt.subj, stmt.pred
    if stmt.form == "A":
        val = not some(lambda r: member(r, idx, s) and not member(r, idx, p))
    elif stmt.form == "E":
        val = not some(lambda r: member(r, idx, s) and member(r, idx, p))
    elif stmt.form == "I":
        val = some(lambda r: member(r, idx, s) and member(r, idx, p))
    else:
        val = some(lambda r: member(r, idx, s) and not member(r, idx, p))
    if mode == "ae" and stmt.form in "AE":
        val = val and some(lambda r: member(r, idx, s))
    return val


def models(names, required_lits=()):
    """穷举所有模型；required_lits 中的词端必须有分子（传统读法的预设）。"""
    idx = {n: i for i, n in enumerate(names)}
    regions = list(itertools.product((True, False), repeat=len(names)))
    for bits in itertools.product((False, True), repeat=len(regions)):
        model = frozenset(r for r, b in zip(regions, bits) if b)
        if all(any(member(r, idx, l) for r in model) for l in required_lits):
            yield model
    return


def check(premises, conclusion, names, mode):
    """回传 (是否有效, 反例模型或 None)。"""
    idx = {n: i for i, n in enumerate(names)}
    required = []
    if mode == "traditional":
        for st in list(premises) + [conclusion]:
            required += st.lits()
    for m in models(names, required):
        if all(true_in(p, m, idx, mode) for p in premises) and not true_in(conclusion, m, idx, mode):
            return False, m
    return True, None


def describe_model(model, names):
    """把反例模型写成"有分子的区域"以及一组具体个体。"""
    if not model:
        return "  讨论界域中一个分子也没有（所有类皆为空类）。"
    lines = []
    sets = {n: [] for n in names}
    for k, region in enumerate(sorted(model, reverse=True), 1):
        label = "·".join(n if b else "非" + n for n, b in zip(names, region))
        lines.append(f"  区域 {label} 有分子，例如个体 x{k}")
        for n, b in zip(names, region):
            if b:
                sets[n].append(f"x{k}")
    lines.append("  于是：" + "；".join(
        f"{n}={{{', '.join(v)}}}" if v else f"{n}=空类" for n, v in sets.items()))
    return "\n".join(lines)


# ---------------------------------------------------------------- 三段式

def parse_code(code):
    code = code.strip().upper().replace(" ", "").replace("_", "-")
    if "-" in code:
        mood, fig = code.split("-", 1)
    else:
        mood, fig = code[:3], code[3:]
    if len(mood) != 3 or any(c not in "AEIO" for c in mood) or fig not in ("1", "2", "3", "4"):
        raise ValueError(f"无法解析 '{code}'：格式应如 AAA-1、EIO-2（式三字母 + 格 1~4）")
    return mood, int(fig)


def build(mood, fig):
    (a, b), (c, d) = FIGURES[fig]
    major = Stmt(mood[0], Lit(a), Lit(b))
    minor = Stmt(mood[1], Lit(c), Lit(d))
    concl = Stmt(mood[2], Lit("G"), Lit("H"))
    return major, minor, concl


def distributed(stmt, term):
    ds, dp = DIST[stmt.form]
    return (stmt.subj.name == term and ds) or (stmt.pred.name == term and dp)


def rule_check(major, minor, concl):
    """五条规律逐条检验；另附两条补充规律。"""
    neg = lambda s: s.form in "EO"
    part = lambda s: s.form in "IO"
    out = []

    ok = distributed(major, "M") or distributed(minor, "M")
    out.append(("规律一", "共词至少普及一次", ok,
                "" if ok else "共词 M 在两前题中一次也未普及（共词不普及），大词与小词无从借共词同一部分发生关联"))

    bad = []
    if distributed(concl, "G") and not distributed(minor, "G"):
        bad.append("小词 G 在小前题未普及而在结论中普及（小词潜越）")
    if distributed(concl, "H") and not distributed(major, "H"):
        bad.append("大词 H 在大前题未普及而在结论中普及（大词潜越）")
    out.append(("规律二", "前题中未普及的词端在结论中不得普及", not bad, "；".join(bad)))

    ok = not (neg(major) and neg(minor))
    out.append(("规律三", "两前题皆否定则无结论", ok,
                "" if ok else "两前题皆否定：G 与 H 都被排斥于 M 之外，二者关系无从确定"))

    ok = not ((neg(major) or neg(minor)) and not neg(concl))
    out.append(("规律四", "前题有一否定，结论必否定", ok,
                "" if ok else "前题有否定语句，结论却是肯定语句"))

    ok = not (part(major) and part(minor))
    out.append(("规律五", "两前题皆偏谓则无结论", ok,
                "" if ok else "两前题皆为偏谓语句"))

    ok = not (not neg(major) and not neg(minor) and neg(concl))
    out.append(("补充一", "两前题皆肯定，结论不得否定", ok,
                "" if ok else "两前题皆肯定却得否定结论（五条规律未列此条，AAO-4 之类须靠它排除）"))

    ok = not ((part(major) or part(minor)) and not part(concl))
    out.append(("补充二", "前题有一偏谓，结论必偏谓", ok,
                "" if ok else "前题有偏谓语句，结论却是全谓语句"))
    return out


def cmd_syllogism(args):
    try:
        mood, fig = parse_code(args.code)
    except ValueError as e:
        sys.exit(str(e))
    code = f"{mood}-{fig}"
    major, minor, concl = build(mood, fig)
    names = ["G", "H", "M"]
    print(f"三段式 {code}" + (f"（传统名 {TRADITIONAL_NAMES[code]}）" if code in TRADITIONAL_NAMES else ""))
    print("词端：G=小词，H=大词，M=共词；〇=普及，︶=未普及\n")
    print(f"  大前题  {major.form}  {major.text(marks=True)}")
    print(f"  小前题  {minor.form}  {minor.text(marks=True)}")
    print("  ————————")
    print(f"  结  论  {concl.form}  ∴{concl.text(marks=True)}\n")

    print("【规律检验】")
    for tag, rule, ok, why in rule_check(major, minor, concl):
        print(f"  {'✓' if ok else '✗'} {tag}：{rule}" + ("" if ok else f" —— {why}"))

    print("\n【语义检验：穷举范恩区域模型】")
    modes = MODES if args.mode == "all" else (args.mode,)
    for mode in modes:
        valid, cm = check([major, minor], concl, names, mode)
        print(f"  {MODE_NAMES[mode]}：{'有效 V' if valid else '无效 I'}")
        if not valid:
            print("  反例（前题皆真而结论假）：")
            print(describe_model(cm, names))
    print("\n提示：把反例中的 G、H、M 换成具体的类，即得'形式相同、前题真而结论假'的反例论证。")


def cmd_list(args):
    modes = MODES if args.mode == "all" else (args.mode,)
    for mode in modes:
        found = []
        for fig in (1, 2, 3, 4):
            for mood in map("".join, itertools.product("AEIO", repeat=3)):
                major, minor, concl = build(mood, fig)
                if check([major, minor], concl, ["G", "H", "M"], mode)[0]:
                    code = f"{mood}-{fig}"
                    found.append(f"{code}({TRADITIONAL_NAMES.get(code, '?')})")
        print(f"{MODE_NAMES[mode]}：共 {len(found)} 个有效式（64 式 × 4 格 = 256 种中）")
        for i in range(0, len(found), 6):
            print("  " + "  ".join(found[i:i + 6]))
        print()


# ---------------------------------------------------------------- 直接推论

def immediate_named(form):
    S, P = Lit("S"), Lit("P")
    prem = Stmt(form, S, P)
    conv = {"A": "I", "E": "E", "I": "I", "O": "O"}[form]
    obv = {"A": "E", "E": "A", "I": "O", "O": "I"}[form]
    ops = [
        ("位换（简单位换）", Stmt(form, P, S)),
        ("位换（限量位换 per accidens）", Stmt(conv, P, S)) if form == "A" else None,
        ("质换", Stmt(obv, S, P.neg())),
        # I 质换得 O，O 不能位换，故 I 的这两项必无效；列出以示其无效
        ("换质位（质换后位换）", Stmt({"A": "E", "E": "I", "I": "O", "O": "I"}[form], P.neg(), S)),
        ("全换（换质位后再质换）", Stmt({"A": "A", "E": "O", "I": "O", "O": "O"}[form], P.neg(), S.neg())),
        ("等差（下推偏谓）", Stmt({"A": "I", "E": "O"}[form], S, P)) if form in "AE" else None,
    ]
    return prem, [o for o in ops if o]


def cmd_immediate(args):
    form = args.form.upper()
    if form not in "AEIO" or len(form) != 1:
        sys.exit("形式须为 A、E、I、O 之一")
    prem, ops = immediate_named(form)
    names = ["S", "P"]
    print(f"原语句：{form}  {prem.text(marks=True)}\n")
    print(pad("操作", 32) + pad("结论", 22) + "".join(pad(MODE_NAMES[m], 26) for m in MODES))
    for label, st in ops:
        cells = ["有效" if check([prem], st, names, mode)[0] else "无效" for mode in MODES]
        print(pad(label, 32) + pad(f"{st.form} {st.text()}", 22) + "".join(pad(c, 26) for c in cells))
    if args.all:
        print("\n所有可推出的直接结论（主宾词端可为 S、P、非S、非P）：")
        for mode in MODES:
            outs = []
            for f in "AEIO":
                for a, b in (("S", "P"), ("P", "S")):
                    for pa, pb in itertools.product((True, False), repeat=2):
                        st = Stmt(f, Lit(a, pa), Lit(b, pb))
                        if st.text() == prem.text():
                            continue
                        if check([prem], st, names, mode)[0]:
                            outs.append(st.text())
            print(f"  {MODE_NAMES[mode]}：" + ("、".join(outs) if outs else "无"))


# ---------------------------------------------------------------- 对待关系

def relation(f1, f2, mode):
    """回传 f1 与 f2（同主同宾）之间的对待关系名称。"""
    n1, n2 = (f + "!" if mode == "ae" and f in "AE" else f for f in (f1, f2))
    S, P = Lit("S"), Lit("P")
    a, b = Stmt(f1, S, P), Stmt(f2, S, P)
    idx = {"S": 0, "P": 1}
    required = [S, P] if mode == "traditional" else []
    combos = set()
    for m in models(["S", "P"], required):
        combos.add((true_in(a, m, idx, mode), true_in(b, m, idx, mode)))
    tt, tf, ft, ff = ((True, True) in combos, (True, False) in combos,
                      (False, True) in combos, (False, False) in combos)
    if not tt and not ff:
        return "矛盾（不同真，亦不同假）"
    if not tt and ff:
        return "反对（不可同真，可以同假）"
    if tt and not ff and tf and ft:
        return "小反对（可以同真，不可同假）"
    if not tf and ft:
        return f"等差（{n1} 真则 {n2} 真；{n2} 假则 {n1} 假）"
    if not ft and tf:
        return f"等差（{n2} 真则 {n1} 真；{n1} 假则 {n2} 假）"
    if not tf and not ft:
        return "相等"
    return "独立（任一之真假不牵扯另一之真假）"


def implied(f_given, value, f_other, mode):
    S, P = Lit("S"), Lit("P")
    a, b = Stmt(f_given, S, P), Stmt(f_other, S, P)
    idx = {"S": 0, "P": 1}
    required = [S, P] if mode == "traditional" else []
    vals = {true_in(b, m, idx, mode) for m in models(["S", "P"], required)
            if true_in(a, m, idx, mode) == value}
    return "真" if vals == {True} else "假" if vals == {False} else "不定"


def cmd_square(args):
    modes = MODES if args.mode == "all" else (args.mode,)
    for mode in modes:
        label = (lambda f: f + "!" if f in "AE" else f) if mode == "ae" else (lambda f: f)
        print(f"== {MODE_NAMES[mode]} ==")
        print("  两两关系：")
        for f1, f2 in itertools.combinations("AEIO", 2):
            print(f"    {label(f1)}—{label(f2)}：{relation(f1, f2, mode)}")
        print("  推论表（行：已知；列：其余语句之真假）")
        print("    " + pad("已知", 10) + "".join(pad(label(f), 8) for f in "AEIO"))
        for f in "AEIO":
            for v in (True, False):
                cells = ["—" if g == f else implied(f, v, g, mode) for g in "AEIO"]
                print("    " + pad(label(f) + ("真" if v else "假"), 10) + "".join(pad(c, 8) for c in cells))
        print()


def cmd_relation(args):
    f1, f2 = args.f1.upper(), args.f2.upper()
    if f1 not in "AEIO" or f2 not in "AEIO" or len(f1) != 1 or len(f2) != 1:
        sys.exit("形式须为 A、E、I、O 之一")
    for mode in MODES:
        n1, n2 = (f + "!" if mode == "ae" and f in "AE" else f for f in (f1, f2))
        print(f"{MODE_NAMES[mode]}：{n1}—{n2} 为 {relation(f1, f2, mode)}")


def main():
    ap = argparse.ArgumentParser(description="定言语句与三段式检验器")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("syllogism", help="检验三段式，如 AAA-1")
    p.add_argument("code")
    p.add_argument("--mode", choices=MODES + ("all",), default="all")
    p.set_defaults(fn=cmd_syllogism)

    p = sub.add_parser("list", help="列出有效式")
    p.add_argument("--mode", choices=MODES + ("all",), default="all")
    p.set_defaults(fn=cmd_list)

    p = sub.add_parser("immediate", help="位换、质换等直接推论")
    p.add_argument("form")
    p.add_argument("--all", action="store_true")
    p.set_defaults(fn=cmd_immediate)

    p = sub.add_parser("square", help="对待关系表")
    p.add_argument("--mode", choices=MODES + ("all",), default="all")
    p.set_defaults(fn=cmd_square)

    p = sub.add_parser("relation", help="两式之间的对待关系")
    p.add_argument("f1")
    p.add_argument("f2")
    p.set_defaults(fn=cmd_relation)

    args = ap.parse_args()
    args.fn(args)


if __name__ == "__main__":
    main()
