#!/usr/bin/env python3
"""语句联系（外部推论）真值表工具

把语句当作不解析内部结构的元素 p、q、r……（外部推论），
列出 2^n 种真假可能，检验：一个式子的真值表、是否为套套络基（恒真式）、
两式是否相等、一组前题是否蕴涵结论（推论是否有效；无效时列出反例行）。

记号（可混用）：
  非   ~  ¬  !  not
  且   ·  &  ∧  and
  或   ∨  |  v  or        （"相容的或"；v 作运算符用，故不可作变量名）
  不相容的或  ⊻  ^  xor   （"或甲或乙，不可得兼"）
  如果…则   ⊃  →  ->  =>  implies
  相等     ≡  ↔  <->  <=>  iff
变量：字母或中文词，如 p、q、下雨、地湿。

用法：
  python truth_table.py table "p⊃q" "~q⊃~p"
  python truth_table.py taut "(p⊃q)·(q⊃r)⊃(p⊃r)"
  python truth_table.py equiv "p⊃q" "~p∨q"
  python truth_table.py argue "p⊃q" "q" --conclusion "p"      # 肯定后件：无效，给反例
  python truth_table.py forms                                 # 各推论形式的有效性总表
"""

import argparse
import itertools
import re
import sys
import unicodedata

TOKEN_RE = re.compile(
    r"\s*(?:(<->|<=>|->|=>|[~¬!·&∧∨|⊻^⊃→≡↔()])|([^\W\d]\w*))", re.UNICODE)
WORD_OPS = {"not": "~", "and": "·", "or": "∨", "v": "∨", "xor": "⊻",
            "implies": "⊃", "iff": "≡"}
SYM = {"~": "~", "¬": "~", "!": "~", "·": "·", "&": "·", "∧": "·",
       "∨": "∨", "|": "∨", "⊻": "⊻", "^": "⊻",
       "⊃": "⊃", "→": "⊃", "->": "⊃", "=>": "⊃",
       "≡": "≡", "↔": "≡", "<->": "≡", "<=>": "≡", "(": "(", ")": ")"}
# 结合力由弱到强：≡ < ⊃ < ∨,⊻ < · < ~
BINARY = [("≡",), ("⊃",), ("∨", "⊻"), ("·",)]


def tokenize(s):
    pos, out = 0, []
    s = s.strip()
    while pos < len(s):
        m = TOKEN_RE.match(s, pos)
        if not m or m.end() == pos:
            raise SyntaxError(f"无法识别的记号：'{s[pos:]}'")
        op, name = m.groups()
        if op:
            out.append(("op", SYM[op]))
        elif name.lower() in WORD_OPS:
            out.append(("op", WORD_OPS[name.lower()]))
        else:
            out.append(("var", name))
        pos = m.end()
    return out


class Parser:
    def __init__(self, text):
        self.toks, self.i, self.text = tokenize(text), 0, text

    def peek(self):
        return self.toks[self.i] if self.i < len(self.toks) else (None, None)

    def take(self):
        tok = self.peek()
        self.i += 1
        return tok

    def parse(self):
        node = self.level(0)
        if self.i != len(self.toks):
            raise SyntaxError(f"'{self.text}' 在第 {self.i + 1} 个记号处多出内容")
        return node

    def level(self, k):
        if k == len(BINARY):
            return self.unary()
        left = self.level(k + 1)
        ops = BINARY[k]
        if ops == ("⊃",):  # 蕴涵右结合：p⊃q⊃r 读作 p⊃(q⊃r)
            if self.peek() == ("op", "⊃"):
                self.take()
                return ("⊃", left, self.level(k))
            return left
        while self.peek()[0] == "op" and self.peek()[1] in ops:
            op = self.take()[1]
            left = (op, left, self.level(k + 1))
        return left

    def unary(self):
        kind, val = self.take()
        if (kind, val) == ("op", "~"):
            return ("~", self.unary())
        if (kind, val) == ("op", "("):
            node = self.level(0)
            if self.take() != ("op", ")"):
                raise SyntaxError(f"'{self.text}' 括号不配对")
            return node
        if kind == "var":
            return ("var", val)
        if kind is None:
            raise SyntaxError(f"'{self.text}' 不完整，结尾缺少语句")
        raise SyntaxError(f"'{self.text}' 语法错误，近 '{val}'")


def parse(text):
    return Parser(text).parse()


def variables(node, acc=None):
    acc = [] if acc is None else acc
    if node[0] == "var":
        if node[1] not in acc:
            acc.append(node[1])
    else:
        for child in node[1:]:
            variables(child, acc)
    return acc


def ev(node, env):
    op = node[0]
    if op == "var":
        return env[node[1]]
    if op == "~":
        return not ev(node[1], env)
    a, b = ev(node[1], env), ev(node[2], env)
    return {"·": a and b, "∨": a or b, "⊻": a != b,
            "⊃": (not a) or b, "≡": a == b}[op]


def show(node, top=True):
    op = node[0]
    if op == "var":
        return node[1]
    if op == "~":
        return "~" + show(node[1], False)
    s = f"{show(node[1], False)}{op}{show(node[2], False)}"
    return s if top else f"({s})"


def rows(names):
    # 排列：TT…T 在前，FF…F 在后
    return list(itertools.product((True, False), repeat=len(names)))


def collect_vars(nodes):
    names = []
    for n in nodes:
        for v in variables(n):
            if v not in names:
                names.append(v)
    return names


def tv(b):
    return "T" if b else "F"


def width(text):
    return sum(2 if unicodedata.east_asian_width(ch) in "WF" else 1 for ch in text)


def pad(text, w):
    return text + " " * (w - width(text))


def print_table(nodes, labels):
    names = collect_vars(nodes)
    heads = names + labels
    widths = [width(h) + 2 for h in heads]
    print("    " + "".join(pad(h, w) for h, w in zip(heads, widths)))
    for i, vals in enumerate(rows(names), 1):
        env = dict(zip(names, vals))
        cells = [tv(v) for v in vals] + [tv(ev(n, env)) for n in nodes]
        print(f"{i:<4}" + "".join(pad(c, w) for c, w in zip(cells, widths)))


def cmd_table(args):
    nodes = [parse(f) for f in args.formulas]
    print_table(nodes, [show(n) for n in nodes])


def cmd_taut(args):
    node = parse(args.formula)
    names = variables(node)
    vals = [ev(node, dict(zip(names, r))) for r in rows(names)]
    if all(vals):
        print(f"{show(node)}：套套络基（tautology，在一切真假可能之下皆真）")
    elif not any(vals):
        print(f"{show(node)}：矛盾式（在一切真假可能之下皆假）")
    else:
        print(f"{show(node)}：适然式（有真有假，其真假须靠经验决定）")
    print_table([node], [show(node)])


def cmd_equiv(args):
    a, b = parse(args.f1), parse(args.f2)
    names = collect_vars([a, b])
    diff = [r for r in rows(names) if ev(a, dict(zip(names, r))) != ev(b, dict(zip(names, r)))]
    print(f"{show(a)} 与 {show(b)}：" + ("相等（真值表逐行相同）" if not diff else "不相等"))
    print_table([a, b], [show(a), show(b)])


def argue(premises, conclusion):
    nodes = premises + [conclusion]
    names = collect_vars(nodes)
    bad = []
    for r in rows(names):
        env = dict(zip(names, r))
        if all(ev(p, env) for p in premises) and not ev(conclusion, env):
            bad.append(env)
    return names, bad


def cmd_argue(args):
    premises = [parse(p) for p in args.premises]
    concl = parse(args.conclusion)
    names, bad = argue(premises, concl)
    for p in premises:
        print(f"  {show(p)}")
    print("  ————————")
    print(f"  ∴{show(concl)}\n")
    if not bad:
        print("有效（V）：凡前题皆真之行，结论无一不真。")
    else:
        print(f"无效（I）：有 {len(bad)} 行前题皆真而结论假，例如：")
        for env in bad:
            print("  " + "，".join(f"{k}={tv(v)}" for k, v in env.items()))
    print()
    print_table(premises + [concl], [show(p) for p in premises] + ["∴" + show(concl)])


CATALOG = [
    ("条件推论", [
        ("肯定前件（离断原则）", ["p⊃q", "p"], "q"),
        ("否定后件", ["p⊃q", "~q"], "~p"),
        ("否定前件（谬误）", ["p⊃q", "~p"], "~q"),
        ("肯定后件（谬误）", ["p⊃q", "q"], "p"),
        ("充足而又必须：否定前件", ["p≡q", "~p"], "~q"),
        ("充足而又必须：肯定后件", ["p≡q", "q"], "p"),
        ("三段式的蕴涵传达", ["p⊃q", "q⊃r"], "p⊃r"),
    ]),
    ("选取推论（相容的或）", [
        ("否定其一 → 肯定另一（须穷尽）", ["p∨q", "~p"], "q"),
        ("肯定其一 → 否定另一（须不相容）", ["p∨q", "p"], "~q"),
    ]),
    ("选取推论（加'不相容'前题）", [
        ("不相容：肯定其一 → 否定另一", ["p∨q", "~(p·q)", "p"], "~q"),
        ("不相容而不穷尽：否定其一", ["~(p·q)", "~p"], "q"),
        ("不相容而穷尽（⊻）：否定其一", ["p⊻q", "~p"], "q"),
        ("不相容而穷尽（⊻）：肯定其一", ["p⊻q", "p"], "~q"),
    ]),
    ("二难式", [
        ("简单肯定前件式", ["p⊃r", "q⊃r", "p∨q"], "r"),
        ("简单否定后件式", ["p⊃q", "p⊃r", "~q∨~r"], "~p"),
        ("复合肯定前件式", ["p⊃q", "r⊃s", "p∨r"], "q∨s"),
        ("复合否定后件式", ["p⊃q", "r⊃s", "~q∨~s"], "~p∨~r"),
        ("误用：否定前件式（谬误）", ["p⊃r", "q⊃r", "~p∨~q"], "~r"),
    ]),
]


def cmd_forms(args):
    for title, items in CATALOG:
        print(f"【{title}】")
        for name, prem, concl in items:
            names, bad = argue([parse(p) for p in prem], parse(concl))
            mark = "有效 V" if not bad else "无效 I"
            print(f"  {mark}  {name}：{'，'.join(prem)} ∴{concl}")
        print()
    print("说明：'或'在本工具中是相容的或；选取推论中的'相容/不相容、穷尽/不穷尽'"
          "须作为额外前题明白写出（不相容 = ~(p·q)，穷尽 = p∨q），推论才有确定结论。")


def main():
    ap = argparse.ArgumentParser(description="真值表与外部推论检验")
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("table", help="列真值表")
    p.add_argument("formulas", nargs="+")
    p.set_defaults(fn=cmd_table)
    p = sub.add_parser("taut", help="判定恒真/矛盾/适然")
    p.add_argument("formula")
    p.set_defaults(fn=cmd_taut)
    p = sub.add_parser("equiv", help="判定两式是否相等")
    p.add_argument("f1")
    p.add_argument("f2")
    p.set_defaults(fn=cmd_equiv)
    p = sub.add_parser("argue", help="检验前题能否推出结论")
    p.add_argument("premises", nargs="+")
    p.add_argument("--conclusion", "-c", required=True)
    p.set_defaults(fn=cmd_argue)
    p = sub.add_parser("forms", help="推论形式有效性总表")
    p.set_defaults(fn=cmd_forms)
    args = ap.parse_args()
    try:
        args.fn(args)
    except SyntaxError as e:
        sys.exit(f"式子有误：{e}")


if __name__ == "__main__":
    main()
