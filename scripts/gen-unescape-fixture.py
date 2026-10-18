"""Generate tests/fixtures/unescape.txt from CPython's html.unescape (stdlib).

Each line: input code points (hex, space separated) TAB expected output code points.
"""
import html, html.entities as E, random, sys
cases = []
for k in sorted(E.html5):
    cases.append("&" + k)
    cases.append("&" + k + "zq;")
    cases.append("a&" + k + " b")
for n in list(range(0, 0x120)) + [0xd7ff, 0xd800, 0xdfff, 0xe000, 0xfdd0, 0xfdef, 0xfdf0, 0xfffe, 0xffff,
          0x10000, 0x1fffe, 0x10fffd, 0x10fffe, 0x10ffff, 0x110000, 10**30]:
    cases += ["&#%d;" % n, "&#%d" % n, "&#x%x;" % n, "&#X%X" % n]
rng = random.Random(20261018)
alpha = list("&#;xX0123456789abcdefltgampquonbsp ;<\t\n") + ["é", "こ"]
for _ in range(3000):
    cases.append("".join(rng.choice(alpha) for _ in range(rng.randint(0, 16))))
out = []
for c in cases:
    enc = lambda s: " ".join("%x" % ord(ch) for ch in s)
    out.append(enc(c) + "\t" + enc(html.unescape(c)))
sys.stdout.write("\n".join(out) + "\n")
