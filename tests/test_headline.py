"""The README's headline numbers against the committed certificate transcripts (run by `make tests`).

`make check` first compares every transcript with a fresh run of its script, so together the two show that each
number printed in the README is what a certificate proves, rounded the safe way: every exponent E in the README is at
least the certified upper bound and within 2e-10 of it (the scripts print their bound rounded at the 10th digit), and every transcript ends with its PASS line.
"""
import os
import re
import unittest

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
CERT = os.path.join(ROOT, "certificates")

# (transcript, regex whose first group is the certified upper bound on E, the README's figure)
EXPONENTS = [
    ("cert_eps.out", r"max E\s+<= ([0-9.]+)", "0.4999983316"),
    ("cert_stage3.out", r"E3 <= ([0-9.]+)", "0.499990922021"),
    ("stage4/cert_stage4.out", r"DET  s=11/100[^\n]*?E <= ([0-9.]+)", "0.4998322132"),
    ("stage4/cert_stage4plus.out", r"\[E\+\] DET[^\n]*?E_det <= ([0-9.]+)", "0.4997369618"),
    ("stage5/cert_stage5.out", r"\[E\] R3:[^\n]*?E_det <= ([0-9.]+)", "0.4989524521"),
    ("stage5b/cert_stage5b.out", r"\[E\] R4b-min[^\n]*?E_det <= ([0-9.]+)", "0.4986298176"),
]
PASS = {"cert_gamma.out": "CERTIFICATE PASS", "cert_eps.out": "CERTIFICATE PASS", "cert_explicit.out": "ALL PASS",
        "cert_explicit_b16.out": "ALL PASS", "cert_explicit_b17.out": "ALL PASS", "cert_stage3.out": "CERTIFICATE PASS",
        "stage4/cert_stage4.out": "CERTIFICATE PASS", "stage4/cert_stage4plus.out": "STAGE 4+ CERTIFICATE PASS",
        "stage4/check_stage4.out": "STAGE 4 CHECK PASS", "stage5/cert_stage5.out": "STAGE 5 CERTIFICATE PASS",
        "stage5/check_stage5.out": "STAGE 5 CHECK PASS", "stage5b/cert_stage5b.out": "STAGE 5b CERTIFICATE PASS"}


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


class Headline(unittest.TestCase):
    def test_pass_lines(self):
        for name, line in PASS.items():
            self.assertEqual(read(os.path.join(CERT, name)).rstrip("\n").split("\n")[-1].strip(), line, name)

    def test_exponents(self):
        readme = read(os.path.join(ROOT, "README.md"))
        for name, rx, shown in EXPONENTS:
            m = re.search(rx, read(os.path.join(CERT, name)))
            self.assertIsNotNone(m, name)
            cert = float(m.group(1))
            self.assertIn(shown, readme, name)
            self.assertGreaterEqual(float(shown), cert, name)
            self.assertLess(float(shown) - cert, 2e-10, name)

    def test_stage1_gamma(self):
        self.assertIn("0.0101041782", read(os.path.join(CERT, "cert_gamma.out")))

    def test_explicit_table(self):
        out = read(os.path.join(CERT, "cert_explicit_b17.out"))
        for n0 in ("1.20e32", "1.59e11", "4.90e10"):
            self.assertIn(n0, out)


if __name__ == "__main__":
    unittest.main()
