"""Performance measurements for rr_pf (MNE class). Usage: python bench.py"""
import sys
import time

from fractions import Fraction
from rr_pf import MNE, kahan_sum


def bench(label, fn, n=1):
    fn()
    t0 = time.perf_counter()
    for _ in range(n):
        fn()
    dt = (time.perf_counter() - t0) / n
    print(f"{label}: {dt * 1000:.3f} ms")
    return dt


if __name__ == "__main__":
    print("== Performance rr_pf, Python", sys.version.split()[0], "==")
    bench("parse 0.[142857] x1000", lambda: [MNE.parse("0.[142857]") for _ in range(1000)])
    bench("suma exacta 100k x 0.01", lambda: sum([MNE("0.01")] * 100000, MNE(0)))
    bench("suma float 100k x 0.01", lambda: sum([0.01] * 100000))

    def float_loop():
        s = 0.0
        for _ in range(100000):
            s += 0.01
        return s

    bench("suma float loop 100k x 0.01", float_loop)
    bench("suma exacta 1M x 0.01", lambda: sum([MNE("0.01")] * 1000000, MNE(0)))
    bench("mul exacta 10k (1/3*3)", lambda: [MNE.parse("0.[3]") * 3 for _ in range(10000)])
    bench("sqrt(2) digits=50", lambda: MNE(Fraction(2)).sqrt())
    bench("kahan_sum MNE 100k", lambda: kahan_sum([MNE("0.01")] * 100000))
    s_float = float_loop()
    print(f"float loop 100k resultado={s_float!r} error={abs(s_float - 1000.0):.3e}")
    print(f"MNE 100k resultado={sum([MNE('0.01')] * 100000, MNE(0)).exact} error=0")
