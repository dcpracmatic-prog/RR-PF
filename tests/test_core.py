"""Tests for rr_pf.core (the MNE class). Run with `pytest`."""
from fractions import Fraction
from decimal import Decimal

from rr_pf import MNE, kahan_sum


def test_parse_corchetes():
    assert MNE.parse("0.[3]").exact == Fraction(1, 3)
    assert MNE.parse("12.[3]").exact == Fraction(37, 3)
    assert MNE.parse("0.1[6]").exact == Fraction(1, 6)
    assert MNE.parse("0.[142857]").exact == Fraction(1, 7)


def test_parse_signo():
    assert MNE.parse("-0.25").exact == Fraction(-1, 4)
    assert MNE.parse("-0.[3]").exact == Fraction(-1, 3)
    assert MNE.parse("1/3").exact == Fraction(1, 3)


def test_parse_parentesis_y_puntos():
    assert MNE.parse("0.(3)").exact == Fraction(1, 3)
    assert MNE.parse("0.1(6)").exact == Fraction(1, 6)
    assert MNE.parse("0.1666...").exact == Fraction(1, 6)
    assert MNE.parse(".5").exact == Fraction(1, 2)
    assert MNE.parse("-.5").exact == Fraction(-1, 2)


def test_exactos():
    assert (MNE.parse("0.[3]") * 3).exact == 1
    assert (MNE.parse("0." + "9" * 20) / 4).exact == Fraction(10**20 - 1, 4 * 10**20)
    assert (MNE.parse("0.7512944554") / 4).exact == Fraction(7512944554, 10**10) / 4
    assert sum([MNE("0.1")] * 10, MNE(0)).exact == 1


def test_sqrt_exacto():
    assert MNE(Fraction(1, 4)).sqrt().exact == Fraction(1, 2)
    assert MNE(Fraction(4, 9)).sqrt().exact == Fraction(2, 3)
    assert MNE(Fraction(4)).sqrt().exact == 2


def test_sqrt2_intervalo():
    lo, hi = MNE(Fraction(2)).sqrt().bounds()
    assert hi - lo == Fraction(1, 10**50)
    assert lo * lo <= 2 <= hi * hi


def test_copia_mne_aproximado():
    aprox = MNE(1, Fraction(1, 10**10))
    assert MNE(aprox).bounds() == aprox.bounds()


def test_from_float():
    assert MNE.from_float(0.1).exact == Fraction(0.1)
    assert MNE(0.1).exact == Fraction(1, 10)
    lo, hi = MNE.from_float(0.1).bounds()
    assert lo <= Decimal(0.1) <= hi


def test_intervalo_division():
    a = MNE(1, Fraction(1, 10**10))
    b = MNE(3, Fraction(1, 10**10))
    lo, hi = (a / b).bounds()
    assert lo <= Fraction(1, 3) <= hi


def test_suma_larga_exacta():
    assert sum([MNE("0.01")] * 100000, MNE(0)).exact == 1000
    assert kahan_sum([MNE.parse("0.1")] * 10).exact == 1
    assert kahan_sum([0.1] * 10).exact == 1
    s = 0.0
    for _ in range(100000):
        s += 0.01
    assert abs(s - 1000.0) > 0


def test_errores():
    try:
        MNE(1) / MNE(0, Fraction(1, 10))
    except ZeroDivisionError:
        pass
    else:
        raise AssertionError("debió lanzar ZeroDivisionError")
    try:
        MNE(1, -1)
    except ValueError:
        pass
    else:
        raise AssertionError("debió lanzar ValueError")


if __name__ == "__main__":
    tests = [(n, f) for n, f in sorted(globals().items())
             if n.startswith("test_") and callable(f)]
    for name, fn in tests:
        fn()
        print(f"PASS {name}")
    print(f"{len(tests)} pruebas en verde")
