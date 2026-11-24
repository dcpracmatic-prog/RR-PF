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


def test_rtruediv():
    # Sin __rtruediv__, `1 / MNE(2)` lanzaba TypeError aunque
    # __radd__/__rmul__/__rsub__ ya existian.
    assert (1 / MNE(2)).exact == Fraction(1, 2)
    assert (Fraction(1, 3) / MNE(2)).exact == Fraction(1, 6)
    assert (2 / MNE(Fraction(1, 3))).exact == 6
    assert (MNE(1) / MNE(2)).exact == Fraction(1, 2)
    # Divisor intervalo: el reciproco acota el valor real.
    lo, hi = (1 / MNE(2, Fraction(1, 10))).bounds()
    assert lo <= Fraction(1, 2) <= hi
    # Divisor que contiene cero sigue lanzando ZeroDivisionError.
    try:
        1 / MNE(0, Fraction(1, 10))
    except ZeroDivisionError:
        pass
    else:
        raise AssertionError("debió lanzar ZeroDivisionError")


def test_hash_consistent_with_eq():
    # Definir __eq__ sin __hash__ dejaba MNE sin hash (unhashable):
    # ni set ni dict lo aceptaban.
    assert hash(MNE(Fraction(1, 3))) == hash(Fraction(1, 3))
    assert hash(MNE(1)) == hash(1) == hash(Fraction(1, 1))
    assert hash(MNE(Fraction(1, 3))) == hash(MNE.parse("0.[3]"))
    # Valores iguales son intercambiables como claves/miembros.
    assert len({MNE(Fraction(1, 3)), Fraction(1, 3), MNE.parse("0.[3]")}) == 1
    d = {MNE(2): "dos"}
    assert d[Fraction(2, 1)] == "dos"
    # Intervalos: el hash va por sus cotas, como __eq__.
    a = MNE(0, Fraction(1, 10))
    b = MNE(0, Fraction(1, 10))
    assert hash(a) == hash(b) and len({a, b}) == 1
    assert len({a, MNE(0)}) == 2


def test_contains_real():
    outer = MNE(0, Fraction(1, 10))  # [-1/10, 1/10]
    # Escalares: extremos incluidos, fuera excluido (sin cambio).
    assert outer.contains(Fraction(1, 10))
    assert outer.contains(Fraction(-1, 10))
    assert not outer.contains(Fraction(1, 5))
    # Intervalo entero dentro.
    assert outer.contains(MNE(0, Fraction(1, 100)))
    assert outer.contains(MNE(Fraction(1, 20), Fraction(1, 20)))  # [0, 1/10]
    # Centrado dentro pero sobresaliendo: el codigo anterior decia True
    # porque solo miraba el centro; la contencion real es False.
    assert not outer.contains(MNE(0, Fraction(1, 5)))
    assert not outer.contains(MNE(Fraction(1, 20), Fraction(1, 5)))
    # Valor exacto como argumento intervalo.
    assert outer.contains(MNE(Fraction(1, 20)))
    assert not outer.contains(MNE(Fraction(1, 5)))


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
