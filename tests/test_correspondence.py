"""Python <-> Lean correspondence checks on random rational intervals.

The Lean side (lean/RRPF) proves, for the interval model, that:
  - the map  [lo, hi] -> (val, bound) = ((lo+hi)/2, (hi-lo)/2)  sends
    membership t in [lo, hi]  to  |t - val| <= bound           (mem_iff)
  - add and sub commute with the map exactly                    (toBN_add, toBN_sub)
  - the Python product/quotient endpoints are inside the
    Lean enclosure given by BoundedNum.mul / BoundedNum.div     (mul_hull_sound, div_hull_sound)

This file checks that the *Python code* satisfies the same statements on many
random inputs, including inputs that are themselves results of earlier
operations (asymmetric intervals). It is a randomized check of the transcription,
not a formal proof about the Python source. See docs/CORRESPONDENCE.md.
"""
import random
from fractions import Fraction

import pytest

from rr_pf import MNE


def to_model(iv: MNE):
    """Map a Python interval to the Lean model pair (val, bound)."""
    return iv.center, iv.radius


def rand_frac(rng, den=50, span=20):
    return Fraction(rng.randint(-span * den, span * den), rng.randint(1, den))


def rand_interval(rng):
    lo = rand_frac(rng)
    hi = lo + Fraction(rng.randint(0, 30), rng.randint(1, 40))
    return MNE._from_bounds(lo, hi)


def rand_nonzero_away_from_zero(rng):
    """Interval not containing 0: |center| > radius, as the Lean hypothesis requires."""
    while True:
        iv = rand_interval(rng)
        lo, hi = iv.bounds()
        if lo > 0 or hi < 0:
            return iv


SEED = 20261123
N = 400


def test_mapa_add_y_sub_son_exactos():
    rng = random.Random(SEED)
    for _ in range(N):
        a, b = rand_interval(rng), rand_interval(rng)
        ma, ra = to_model(a)
        mb, rb = to_model(b)
        s = a + b
        assert to_model(s) == (ma + mb, ra + rb)        # toBN_add
        d = a - b
        assert to_model(d) == (ma - mb, ra + rb)        # toBN_sub


def test_membresia_se_preserva():
    """t in [lo, hi]  <->  |t - val| <= bound  (mem_iff)."""
    rng = random.Random(SEED + 1)
    for _ in range(N):
        iv = rand_interval(rng)
        m, r = to_model(iv)
        lo, hi = iv.bounds()
        for t in (lo, hi, (lo + hi) / 2, lo - Fraction(1, 97), hi + Fraction(1, 89)):
            assert (lo <= t <= hi) == (abs(t - m) <= r)


def test_mul_contenida_en_envolvente_lean():
    """Python product hull subset of Lean mul enclosure (mul_hull_sound)."""
    rng = random.Random(SEED + 2)
    for _ in range(N):
        a, b = rand_interval(rng), rand_interval(rng)
        ma, ra = to_model(a)
        mb, rb = to_model(b)
        R = abs(ma) * rb + abs(mb) * ra + ra * rb   # Lean BoundedNum.mul bound
        c = ma * mb
        lo, hi = (a * b).bounds()
        assert c - R <= lo and hi <= c + R


def test_mul_puntos_muestreados_en_envolvente():
    rng = random.Random(SEED + 3)
    for _ in range(N // 4):
        a, b = rand_interval(rng), rand_interval(rng)
        ma, ra = to_model(a)
        mb, rb = to_model(b)
        R = abs(ma) * rb + abs(mb) * ra + ra * rb
        alo, ahi = a.bounds()
        blo, bhi = b.bounds()
        for _ in range(5):
            t = alo + (ahi - alo) * Fraction(rng.randint(0, 100), 100)
            s = blo + (bhi - blo) * Fraction(rng.randint(0, 100), 100)
            assert abs(t * s - ma * mb) <= R             # mul_valid pointwise


def test_div_contenida_en_envolvente_lean():
    """Python quotient hull subset of Lean div enclosure (div_hull_sound)."""
    rng = random.Random(SEED + 4)
    checked = 0
    for _ in range(N):
        a = rand_interval(rng)
        b = rand_nonzero_away_from_zero(rng)
        ma, ra = to_model(a)
        mb, rb = to_model(b)
        assert abs(mb) > rb                               # Lean hypothesis h
        D = (ra * abs(mb) + abs(ma) * rb) / (abs(mb) * (abs(mb) - rb))
        c = ma / mb
        lo, hi = (a / b).bounds()
        assert c - D <= lo and hi <= c + D
        checked += 1
    assert checked == N


def test_division_por_intervalo_con_cero_se_rechaza_igual_que_lean():
    """Python raises iff 0 in [lo, hi]; Lean's hypothesis is |val| > bound."""
    rng = random.Random(SEED + 5)
    for _ in range(N):
        b = rand_interval(rng)
        m, r = to_model(b)
        lo, hi = b.bounds()
        zero_inside = lo <= 0 <= hi
        assert zero_inside == (abs(m) <= r)
        if zero_inside:
            with pytest.raises(ZeroDivisionError):
                MNE(1) / b
        else:
            MNE(1) / b  # must not raise


def test_division_muestreada_en_envolvente():
    rng = random.Random(SEED + 6)
    for _ in range(N // 4):
        a = rand_interval(rng)
        b = rand_nonzero_away_from_zero(rng)
        ma, ra = to_model(a)
        mb, rb = to_model(b)
        D = (ra * abs(mb) + abs(ma) * rb) / (abs(mb) * (abs(mb) - rb))
        alo, ahi = a.bounds()
        blo, bhi = b.bounds()
        for _ in range(5):
            t = alo + (ahi - alo) * Fraction(rng.randint(0, 100), 100)
            s = blo + (bhi - blo) * Fraction(rng.randint(0, 100), 100)
            assert abs(t / s - ma / mb) <= D              # div_valid pointwise
