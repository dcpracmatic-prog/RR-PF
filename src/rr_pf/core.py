"""RR-PF core: exact rational numbers and rational intervals that enclose them.

Every value is a ``fractions.Fraction``. There is no hidden rounding: the
sum of exact rationals is exact, so Kahan summation is unnecessary here.
The class is still named ``MNE`` for API stability with earlier versions.

Notes on behaviour (kept from v3):
- ``MNE(x)`` interprets str/Decimal/float by their decimal representation:
  ``MNE(0.1)`` is 1/10. ``MNE.from_float(0.1)`` is the exact binary value.
- ``sqrt`` is exact for rationals whose numerator and denominator are both
  perfect squares; otherwise it returns a rational enclosure with
  ``10**-digits`` width.
- ``a / b`` raises ZeroDivisionError when the divisor's interval contains 0.

The mathematical correspondence between these intervals and the Lean model
in ``lean/RRPF`` is documented in ``docs/CORRESPONDENCE.md``.
"""
from __future__ import annotations

from fractions import Fraction
from decimal import Decimal
from math import isqrt
import re


def as_fraction(value):
    if isinstance(value, Fraction):
        return value
    if isinstance(value, int):
        return Fraction(value)
    return Fraction(str(value))


def _is_square(n: int):
    if n < 0:
        return None
    r = isqrt(n)
    return r if r * r == n else None


class MNE:
    """Valor racional exacto o intervalo racional que lo acota."""

    __slots__ = ("_lo", "_hi")

    def __init__(self, value, err=0):
        if isinstance(value, MNE):
            radius = as_fraction(err)
            if radius < 0:
                raise ValueError("err debe ser no negativo")
            self._lo = value._lo - radius
            self._hi = value._hi + radius
            return
        center = as_fraction(value)
        radius = as_fraction(err)
        if radius < 0:
            raise ValueError("err debe ser no negativo")
        self._lo = center - radius
        self._hi = center + radius

    @classmethod
    def from_float(cls, x: float) -> "MNE":
        """El valor binario real del float, exacto como Fraction.

        Distinto de MNE(0.1), que es el decimal 1/10 por la regla
        documentada de as_fraction. Aqui no se esconde nada:
        from_float(0.1) = 3602879701896397/36028797018963968.
        """
        obj = object.__new__(cls)
        f = Fraction(x)
        obj._lo = f
        obj._hi = f
        return obj

    @classmethod
    def _from_bounds(cls, lo, hi):
        if lo > hi:
            raise ValueError("intervalo inválido")
        obj = object.__new__(cls)
        obj._lo = lo
        obj._hi = hi
        return obj

    @classmethod
    def parse(cls, text):
        """Acepta enteros, decimales, fracciones, periodicos [ ], ( )
        y ... ; tambien ".5"."""
        t = str(text).strip()
        if "/" in t:
            return cls(Fraction(t))
        if "(" in t and ")" in t:
            t = t.replace("(", "[").replace(")", "]")
        if t.endswith("..."):
            base = t[:-3]
            if "." not in base:
                raise ValueError(f"No se puede inferir periodo de {text!r}")
            entero, dec = base.split(".", 1)
            if len(dec) < 2 or dec[-1] != dec[-2]:
                raise ValueError(f"No se puede inferir periodo de {text!r}")
            digito = dec[-1]
            i = len(dec)
            while i > 0 and dec[i - 1] == digito:
                i -= 1
            no_per = dec[: i + 1] if i < len(dec) else dec
            if set(dec) == {digito}:
                no_per = ""
            t = f"{entero}.{no_per}[{digito}]" if no_per else f"{entero}.[{digito}]"

        match = re.fullmatch(r"([+-]?)(\d*)(?:\.(\d*))?(?:\[(\d+)\])?", t)
        if not match:
            raise ValueError(f"Formato no válido: {text!r}")
        sign_text, whole, finite, repeat = match.groups()
        if whole == "" and finite == "" and repeat is None:
            raise ValueError(f"Formato no válido: {text!r}")
        sign = -1 if sign_text == "-" else 1
        whole = whole or "0"
        finite = finite or ""
        if repeat is None:
            digits = whole + finite
            denominator = 10 ** len(finite)
            return cls(sign * Fraction(int(digits), denominator))
        if "." not in t:
            raise ValueError("Un período debe seguir al punto decimal")
        prefix = int(whole + finite)
        full = int(whole + finite + repeat)
        denominator = 10 ** len(finite) * (10 ** len(repeat) - 1)
        return cls(sign * Fraction(full - prefix, denominator))

    @property
    def exact(self):
        return self._lo if self._lo == self._hi else None

    @property
    def center(self):
        return (self._lo + self._hi) / 2

    @property
    def radius(self):
        return (self._hi - self._lo) / 2

    def bounds(self):
        return self._lo, self._hi

    def contains(self, value) -> bool:
        # Real containment. For a scalar (or an exact value) this is the
        # endpoint check lo <= v <= hi. For an interval argument, checking
        # only its center is wrong: an interval can be centered inside
        # while sticking out on either side. The whole interval must lie
        # inside: lo <= value._lo and value._hi <= hi.
        if isinstance(value, MNE):
            return self._lo <= value._lo and value._hi <= self._hi
        return self._lo <= as_fraction(value) <= self._hi

    def __add__(self, other):
        other = other if isinstance(other, MNE) else MNE(other)
        return self._from_bounds(self._lo + other._lo, self._hi + other._hi)

    __radd__ = __add__

    def __neg__(self):
        return self._from_bounds(-self._hi, -self._lo)

    def __sub__(self, other):
        other = other if isinstance(other, MNE) else MNE(other)
        return self + (-other)

    def __rsub__(self, other):
        return MNE(other) - self

    def __mul__(self, other):
        other = other if isinstance(other, MNE) else MNE(other)
        products = (self._lo * other._lo, self._lo * other._hi,
                    self._hi * other._lo, self._hi * other._hi)
        return self._from_bounds(min(products), max(products))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = other if isinstance(other, MNE) else MNE(other)
        if other._lo <= 0 <= other._hi:
            raise ZeroDivisionError("El divisor contiene cero en su intervalo")
        reciprocals = (1 / other._lo, 1 / other._hi)
        reciprocal = self._from_bounds(min(reciprocals), max(reciprocals))
        return self * reciprocal

    def __rtruediv__(self, other):
        # Reflected division: `1 / MNE(2)`, `Fraction(1, 3) / MNE(2)`.
        # Without this, only MNE-on-the-left divided; anything on the
        # left raised TypeError even though __radd__/__rmul__/__rsub__
        # already exist. Delegates to __truediv__, so a divisor whose
        # interval contains zero still raises ZeroDivisionError.
        return MNE(other) / self

    @staticmethod
    def _sqrt_bounds(value, digits):
        if value < 0:
            raise ValueError("raíz de número negativo")
        scale = 10 ** digits
        k = isqrt((value.numerator * scale * scale) // value.denominator)
        lower = Fraction(k, scale)
        if lower * lower == value:
            return lower, lower
        return lower, Fraction(k + 1, scale)

    def sqrt(self, digits=50):
        if not isinstance(digits, int) or digits < 0:
            raise ValueError("digits debe ser un entero no negativo")
        if self._lo < 0:
            raise ValueError("El intervalo incluye valores negativos")
        # CORRECCION 1: exactitud por cuadrados perfectos, antes
        # de acotar por digitos. Asi sqrt(4/9) = 2/3 exacto.
        if self.exact is not None:
            num_r = _is_square(self.exact.numerator)
            den_r = _is_square(self.exact.denominator)
            if num_r is not None and den_r is not None:
                return MNE(Fraction(num_r, den_r))
        lower, _ = self._sqrt_bounds(self._lo, digits)
        _, upper = self._sqrt_bounds(self._hi, digits)
        return self._from_bounds(lower, upper)

    def __eq__(self, other):
        if isinstance(other, MNE):
            return self._lo == other._lo and self._hi == other._hi
        try:
            return self.exact is not None and self.exact == as_fraction(other)
        except Exception:
            return NotImplemented

    def __hash__(self):
        # Defining __eq__ without __hash__ made MNE unhashable
        # (Python sets __hash__ to None), so values could not be used
        # in sets or as dict keys. The hash must agree with __eq__:
        # an exact value hashes like the Fraction it equals, so
        # hash(MNE(1, 3)) == hash(Fraction(1, 3)) and equal values
        # stay interchangeable as keys; an interval (never equal to
        # a non-MNE) hashes from its bounds, which is what __eq__
        # compares for two intervals.
        if self.exact is not None:
            return hash(self.exact)
        return hash((self._lo, self._hi))

    def __str__(self):
        if self.exact is not None:
            return str(self.exact)
        return f"[{self._lo}, {self._hi}]"

    def __repr__(self):
        return f"MNE({self})"


def kahan_sum(values):
    """Suma de valores como MNE. Con racionales exactos es exacta,
    asi que no necesita compensacion: ese es el punto.
    Acepta MNE, Fraction, Decimal, int, float y str."""
    total = MNE(0)
    for v in values:
        total = total + (v if isinstance(v, MNE) else MNE(v))
    return total
