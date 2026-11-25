"""Exact sparse matrix-vector product over ``Fraction``: a test oracle.

Intended as a slow, obviously-correct reference for other projects' test
suites (HBAG, MORPH): feed it a small CSR matrix and a vector, compare
against the implementation under test.

Entries are converted only through exact paths: ``int``, ``Fraction``,
``str`` (e.g. ``"1/10"``, ``"0.1"``) and ``Decimal``. ``float`` is rejected
on purpose: ``float(0.1)`` is a binary value, and silently choosing either
reading of it would hide the very class of error this oracle is for.
Convert floats explicitly, e.g. ``Fraction(0.1)``, if you mean the binary value.
"""
from __future__ import annotations

import math
from decimal import Decimal
from fractions import Fraction
from typing import Iterable, NamedTuple, Sequence


def exact(value) -> Fraction:
    """Convert one entry to Fraction without rounding. Rejects float."""
    if isinstance(value, Fraction):
        return value
    if isinstance(value, bool):
        raise TypeError("bool is not a matrix entry")
    if isinstance(value, int):
        return Fraction(value)
    if isinstance(value, Decimal):
        return Fraction(value)
    if isinstance(value, str):
        return Fraction(value.strip())
    if isinstance(value, float):
        raise TypeError(
            "float rejected by the oracle; pass Fraction(x) for the binary value "
            "or a str/Decimal for the decimal one"
        )
    raise TypeError(f"unsupported entry type: {type(value).__name__}")


class ExactCSR:
    """CSR matrix with Fraction entries. Validated on construction."""

    __slots__ = ("shape", "indptr", "indices", "data")

    def __init__(self, shape, indptr, indices, data):
        nrows, ncols = (int(shape[0]), int(shape[1]))
        if nrows < 0 or ncols < 0:
            raise ValueError("shape must be non-negative")
        indptr = tuple(int(p) for p in indptr)
        indices = tuple(int(j) for j in indices)
        data = tuple(exact(v) for v in data)
        if len(indptr) != nrows + 1:
            raise ValueError(f"indptr must have length nrows+1 = {nrows + 1}")
        if indptr[0] != 0:
            raise ValueError("indptr[0] must be 0")
        if any(b < a for a, b in zip(indptr, indptr[1:])):
            raise ValueError("indptr must be non-decreasing")
        nnz = indptr[-1]
        if len(indices) != nnz or len(data) != nnz:
            raise ValueError("indices and data must have length indptr[-1]")
        if any(not (0 <= j < ncols) for j in indices):
            raise ValueError("column index out of range")
        self.shape = (nrows, ncols)
        self.indptr = indptr
        self.indices = indices
        self.data = data

    @classmethod
    def from_dense(cls, rows: Sequence[Sequence]) -> "ExactCSR":
        """Build from a list of rows; zero entries are not stored."""
        nrows = len(rows)
        ncols = len(rows[0]) if nrows else 0
        if any(len(r) != ncols for r in rows):
            raise ValueError("ragged rows")
        indptr, indices, data = [0], [], []
        for row in rows:
            for j, v in enumerate(row):
                fv = exact(v)
                if fv != 0:
                    indices.append(j)
                    data.append(fv)
            indptr.append(len(indices))
        return cls((nrows, ncols), indptr, indices, data)

    def matvec(self, x: Iterable) -> list[Fraction]:
        """Exact y = A @ x. Returns a list of Fraction of length nrows."""
        xs = [exact(v) for v in x]
        if len(xs) != self.shape[1]:
            raise ValueError(f"x must have length {self.shape[1]}, got {len(xs)}")
        y: list[Fraction] = []
        for i in range(self.shape[0]):
            acc = Fraction(0)
            for k in range(self.indptr[i], self.indptr[i + 1]):
                acc += self.data[k] * xs[self.indices[k]]
            y.append(acc)
        return y


    def spmm(self, B: Sequence[Sequence]) -> list[list[Fraction]]:
        """Exact Y = A @ B for a dense B of shape (ncols, K).

        Returns nrows lists of K Fractions. Entries of B go through ``exact``,
        so floats are rejected here as well.
        """
        rows = [[exact(v) for v in row] for row in B]
        if len(rows) != self.shape[1]:
            raise ValueError(f"B must have {self.shape[1]} rows, got {len(rows)}")
        K = len(rows[0]) if rows else 0
        if any(len(r) != K for r in rows):
            raise ValueError("ragged B")
        Y: list[list[Fraction]] = []
        for i in range(self.shape[0]):
            acc = [Fraction(0)] * K
            for k in range(self.indptr[i], self.indptr[i + 1]):
                a = self.data[k]
                brow = rows[self.indices[k]]
                for j in range(K):
                    acc[j] += a * brow[j]
            Y.append(acc)
        return Y


def csr_matvec_exact(shape, indptr, indices, data, x) -> list[Fraction]:
    """Convenience wrapper: validate a CSR matrix and return exact A @ x."""
    return ExactCSR(shape, indptr, indices, data).matvec(x)


class Violation(NamedTuple):
    """One entry outside its bound. ``error`` is None when approx is not finite."""

    row: int
    col: int
    approx: object
    expected: Fraction
    error: Fraction | None


def _approx_fraction(value) -> Fraction | None:
    """Exact value of an approximation: floats as their binary value
    (``Fraction(x)``), other types through ``exact``. None if not finite."""
    if isinstance(value, float):
        if not math.isfinite(value):
            return None
        return Fraction(value)
    return exact(value)


def check_bounds(approx, expected, bound) -> list[Violation]:
    """Per-entry check: every |approx[i][j] - expected[i][j]| must be <= bound.

    ``expected`` is an exact matrix (e.g. the output of ``ExactCSR.spmm``).
    ``approx`` may hold floats, read as their binary values. ``bound`` goes
    through ``exact``, so a float bound is rejected. Returns the violations;
    an empty list means every entry is within bound.
    """
    tol = exact(bound)
    if tol < 0:
        raise ValueError("bound must be non-negative")
    if len(approx) != len(expected):
        raise ValueError(f"approx has {len(approx)} rows, expected {len(expected)}")
    out: list[Violation] = []
    for i, (arow, erow) in enumerate(zip(approx, expected)):
        if len(arow) != len(erow):
            raise ValueError(f"row {i}: approx has {len(arow)} entries, expected {len(erow)}")
        for j, (a, e) in enumerate(zip(arow, erow)):
            fe = exact(e)
            fa = _approx_fraction(a)
            if fa is None:
                out.append(Violation(i, j, a, fe, None))
                continue
            err = abs(fa - fe)
            if err > tol:
                out.append(Violation(i, j, a, fe, err))
    return out


def assert_within_bounds(approx, expected, bound) -> None:
    """Test helper: raise AssertionError listing the first violations, if any."""
    bad = check_bounds(approx, expected, bound)
    if bad:
        shown = "; ".join(
            f"[{v.row},{v.col}] approx={v.approx!r} expected={v.expected} error={v.error}"
            for v in bad[:5]
        )
        raise AssertionError(f"{len(bad)} entries outside bound {bound}: {shown}")
