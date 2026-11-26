"""Tests for the exact CSR oracle, including a mutant it catches and float does not.

The mutant models a real bug class: a "sparsity cleanup" that drops entries
whose magnitude is below a threshold. When the dropped term is smaller than
the float resolution of the surviving terms, a float-vs-float comparison
cannot see the difference, because both sides round the same way. The
Fraction oracle keeps the term and sees it.
"""
import math
from fractions import Fraction
from decimal import Decimal

import pytest

from rr_pf import MNE, ExactCSR, csr_matvec_exact, kahan_sum
from rr_pf.oracle import exact


# ---------- reference implementations under test -------------------------

def float_matvec(indptr, indices, data, x):
    """Plain float CSR product. Reference for float-vs-float comparisons."""
    y = []
    for i in range(len(indptr) - 1):
        s = 0.0
        for k in range(indptr[i], indptr[i + 1]):
            s += data[k] * x[indices[k]]
        y.append(s)
    return y


def mutant_matvec(indptr, indices, data, x, threshold=1e-12):
    """MUTANT: drops entries with |v| < threshold before multiplying.

    Works for float or Fraction data, so the same bug can be run through
    both the float comparison and the exact oracle.
    """
    y = []
    for i in range(len(indptr) - 1):
        s = 0
        for k in range(indptr[i], indptr[i + 1]):
            if abs(data[k]) < threshold:
                continue  # <- the injected error
            s += data[k] * x[indices[k]]
        y.append(s)
    return y


def float_close(a, b):
    return all(math.isclose(p, q, rel_tol=1e-9, abs_tol=0.0) for p, q in zip(a, b))


# ---------- oracle basics ------------------------------------------------

def test_producto_exacto_pequeno():
    A = ExactCSR.from_dense([[1, "1/3"], [0, 2]])
    assert A.matvec([3, 3]) == [Fraction(4), Fraction(6)]


def test_csr_directo_y_fracciones_exactas():
    y = csr_matvec_exact((2, 2), [0, 2, 3], [0, 1, 1], ["1", "0.5", "2"], [1, 1])
    assert y == [Fraction(3, 2), Fraction(2)]


def test_decimal_y_str_son_exactos():
    assert exact("0.1") == Fraction(1, 10)
    assert exact(Decimal("0.1")) == Fraction(1, 10)
    assert exact("1/3") == Fraction(1, 3)


def test_float_se_rechaza():
    with pytest.raises(TypeError):
        exact(0.1)
    with pytest.raises(TypeError):
        ExactCSR.from_dense([[0.1]])


def test_validacion_csr():
    with pytest.raises(ValueError):
        ExactCSR((2, 2), [0, 1], [0], ["1"])          # indptr de longitud incorrecta
    with pytest.raises(ValueError):
        ExactCSR((1, 2), [0, 1], [5], ["1"])          # columna fuera de rango
    with pytest.raises(ValueError):
        ExactCSR((2, 2), [0, 2, 1], [0, 1], ["1", "1"])  # indptr decreciente
    with pytest.raises(ValueError):
        ExactCSR((1, 1), [0, 1], [0], ["1"]).matvec([1, 2])  # x de longitud errada


def test_resultado_coincide_con_mne_intervalos():
    """MNE interval arithmetic must enclose the exact oracle result."""
    A = ExactCSR.from_dense([["1/3", 0, "2"], [0, "0.1", "1/7"]])
    x = ["3", "2", "1/5"]
    exacto = A.matvec(x)
    for i in range(A.shape[0]):
        acc = MNE(0)
        for k in range(A.indptr[i], A.indptr[i + 1]):
            acc = acc + MNE(A.data[k]) * MNE(x[A.indices[k]])
        lo, hi = acc.bounds()
        assert lo <= exacto[i] <= hi


# ---------- the mutant: float-vs-float is blind, the oracle is not -------

@pytest.mark.parametrize("k", [20, 30, 40])
def test_oracle_detecta_mutante_que_float_no_ve(k):
    # Row = [1, 10**-k], x = [1, 1]. True value: 1 + 10**-k.
    tiny = Fraction(1, 10**k)
    indptr, indices = [0, 2], [0, 1]
    x = [Fraction(1), Fraction(1)]

    # 1) float-vs-float: 1.0 + 10**-k rounds to 1.0, so the mutant's output is
    #    bit-identical to the reference. Blind even with `==`, not only with tolerance.
    data_f = [1.0, float(tiny)]
    ref_f = float_matvec(indptr, indices, data_f, [1.0, 1.0])
    mut_f = mutant_matvec(indptr, indices, data_f, [1.0, 1.0])
    assert float_close(mut_f, ref_f), "el test float-vs-float debe pasar (ciego)"
    assert mut_f == ref_f

    # 2) exact oracle: the mutant drops 10**-k and returns 1 instead of 1+10**-k.
    data_q = [Fraction(1), tiny]
    oracle = csr_matvec_exact((1, 2), indptr, indices, [1, tiny], x)
    mut_q = mutant_matvec(indptr, indices, data_q, x)
    assert mut_q != oracle, "el oráculo debe detectar el mutante"
    assert oracle == [1 + tiny]


def test_float_si_ve_el_termino_cuando_cabe_en_float():
    """Control: at 10**-13 the term survives in float (1.0 + 1e-13 != 1.0), so a
    bitwise float comparison does catch the mutant. The blind spot is precision,
    not a general weakness of float tests."""
    tiny = Fraction(1, 10**13)
    indptr, indices = [0, 2], [0, 1]
    ref_f = float_matvec(indptr, indices, [1.0, float(tiny)], [1.0, 1.0])
    mut_f = mutant_matvec(indptr, indices, [1.0, float(tiny)], [1.0, 1.0],
                          threshold=1e-12)
    assert mut_f != ref_f


def test_mutante_de_indice_lo_detectan_ambos():
    """A gross bug (off-by-one column) is caught by float and by the oracle."""
    A = ExactCSR.from_dense([[1, 2], [3, 4]])
    x = [1, 1]
    correct = A.matvec(x)
    shifted = [Fraction(1 + 2), Fraction(3 + 4)]
    wrong = [Fraction(1 + 1), Fraction(3 + 3)]  # columna desplazada
    assert correct != wrong and correct == shifted


# ---------- spmm: exact A @ B, column by column ---------------------------

from rr_pf.oracle import check_bounds, assert_within_bounds  # noqa: E402


def test_spmm_producto_pequeno_exacto():
    A = ExactCSR.from_dense([[1, "1/2"], [0, 3]])
    B = [[2, "1/3"], [4, "1/5"]]
    assert A.spmm(B) == [
        [Fraction(4), Fraction(13, 30)],
        [Fraction(12), Fraction(3, 5)],
    ]


def test_spmm_columna_a_columna_es_matvec():
    A = ExactCSR.from_dense([["1/3", 0, 2], [0, "0.1", "1/7"], [5, 0, 0]])
    B = [[3, "1/2", 0], [2, 1, "-4/3"], ["1/5", 7, "9"]]
    Y = A.spmm(B)
    for j in range(3):
        col = [B[i][j] for i in range(3)]
        assert [Y[i][j] for i in range(3)] == A.matvec(col)


def test_spmm_vacio():
    Z = ExactCSR.from_dense([[0, 0], [0, 0]])
    assert Z.spmm([[1, 2], [3, 4]]) == [[0, 0], [0, 0]]
    assert ExactCSR.from_dense([]).spmm([]) == []


def test_spmm_validacion_y_float_en_b():
    A = ExactCSR.from_dense([[1, 2]])
    with pytest.raises(ValueError):
        A.spmm([[1], [2], [3]])          # B con filas de más
    with pytest.raises(ValueError):
        A.spmm([[1, 2], [3]])            # B irregular
    with pytest.raises(TypeError):
        ExactCSR.from_dense([[1]]).spmm([[0.5]])  # float en B


# ---------- bound checker ------------------------------------------------

def test_check_bounds_frontera_inclusiva():
    expected = [[Fraction(0)]]
    # error exactamente igual a la cota: dentro (<=)
    assert check_bounds([[Fraction(1, 2)]], expected, "1/2") == []
    # error un poco mayor: fuera
    bad = check_bounds([["0.5000000000001"]], expected, "1/2")
    assert len(bad) == 1 and (bad[0].row, bad[0].col) == (0, 0)
    assert bad[0].error == Fraction("0.5000000000001")
    # la cota no puede ser float
    with pytest.raises(TypeError):
        check_bounds([[0]], expected, 1e-9)


def test_check_bounds_float_binario_y_nan():
    expected = [[Fraction(1, 10)]]
    # float se lee como valor binario: Fraction(0.1) - 1/10 ~ 5.55e-18
    assert check_bounds([[0.1]], expected, Fraction(1, 10**18)) != []
    assert check_bounds([[0.1]], expected, Fraction(1, 10**17)) == []
    # NaN no tiene error finito: se marca con error None
    nan = check_bounds([[float("nan")]], expected, 1)
    assert len(nan) == 1 and nan[0].error is None


# ---------- mutants the oracle catches -----------------------------------

def test_cancelacion_float_ciega_oraculo_no():
    # [1e16, 1, -1e16] . [1, 1, 1] = 1. In float, 1e16 + 1.0 rounds back to 1e16.
    indptr, indices = [0, 3], [0, 1, 2]
    ref_f = float_matvec(indptr, indices, [1e16, 1.0, -1e16], [1.0, 1.0, 1.0])
    assert ref_f == [0.0]          # referencia float: también ciega
    exact_y = csr_matvec_exact((1, 3), indptr, indices, [10**16, 1, -10**16],
                               [1, 1, 1])
    assert exact_y == [Fraction(1)]
    assert kahan_sum([1e16, 1.0, -1e16]).exact == 1


def test_mutante_b_transpuesta_lo_caza_con_cota_cero():
    A = [[1, 2], [3, 4]]
    B = [[1, 5], [6, 7]]
    correct = ExactCSR.from_dense(A).spmm(B)
    assert correct == [[13, 19], [27, 43]]
    # MUTANTE: usa B transpuesta
    Bt = [[B[j][i] for j in range(2)] for i in range(2)]
    mutant = ExactCSR.from_dense(A).spmm(Bt)
    assert_within_bounds(correct, correct, 0)
    with pytest.raises(AssertionError):
        assert_within_bounds(mutant, correct, 0)
