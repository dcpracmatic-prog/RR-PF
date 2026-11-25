# RR-PF

Números racionales exactos e intervalos racionales que los acotan, con un
oráculo basado en `Fraction` y un modelo en Lean 4 de la aritmética de
intervalos.

Antes se publicaba como `mne`; se renombró porque ese nombre está ocupado en
PyPI. La clase principal sigue llamándose `MNE` por compatibilidad de API.

Versión en inglés: [README.md](README.md).

## Instalación

```bash
pip install .            # desde un clon
pip install ".[test]"    # con pytest
```

## Uso

```python
from fractions import Fraction
from rr_pf import MNE

MNE.parse("0.[3]") * 3          # 1
MNE.parse("0.1[6]")             # 1/6
MNE.parse("0.[142857]")         # 1/7
MNE.parse("-0.25")              # -1/4
MNE(Fraction(4, 9)).sqrt()      # 2/3
MNE.from_float(0.1)             # valor binario exacto del float
```

`MNE(0.1)` es el decimal `1/10`, por regla documentada.
`MNE.from_float(0.1)` es el binario real: `3602879701896397/36028797018963968`.

Dividir entre un intervalo que contiene al 0 lanza `ZeroDivisionError`.

## Oráculo

`rr_pf.oracle` ofrece un producto matriz-vector disperso exacto (`ExactCSR`,
`csr_matvec_exact`) para usarlo como referencia lenta en las pruebas de otros
proyectos. Rechaza entradas `float` a propósito, para que una ambigüedad
binario/decimal no pase en silencio.

## Modelo en Lean

El formalismo está en [`lean/`](lean/). Define números acotados
`(val, bound)` y operaciones de intervalos sobre `ℝ`, y prueba:

- `add_valid`, `mul_valid`, `sub_valid`, `div_valid`: las cotas son correctas;
- `add_exact`, `mul_exact`, `div_exact`, `add_mono_bound`;
- `RInterval.toBN_add`, `toBN_sub`: la suma y la resta de estilo Python
  corresponden exactamente;
- `RInterval.mul_hull_sound`, `div_hull_sound`: los resultados de multiplicar
  y dividir de estilo Python caen dentro de la envolvente de Lean;
- `RRPF.Sqrt.pySqrt_enclosure`: el `sqrt` de Python sobre un intervalo envuelve
  a `√x` para cada `x` del intervalo; `RRPF.Literals.periodic_closed`: la forma
  cerrada de un decimal periódico; `RRPF.Literals.den_dyadic_pow_two`: los
  denominadores de `from_float` son potencias de dos.

`lean/RRPF/Cases.lean` lo genera `tools/export_cases.py` y comprueba 89
resultados de Python contra la especificación en Lean. El CI falla si el
archivo versionado difiere de la salida del generador.

Sin `sorry`. Cada teorema depende solo de `propext`, `Classical.choice` y
`Quot.sound`.

[`docs/CORRESPONDENCE.md`](docs/CORRESPONDENCE.md) indica, para cada
afirmación, si está probada en Lean, solo probada en Python o fuera de
alcance, y en qué dirección se cumple (igualdad o contención).

## Pruebas

```bash
pip install ".[test]"
pytest -q
```

La suite tiene 44 pruebas. Cubren la aritmética básica, el oráculo, el
generador de casos de Lean y una comprobación aleatoria (semilla fija) de
correspondencia entre el código Python y las fórmulas de Lean.

La suite del oráculo incluye un mutante que descarta términos pequeños. La
comparación float contra float no lo detecta para algunos tamaños; el oráculo
exacto sí.

## Build de Lean

```bash
cd lean
lake exe cache get   # descarga la caché de Mathlib
lake build           # debe terminar con "Build completed successfully"
```

Toolchain: `leanprover/lean4:v4.14.0`, Mathlib `v4.14.0`.

## Integración continua

`.github/workflows/ci.yml` ejecuta `pytest` en Python y `lake build` en Lean,
verifica la lista de axiomas de los teoremas clave y comprueba que los casos
de Lean generados están al día.

## Licencia

Ver [LICENSE](LICENSE).
