"""Generator tests for tools/export_cases.py -> lean/RRPF/Cases.lean.

The Lean file is generated, not hand-written. These tests check that the
generator is deterministic and that the committed file is the generator's
current output (the same condition CI enforces with --check).
"""
import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def _load_export():
    spec = importlib.util.spec_from_file_location(
        "export_cases", ROOT / "tools" / "export_cases.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_render_es_determinista():
    export = _load_export()
    assert export.render() == export.render()


def test_cases_lean_comprometido_igual_a_render():
    export = _load_export()
    committed = (ROOT / "lean" / "RRPF" / "Cases.lean").read_text(encoding="utf-8")
    assert committed == export.render(), (
        "lean/RRPF/Cases.lean está desactualizado: ejecuta "
        "python tools/export_cases.py")
