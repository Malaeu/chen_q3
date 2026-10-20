#!/usr/bin/env python3
"""Run the bounded CF22 PySR pilot and certify candidates on heldout intervals.

Input rows require ``id``, ``split``, exact decimal-string ``U``, point
``features`` (logU, r, ell), matching ``feature_intervals``, and q_lower /
q_upper decimal strings.  The dataset also requires a top-level ``provenance``
value.  The model sees only point features and q_upper on train rows; Arb sees
the feature intervals and q endpoints on test rows.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import importlib.metadata
import json
import math
import os
import platform
import re
import sys
from dataclasses import dataclass
from decimal import Decimal, InvalidOperation, ROUND_CEILING, ROUND_FLOOR, localcontext
from fractions import Fraction
from functools import reduce
from operator import add, mul
from pathlib import Path
from typing import Any, Iterable, Mapping


FEATURES = ("logU", "r", "ell")
DECIMAL_RE = re.compile(r"[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?\Z")
SEED = 20261020
CANDIDATE_CONSTANTS = (
    "exact decimal literals in frozen equation, potentially rounded vs Julia search constants"
)

FIT_CONFIG: dict[str, Any] = {
    "seed": SEED,
    "deterministic": True,
    "parallelism": "serial",
    "batching": False,
    "warm_start": False,
    "precision": 64,
    "niterations": 20,
    "populations": 2,
    "population_size": 20,
    "ncycles_per_iteration": 50,
    "maxsize": 12,
    "timeout_in_seconds": 60,
    "binary_operators": ["+", "-", "*", "/"],
    "unary_operators": [],
    "parsimony": 0.001,
    "target": "q_upper",
}

JULIA_LOSS = r"""
function loss(tree, dataset::Dataset{T,L}, options)::L where {T,L}
    prediction, complete = eval_tree_array(tree, dataset.X, options)
    complete || return L(Inf)
    all(isfinite, prediction) || return L(Inf)
    y = dataset.y
    underprediction = max(maximum(y .- prediction), zero(L))
    overprediction = max.(prediction .- y, zero(L))
    return L(1000) * underprediction^2 + sum(overprediction .^2) / length(y)
end
""".strip()
JULIA_LOSS_SHA256 = hashlib.sha256(JULIA_LOSS.encode("utf-8")).hexdigest()


@dataclass(frozen=True)
class Row:
    row_id: str
    split: str
    u_text: str
    u_value: Decimal
    point_text: Mapping[str, str]
    point_value: Mapping[str, Decimal]
    interval_text: Mapping[str, tuple[str, str]]
    q_lower_text: str
    q_upper_text: str
    q_lower: Decimal
    q_upper: Decimal


def decimal_value(value: Any, field: str) -> tuple[str, Decimal]:
    if not isinstance(value, str) or not DECIMAL_RE.fullmatch(value):
        raise ValueError(f"{field} must be a finite decimal string")
    try:
        number = Decimal(value)
    except InvalidOperation as exc:
        raise ValueError(f"{field} is not a decimal string") from exc
    if not number.is_finite():
        raise ValueError(f"{field} must be finite")
    return value, number


def validate_dataset(data: Any) -> tuple[list[Row], Any]:
    """Validate the input schema, finite numerics, and scale-level split fence."""
    if not isinstance(data, dict) or not isinstance(data.get("rows"), list):
        raise ValueError("dataset must be an object with a rows array")
    if "provenance" not in data:
        raise ValueError("dataset must include top-level provenance")

    rows: list[Row] = []
    seen_ids: set[str] = set()
    train_scales: set[Decimal] = set()
    test_scales: set[Decimal] = set()
    for index, raw in enumerate(data["rows"]):
        where = f"rows[{index}]"
        if not isinstance(raw, dict):
            raise ValueError(f"{where} must be an object")
        row_id, split = raw.get("id"), raw.get("split")
        if not isinstance(row_id, str) or not row_id:
            raise ValueError(f"{where}.id must be a non-empty string")
        if row_id in seen_ids:
            raise ValueError(f"duplicate row id: {row_id}")
        seen_ids.add(row_id)
        if split not in ("train", "test"):
            raise ValueError(f"{where}.split must be 'train' or 'test'")

        # U is retained as its original decimal spelling and compared by exact
        # decimal value, so 8, 8.0, and 8e0 all identify the same scale.
        u_text, u_value = decimal_value(raw.get("U"), f"{where}.U")
        if u_value <= 0:
            raise ValueError(f"{where}.U must be positive")
        (train_scales if split == "train" else test_scales).add(u_value)

        point = raw.get("features")
        intervals = raw.get("feature_intervals")
        if not isinstance(point, dict) or not isinstance(intervals, dict):
            raise ValueError(f"{where} requires features and feature_intervals objects")
        point_text: dict[str, str] = {}
        point_value: dict[str, Decimal] = {}
        interval_text: dict[str, tuple[str, str]] = {}
        for feature in FEATURES:
            text, number = decimal_value(point.get(feature), f"{where}.features.{feature}")
            bounds = intervals.get(feature)
            if not isinstance(bounds, dict):
                raise ValueError(f"{where}.feature_intervals.{feature} must be an object")
            lo_text, lo = decimal_value(bounds.get("lower"), f"{where}.feature_intervals.{feature}.lower")
            hi_text, hi = decimal_value(bounds.get("upper"), f"{where}.feature_intervals.{feature}.upper")
            if lo > hi:
                raise ValueError(f"{where}.feature_intervals.{feature} lower exceeds upper")
            if not lo <= number <= hi:
                raise ValueError(f"{where}.features.{feature} is outside its interval")
            point_text[feature], point_value[feature] = text, number
            interval_text[feature] = (lo_text, hi_text)

        q_lower_text, q_lower = decimal_value(raw.get("q_lower"), f"{where}.q_lower")
        q_upper_text, q_upper = decimal_value(raw.get("q_upper"), f"{where}.q_upper")
        if q_lower > q_upper:
            raise ValueError(f"{where}.q_lower exceeds q_upper")
        rows.append(Row(row_id, split, u_text, u_value, point_text, point_value,
                        interval_text, q_lower_text, q_upper_text, q_lower, q_upper))

    train = [row for row in rows if row.split == "train"]
    test = [row for row in rows if row.split == "test"]
    if not train:
        raise ValueError("dataset has no train rows")
    if not test:
        raise ValueError("dataset has no test rows")
    shared_scales = train_scales & test_scales
    if shared_scales:
        shown = ", ".join(str(value) for value in sorted(shared_scales))
        raise ValueError(f"train/test share U scales: {shown}")
    return rows, data["provenance"]


def exact_fraction(value: Decimal) -> Fraction:
    return Fraction(value)


def _fraction_from_arb_endpoint(value: Any, *, upper: bool) -> Fraction:
    """Return the exact rational value of Arb's outward-rounded endpoint."""
    endpoint = value.upper() if upper else value.lower()
    mantissa, exponent = endpoint.man_exp()
    mantissa = int(mantissa)
    exponent = int(exponent)
    if exponent >= 0:
        return Fraction(mantissa * (2 ** exponent), 1)
    return Fraction(mantissa, 2 ** (-exponent))


def _fraction_json(value: Fraction) -> dict[str, str]:
    return {
        "numerator": str(value.numerator),
        "denominator": str(value.denominator),
        "text": str(value),
    }


def arb_interval(lower_text: str, upper_text: str, arb_type: Any | None = None) -> Any:
    """Create an Arb ball enclosing the full closed interval of decimal endpoints."""
    if arb_type is None:
        from flint import arb as arb_type
    return arb_type(lower_text).union(arb_type(upper_text))


def _arb_json(value: Any) -> dict[str, Any]:
    if not value.is_finite():
        raise ValueError("non-finite Arb result")
    return {
        "lower": _fraction_json(_fraction_from_arb_endpoint(value, upper=False)),
        "upper": _fraction_json(_fraction_from_arb_endpoint(value, upper=True)),
        "ball": value.str(80, more=True),
    }


def _rational_decimal_bounds(value: Fraction, digits: int = 80) -> tuple[str, str]:
    numerator, denominator = value.numerator, value.denominator
    with localcontext() as ctx:
        ctx.prec = digits
        ctx.rounding = ROUND_FLOOR
        lower = Decimal(numerator) / Decimal(denominator)
    with localcontext() as ctx:
        ctx.prec = digits
        ctx.rounding = ROUND_CEILING
        upper = Decimal(numerator) / Decimal(denominator)
    return str(lower), str(upper)


def _sympy_parse(expression: str) -> tuple[Any | None, str | None]:
    """Parse only the small arithmetic grammar allowed for certification."""
    import sympy as sp

    try:
        syntax = ast.parse(expression, mode="eval")
    except (SyntaxError, ValueError) as exc:
        return None, f"parse error: {exc}"

    allowed_binary = (ast.Add, ast.Sub, ast.Mult, ast.Div, ast.Pow)
    allowed_unary = (ast.UAdd, ast.USub)

    def check(node: ast.AST) -> None:
        if isinstance(node, ast.Expression):
            check(node.body)
        elif isinstance(node, ast.Name):
            if node.id not in FEATURES:
                raise ValueError(f"unsupported symbol {node.id!r}")
        elif isinstance(node, ast.Constant):
            if isinstance(node.value, bool) or not isinstance(node.value, (int, float)):
                raise ValueError("only numeric constants are allowed")
            if isinstance(node.value, float) and not math.isfinite(node.value):
                raise ValueError("non-finite expression constant")
        elif isinstance(node, ast.BinOp) and isinstance(node.op, allowed_binary):
            check(node.left)
            check(node.right)
        elif isinstance(node, ast.UnaryOp) and isinstance(node.op, allowed_unary):
            check(node.operand)
        else:
            raise ValueError(f"unsupported expression syntax: {type(node).__name__}")

    try:
        check(syntax)
        locals_map = {name: sp.Symbol(name) for name in FEATURES}
        # Keep syntactic divisions and powers intact: simplifying x/x to 1
        # would erase a denominator that may vanish on a feature interval.
        return sp.sympify(expression, locals=locals_map, rational=True, evaluate=False), None
    except Exception as exc:
        return None, f"unsupported expression: {type(exc).__name__}: {exc}"


def rational_constant_serializations(expression: Any) -> list[dict[str, str]]:
    """Expose every non-integer rational as directed decimal endpoints."""
    import sympy as sp

    found: dict[str, dict[str, str]] = {}
    for node in sp.preorder_traversal(expression):
        if isinstance(node, sp.Rational) and not isinstance(node, sp.Integer) and node.q != 1:
            key = str(node)
            lower, upper = _rational_decimal_bounds(Fraction(int(node.p), int(node.q)))
            found[key] = {"sympy_rational": key, "decimal_lower": lower, "decimal_upper": upper}
    return [found[key] for key in sorted(found)]


def _arb_contains_zero(value: Any) -> bool:
    return (_fraction_from_arb_endpoint(value, upper=False) <= 0
            <= _fraction_from_arb_endpoint(value, upper=True))


def evaluate_sympy_expression(expression: Any, values: Mapping[str, Any], arb_type: Any | None = None) -> Any:
    """Evaluate a parsed SymPy expression with Arb; unsupported powers fail closed."""
    import sympy as sp

    if arb_type is None:
        from flint import arb as arb_type

    symbol_values = {sp.Symbol(name): val for name, val in values.items()}

    def evaluate(node: Any) -> Any:
        if node in symbol_values:
            return symbol_values[node]
        if isinstance(node, sp.Float):
            node = sp.Rational(node)
        if isinstance(node, sp.Integer):
            return arb_type(str(int(node)))
        if isinstance(node, sp.Rational):
            from flint import fmpq

            return arb_type(fmpq(int(node.p), int(node.q)))
        if isinstance(node, sp.Float):
            return arb_type(str(node))
        if isinstance(node, sp.Add):
            return reduce(add, (evaluate(arg) for arg in node.args), arb_type(0))
        if isinstance(node, sp.Mul):
            return reduce(mul, (evaluate(arg) for arg in node.args), arb_type(1))
        if isinstance(node, sp.Pow):
            exponent = node.exp
            if not isinstance(exponent, sp.Integer):
                raise ValueError("non-integer powers are INVALID")
            power = int(exponent)
            base = evaluate(node.base)
            if power < 0 and _arb_contains_zero(base):
                raise ZeroDivisionError("denominator interval contains zero")
            return base ** power
        if isinstance(node, sp.Symbol):
            raise ValueError(f"unbound symbol {node}")
        raise ValueError(f"unsupported SymPy node: {type(node).__name__}")

    return evaluate(expression)


def classify_interval(value: Any, q_lower: Decimal, q_upper: Decimal) -> tuple[str, Fraction, Fraction]:
    """Classify by exact comparison of Arb's rigorous endpoints to decimal q bounds."""
    lower = _fraction_from_arb_endpoint(value, upper=False)
    upper = _fraction_from_arb_endpoint(value, upper=True)
    if lower >= exact_fraction(q_upper):
        return "ACCEPT", lower, upper
    if upper < exact_fraction(q_lower):
        return "REFUTE", lower, upper
    return "UNRESOLVED", lower, upper


def evaluate_candidate_on_row(expression: Any, row: Row, arb_type: Any | None = None) -> dict[str, Any]:
    """Evaluate a candidate on one test row and return its finite interval margins."""
    if arb_type is None:
        from flint import arb as arb_type
    values = {
        feature: arb_interval(*row.interval_text[feature], arb_type=arb_type)
        for feature in FEATURES
    }
    try:
        result = evaluate_sympy_expression(expression, values, arb_type=arb_type)
        if not result.is_finite():
            raise ValueError("expression produced a non-finite Arb result")
    except Exception as exc:
        return {
            "row_id": row.row_id,
            "U": row.u_text,
            "status": "INVALID",
            "reason": f"{type(exc).__name__}: {exc}",
        }

    status, lower, upper = classify_interval(result, row.q_lower, row.q_upper)
    q_lower = exact_fraction(row.q_lower)
    q_upper = exact_fraction(row.q_upper)
    return {
        "row_id": row.row_id,
        "U": row.u_text,
        "status": status,
        "g": _arb_json(result),
        "acceptance_margin_lower": _fraction_json(lower - q_upper),
        "refutation_margin_upper": _fraction_json(upper - q_lower),
    }


def _overall_status(row_results: Iterable[Mapping[str, Any]], *, scope: str = "heldout") -> str:
    statuses = [item["status"] for item in row_results]
    if any(status == "INVALID" for status in statuses):
        return "INVALID"
    if all(status == "ACCEPT" for status in statuses):
        return f"FINITE_{scope.upper()}_ACCEPT"
    if any(status == "REFUTE" for status in statuses):
        return f"FINITE_{scope.upper()}_REFUTE"
    return "UNRESOLVED"


def _combined_status(training_results: Iterable[Mapping[str, Any]],
                     heldout_results: Iterable[Mapping[str, Any]]) -> str:
    statuses = [item["status"] for item in (*training_results, *heldout_results)]
    if statuses and all(status == "ACCEPT" for status in statuses):
        return "EMPIRICAL_CANDIDATE"
    if any(status == "REFUTE" for status in statuses):
        return "FINITE_CHECK_REFUTED"
    if any(status == "INVALID" for status in statuses):
        return "INVALID"
    return "UNRESOLVED"


def _json_value(value: Any) -> Any:
    if hasattr(value, "item"):
        value = value.item()
    if isinstance(value, float) and not math.isfinite(value):
        return repr(value)
    if isinstance(value, Decimal):
        return str(value)
    if value is None or isinstance(value, (str, int, float, bool)):
        return value
    return str(value)


def _write_json_exclusive(path: Path, payload: Any, *, readonly: bool = False) -> str:
    encoded = (json.dumps(payload, indent=2, sort_keys=True, allow_nan=False) + "\n").encode("utf-8")
    with path.open("xb") as handle:
        handle.write(encoded)
        handle.flush()
        os.fsync(handle.fileno())
    if readonly:
        path.chmod(0o444)
    return hashlib.sha256(encoded).hexdigest()


def _package_versions() -> dict[str, str | None]:
    names = ("pysr", "numpy", "sympy", "python-flint", "juliacall")
    versions: dict[str, str | None] = {}
    for name in names:
        try:
            versions[name] = importlib.metadata.version(name)
        except importlib.metadata.PackageNotFoundError:
            versions[name] = None
    return versions


def _julia_metadata() -> dict[str, Any]:
    """Query the Julia runtime already initialized by PySR, if available."""
    try:
        from pysr.julia_import import jl

        version = str(jl.seval("VERSION"))
        bindir = str(jl.seval("Sys.BINDIR"))
        project_raw = str(jl.seval("Base.active_project()"))
        project_path = Path(project_raw) if project_raw not in ("nothing", "None", "") else None
        manifest_path = project_path.with_name("Manifest.toml") if project_path else None
        manifest_exists = bool(manifest_path and manifest_path.is_file())
        manifest_sha256 = (
            hashlib.sha256(manifest_path.read_bytes()).hexdigest() if manifest_exists else None
        )
        return {
            "available": True,
            "version": version,
            "bindir": bindir,
            "active_project": str(project_path) if project_path else None,
            "manifest_path": str(manifest_path) if manifest_exists else None,
            "manifest_sha256": manifest_sha256,
        }
    except Exception as exc:
        return {"available": False, "reason": f"{type(exc).__name__}: {exc}"}


def _equation_records(model: Any) -> list[dict[str, Any]]:
    equations = model.equations_
    if equations is None or len(equations) == 0:
        raise RuntimeError("PySR returned an empty hall of fame")
    records: list[dict[str, Any]] = []
    for index, (_, row) in enumerate(equations.iterrows()):
        expression = row.get("equation")
        raw_expression = str(expression)
        parsed, parse_error = _sympy_parse(raw_expression)
        record: dict[str, Any] = {
            "candidate_id": f"hof-{index:03d}",
            "equation": raw_expression,
        }
        if parsed is not None:
            import sympy as sp

            record["sympy_expression"] = sp.sstr(parsed)
            record["rational_constant_decimals"] = rational_constant_serializations(parsed)
        else:
            record["expression_parse_error"] = parse_error
        for field in ("complexity", "loss", "score"):
            if field in row:
                record[field] = _json_value(row[field])
        records.append(record)
    return records


def _float_features(row: Row) -> list[float]:
    values = [float(row.point_value[name]) for name in FEATURES]
    if not all(math.isfinite(value) for value in values):
        raise ValueError(f"row {row.row_id} has point features outside finite float64 range")
    return values


def run(dataset_path: Path, output_path: Path) -> dict[str, Any]:
    raw_bytes = dataset_path.read_bytes()
    input_sha256 = hashlib.sha256(raw_bytes).hexdigest()
    try:
        dataset = json.loads(raw_bytes)
    except json.JSONDecodeError as exc:
        raise ValueError(f"invalid dataset JSON: {exc}") from exc
    rows, provenance = validate_dataset(dataset)
    train_rows = [row for row in rows if row.split == "train"]
    test_rows = [row for row in rows if row.split == "test"]

    output_path.mkdir(parents=True, exist_ok=True)
    pysr_output = output_path / "pysr"
    for artifact in ("input_manifest.json", "candidates.json", "results.json", "pysr"):
        if (output_path / artifact).exists():
            raise FileExistsError(f"output artifact already exists: {output_path / artifact}")
    prefit_manifest = {
        "schema": "cf22_pysr_input_manifest.v1",
        "dataset_sha256": input_sha256,
        "dataset_path": str(dataset_path.resolve()),
        "provenance": provenance,
        "train_rows": len(train_rows),
        "test_rows": len(test_rows),
        "train_ids": [row.row_id for row in train_rows],
        "test_ids": [row.row_id for row in test_rows],
        "fit_config": FIT_CONFIG,
        "loss_source": JULIA_LOSS,
        "loss_source_sha256": JULIA_LOSS_SHA256,
        "candidate_constants": CANDIDATE_CONSTANTS,
    }
    _write_json_exclusive(output_path / "input_manifest.json", prefit_manifest, readonly=True)

    import numpy as np
    from pysr import PySRRegressor

    x_train = np.asarray([_float_features(row) for row in train_rows], dtype=np.float64)
    y_train = np.asarray([float(row.q_upper) for row in train_rows], dtype=np.float64)
    if not np.isfinite(y_train).all():
        raise ValueError("train q_upper values must fit finite float64")

    model = PySRRegressor(
        niterations=FIT_CONFIG["niterations"],
        populations=FIT_CONFIG["populations"],
        population_size=FIT_CONFIG["population_size"],
        ncycles_per_iteration=FIT_CONFIG["ncycles_per_iteration"],
        maxsize=FIT_CONFIG["maxsize"],
        timeout_in_seconds=FIT_CONFIG["timeout_in_seconds"],
        binary_operators=list(FIT_CONFIG["binary_operators"]),
        unary_operators=list(FIT_CONFIG["unary_operators"]),
        precision=FIT_CONFIG["precision"],
        random_state=FIT_CONFIG["seed"],
        deterministic=FIT_CONFIG["deterministic"],
        parallelism=FIT_CONFIG["parallelism"],
        batching=FIT_CONFIG["batching"],
        warm_start=FIT_CONFIG["warm_start"],
        parsimony=FIT_CONFIG["parsimony"],
        loss_function=JULIA_LOSS,
        output_directory=str(pysr_output),
        verbosity=0,
        progress=False,
    )
    model.fit(x_train, y_train, variable_names=list(FEATURES))

    candidates = _equation_records(model)
    environment = {
        "python": sys.version,
        "platform": platform.platform(),
        "packages": _package_versions(),
        "julia": _julia_metadata(),
    }
    candidate_payload = {
        "schema": "cf22_pysr_candidates.v1",
        "dataset_sha256": input_sha256,
        "provenance": provenance,
        "fit_config": FIT_CONFIG,
        "loss_source": JULIA_LOSS,
        "loss_source_sha256": JULIA_LOSS_SHA256,
        "candidate_constants": CANDIDATE_CONSTANTS,
        "environment": environment,
        "train_row_ids": [row.row_id for row in train_rows],
        "candidate_scope": "finite heldout interval checks only; no universal claim",
        "candidates": candidates,
    }
    candidate_sha256 = _write_json_exclusive(output_path / "candidates.json", candidate_payload, readonly=True)

    # Heldout rows are used only after the complete hall of fame is frozen.
    from flint import arb, ctx

    ctx.prec = 256
    candidate_results: list[dict[str, Any]] = []
    for candidate in candidates:
        parsed, parse_error = _sympy_parse(candidate["equation"])
        training_results: list[dict[str, Any]] = []
        row_results: list[dict[str, Any]] = []
        if parsed is None:
            training_results = [
                {"row_id": row.row_id, "U": row.u_text, "status": "INVALID", "reason": parse_error}
                for row in train_rows
            ]
            row_results = [
                {"row_id": row.row_id, "U": row.u_text, "status": "INVALID", "reason": parse_error}
                for row in test_rows
            ]
        else:
            for row in train_rows:
                training_results.append(evaluate_candidate_on_row(parsed, row, arb_type=arb))
            for row in test_rows:
                row_results.append(evaluate_candidate_on_row(parsed, row, arb_type=arb))
        heldout_status = _overall_status(row_results, scope="heldout")
        training_status = _overall_status(training_results, scope="train")
        overall_status = _combined_status(training_results, row_results)
        usable = overall_status == "EMPIRICAL_CANDIDATE"
        candidate_results.append({
            "candidate_id": candidate["candidate_id"],
            "equation": candidate["equation"],
            # `status` remains the finite heldout verdict for compatibility.
            "status": heldout_status,
            "heldout_status": heldout_status,
            "training_status": training_status,
            "overall_status": overall_status,
            "usable": usable,
            "training_per_row": training_results,
            "per_row": row_results,
        })

    best_train_row = max(train_rows, key=lambda row: row.q_upper)
    baseline_value = best_train_row.q_upper_text
    baseline_expression = _sympy_parse(baseline_value)[0]
    if baseline_expression is None:
        raise ValueError("train-only baseline could not be parsed")
    baseline_training_rows = [evaluate_candidate_on_row(baseline_expression, row, arb_type=arb) for row in train_rows]
    baseline_rows = [evaluate_candidate_on_row(baseline_expression, row, arb_type=arb) for row in test_rows]
    baseline_overall_status = _combined_status(baseline_training_rows, baseline_rows)
    baseline_usable = baseline_overall_status == "EMPIRICAL_CANDIDATE"
    baseline = {
        "label": "empirical no-new-gain baseline",
        "kind": "train_max_q_upper_constant",
        "value": baseline_value,
        "selected_train_row_id": best_train_row.row_id,
        "status": _overall_status(baseline_rows, scope="heldout"),
        "training_status": _overall_status(baseline_training_rows, scope="train"),
        "overall_status": baseline_overall_status,
        "usable": baseline_usable,
        "training_per_row": baseline_training_rows,
        "per_row": baseline_rows,
    }

    results = {
        "schema": "cf22_pysr_results.v1",
        "dataset_sha256": input_sha256,
        "candidate_sha256": candidate_sha256,
        "scope": "finite heldout interval checks only; no universal or analytic-envelope claim",
        "baseline": baseline,
        "candidates": candidate_results,
    }
    _write_json_exclusive(output_path / "results.json", results)
    return results


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dataset", type=Path, required=True, help="input JSON dataset")
    parser.add_argument("--output", type=Path, required=True, help="new or empty output directory")
    args = parser.parse_args(argv)
    result = run(args.dataset, args.output)
    print(json.dumps({
        "dataset_sha256": result["dataset_sha256"],
        "candidate_sha256": result["candidate_sha256"],
        "baseline_status": result["baseline"]["status"],
        "candidate_statuses": [candidate["status"] for candidate in result["candidates"]],
    }, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
