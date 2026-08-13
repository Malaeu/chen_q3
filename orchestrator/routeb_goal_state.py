"""Shared lifecycle parsing for physical Route B goal files."""

from __future__ import annotations

import re
from pathlib import Path
from typing import Any

import yaml

MACHINE_HEADER_RE = re.compile(
    r"```(?:yaml|yml)\s*\n(.*?)```", re.DOTALL | re.IGNORECASE
)
STATUS_RE = re.compile(r"^[A-Z][A-Z0-9_]*$")
PAUSED_STATUSES = frozenset({"PAUSED_RESTORABLE"})


class _UniqueStringLoader(yaml.BaseLoader):
    """YAML loader with string scalars and duplicate-key rejection.

    Goal identifiers such as ``057`` are lexical identifiers, not YAML 1.1
    octal integers.  ``BaseLoader`` preserves them byte-semantically as
    strings; the custom mapping constructor prevents a later duplicate key
    from silently replacing the first machine value.
    """


def _construct_unique_mapping(
    loader: _UniqueStringLoader, node: yaml.nodes.MappingNode, deep: bool = False
) -> dict[str, Any]:
    mapping: dict[str, Any] = {}
    for key_node, value_node in node.value:
        key = loader.construct_object(key_node, deep=deep)
        if not isinstance(key, str) or key in mapping:
            raise yaml.constructor.ConstructorError(
                "while constructing a machine header",
                node.start_mark,
                f"duplicate or non-string key: {key!r}",
                key_node.start_mark,
            )
        mapping[key] = loader.construct_object(value_node, deep=deep)
    return mapping


_UniqueStringLoader.add_constructor(
    yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG,
    _construct_unique_mapping,
)


class _UniqueSafeLoader(yaml.SafeLoader):
    """Typed YAML loader which rejects duplicate keys at every depth."""


_UniqueSafeLoader.add_constructor(
    yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG,
    _construct_unique_mapping,
)


def load_unique_yaml(text: str) -> Any:
    """Load typed YAML while rejecting duplicate or non-string mapping keys."""
    return yaml.load(text, Loader=_UniqueSafeLoader)


def goal_machine_header_text(text: str) -> dict[str, Any] | None:
    """Parse the first machine header without coercing lexical identifiers."""
    header = MACHINE_HEADER_RE.search(text)
    if header is None:
        return None
    try:
        payload = yaml.load(header.group(1), Loader=_UniqueStringLoader)
    except yaml.YAMLError:
        return None
    return payload if isinstance(payload, dict) else None


def goal_status_text(text: str) -> str | None:
    """Return ``STATUS`` only from the first YAML machine header."""
    payload = goal_machine_header_text(text)
    if payload is None:
        return None
    status = payload.get("STATUS")
    return status if isinstance(status, str) and STATUS_RE.fullmatch(status) else None


def goal_status(path: Path) -> str | None:
    return goal_status_text(path.read_text(encoding="utf-8"))


def is_paused_goal(path: Path) -> bool:
    return goal_status(path) in PAUSED_STATUSES
