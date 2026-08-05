#!/usr/bin/env python3
"""Wave 3 addendum: migrate the PRIME_COMB family — knowledge nearly written off as clutter.

Found only because the owner insisted that the un-migrated remainder be examined rather than
dismissed ("а может там что-нибудь путное есть"). Three files, all frozen 2026-06-12, none of
them referenced by any atlas:

  docs/PRIME_COMB_MODULARITY_ATLAS_CARD_01.md  — "what plays the role modular forms played
      for E8?", with sources spot-checked against primaries and one attribution corrected
  docs/PRIME_COMB_STRUCTURE_PROOF.md
  docs/PRIME_COMB_STRUCTURE_TRACK_B.md

They carry two hard negative results that belong in `kill`, not in a forgotten markdown file:
Kurasov–Sarnak (the prime comb is provably NOT a Fourier quasicrystal — kills the crystalline
measure / Lee-Yang transplant) and Conrey–Li (a natural de Branges positivity certificate for
RH actually fails). Both are external theorems, so `status='standing'`: nothing we do makes
them go away.

The full texts go in as dossiers so the ranking of candidate mechanisms stays searchable.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import kb  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
FILES = ["docs/PRIME_COMB_MODULARITY_ATLAS_CARD_01.md",
         "docs/PRIME_COMB_STRUCTURE_PROOF.md",
         "docs/PRIME_COMB_STRUCTURE_TRACK_B.md"]
CARD = FILES[0]

KILLS = [
    {"id": "PRIME_COMB_NOT_A_FOURIER_QUASICRYSTAL", "unit_type": "wall",
     "subject": "Transplanting Fourier-quasicrystal / Lee-Yang crystalline-measure machinery "
                "to the prime side of the explicit formula",
     "status": "standing",
     "reason": "THEOREM (Kurasov–Sarnak 2020): the prime/zero explicit-formula measure is "
               "provably NOT a Fourier quasicrystal — and this holds even under RH. The "
               "crystalline-measure toolkit therefore cannot be transplanted directly.",
     "scope_negation": "Does not kill positivity/LP approaches as such; it kills the specific "
                       "hope of importing quasicrystal structure as 'modularity for primes'.",
     "rollback_target": None,
     "replacement": "Closest genuine structural analogue is the Connes–Consani–Moscovici "
                    "prolate/Sonin/Toeplitz line (Carathéodory–Fejér mechanism), which natively "
                    "encodes two-sided positivity-plus-sign constraints.",
     "forbidden_future_move": "Do not look for 'modularity for the prime comb' via crystalline "
                              "measures or Lee-Yang; the obstruction is a theorem, not a gap.",
     "stop_code": "PRIME_COMB_NOT_FQ_KURASOV_SARNAK",
     "track": "TrackB", "recorded_at": "2026-06-12", "source_file": CARD},
    {"id": "DE_BRANGES_POSITIVITY_CERTIFICATE_FOR_RH_FAILS", "unit_type": "wall",
     "subject": "A natural de Branges-type positivity certificate as a route to RH",
     "status": "standing",
     "reason": "Conrey–Li (arXiv:math/9812166) proved the natural de Branges positivity "
               "condition actually FAILS. Recorded here because the card also corrects a "
               "common misattribution: this result is Conrey–Li, not Sarnak.",
     "scope_negation": "Kills the naive de Branges certificate; does not kill "
                       "Beurling–Selberg / Carneiro–Littmann–Vaaler extremal-function work, "
                       "which runs unconditionally on the explicit formula.",
     "rollback_target": None,
     "replacement": "Carneiro–Littmann–Vaaler extremal functions — the most directly "
                    "transferable unconditional toolkit for edge-strip defects.",
     "forbidden_future_move": "Do not cite a de Branges positivity certificate for RH as "
                              "available; and do not attribute its failure to Sarnak.",
     "stop_code": "DE_BRANGES_CERTIFICATE_FAILS_CONREY_LI",
     "track": "TrackB", "recorded_at": "2026-06-12", "source_file": CARD},
    {"id": "NO_COHN_ELKIES_DUAL_CERTIFICATE_FOR_ZERO_LOCATION", "unit_type": "wall",
     "subject": "A Cohn–Elkies-style single dual certificate for zero location / RH",
     "status": "standing",
     "reason": "No such certificate has ever been built. The literature has dual certificates "
               "only for proportions of zeros, prime gaps and first-zero heights — never for "
               "zero location itself.",
     "scope_negation": "A statement about the state of the art, not an impossibility theorem: "
                       "unlike the Kurasov–Sarnak wall, this one could in principle fall.",
     "rollback_target": None, "replacement": None,
     "forbidden_future_move": "Do not assume a single magic dual certificate exists to be "
                              "found by analogy with E8 sphere packing.",
     "stop_code": "NO_DUAL_CERTIFICATE_FOR_ZERO_LOCATION",
     "track": "TrackB", "recorded_at": "2026-06-12", "source_file": CARD},
]

EVIDENCE = [(k["id"], "md", CARD) for k in KILLS] + [
    ("PRIME_COMB_NOT_A_FOURIER_QUASICRYSTAL", "source", "Kurasov–Sarnak 2020"),
    ("DE_BRANGES_POSITIVITY_CERTIFICATE_FOR_RH_FAILS", "source", "arXiv:math/9812166"),
]
ALIASES = [
    ("DE_BRANGES_POSITIVITY_CERTIFICATE_FOR_RH_FAILS", "Sarnak de Branges condition",
     "MISATTRIBUTION corrected on the card 2026-06-12: the failure result is Conrey–Li"),
]


def main() -> int:
    conn = kb.connect()
    kb.insert_kills(conn, KILLS, evidence=EVIDENCE, aliases=ALIASES)

    dossiers = []
    for rel in FILES:
        p = REPO / rel
        if not p.exists():
            print(f"  [warn] missing {rel}")
            continue
        text = p.read_text(errors="ignore")
        title = next((l.lstrip("# ").strip() for l in text.splitlines()
                      if l.startswith("# ")), p.stem)
        dossiers.append((p.stem, title, "2026-06-12", "frozen strategy/review material",
                         None, "dossier", "prime-comb,track-b,literature", "high",
                         text, rel))
    conn.executemany(
        "INSERT OR REPLACE INTO dossier (slug, title, date, status_token, verdict, subtype, "
        "tags, priority, body_md, source_file) VALUES (?,?,?,?,?,?,?,?,?,?)", dossiers)
    conn.execute("INSERT INTO dossier_fts(dossier_fts) VALUES('delete-all')")
    conn.execute("INSERT INTO dossier_fts(rowid, title, status_token, verdict, body_md) "
                 "SELECT rowid, title, status_token, verdict, body_md FROM dossier")
    conn.executemany(
        "INSERT OR REPLACE INTO source_ledger (source_file, expected_rows, migrated_at, note) "
        "VALUES (?,?,?,?)",
        [(rel, 1 + (len(KILLS) if rel == CARD else 0), "2026-08-05",
          "wave 3 addendum: PRIME_COMB family") for rel in FILES])
    conn.commit()
    print(f"migrated {len(KILLS)} standing walls + {len(dossiers)} dossiers from the "
          f"PRIME_COMB family")
    for k in KILLS:
        print(f"   · {k['id']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
