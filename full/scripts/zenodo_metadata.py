#!/usr/bin/env python3
"""Zenodo metadata editor for the Q3 records — status note as first paragraph of the description.

Usage:
  ZTOKEN=$(op read "op://Personal/ZENODO_API/credential") python3 -I full/scripts/zenodo_metadata.py diff  [ids...]
  ZTOKEN=$(op read "op://Personal/ZENODO_API/credential") python3 -I full/scripts/zenodo_metadata.py apply [ids...]

diff  — compare the note in full/ZENODO_STATUS_NOTE_2026-10-22.md with what is on Zenodo; nothing is sent.
apply — for every record whose note differs: actions/edit → PUT metadata → actions/publish, then verify via public API.
Default ids: 17527099 17541763 17956251. Token is never printed.
"""
import difflib, html, json, os, re, sys, time, urllib.request, urllib.error

NOTE_FILE = os.path.join(os.path.dirname(__file__), "..", "ZENODO_STATUS_NOTE_2026-10-22.md")
DEFAULT_IDS = ["17527099", "17541763", "17956251"]
API = "https://zenodo.org/api"
SEP = "<p>---</p>"


def token():
    t = os.environ.get("ZTOKEN")
    if not t:
        sys.exit('ZTOKEN missing. Run with: ZTOKEN=$(op read "op://Personal/ZENODO_API/credential") ...')
    return t


def call(method, path, body=None):
    data = json.dumps(body).encode() if body is not None else None
    req = urllib.request.Request(API + path, data=data, method=method,
                                 headers={"Authorization": f"Bearer {token()}", "Accept": "application/json",
                                          "Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req) as r:
            raw = r.read()
            return r.status, (json.loads(raw) if raw else {})
    except urllib.error.HTTPError as e:
        return e.code, json.loads(e.read() or b"{}")


def note_paras():
    md = open(NOTE_FILE, encoding="utf-8").read().split("\n", 2)[2].strip()
    return [p.strip() for p in md.split("\n\n") if p.strip()]


def esc(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def note_html(paras):
    return "".join(f"<p>{esc(p)}</p>" for p in paras) + SEP


def split_record(desc_html):
    """Return (note paragraphs found on zenodo, remainder html after separator)."""
    if SEP in desc_html:
        head, rest = desc_html.split(SEP, 1)
    else:
        head, rest = "", desc_html
    text = html.unescape(re.sub(r"<[^>]+>", "\n", head))
    return [p.strip() for p in text.split("\n") if p.strip()], rest


def diff_one(rid, want):
    st, d = call("GET", f"/deposit/depositions/{rid}")
    if st != 200:
        print(f"[{rid}] GET failed HTTP {st}: {d.get('message')}")
        return None
    m = d["metadata"]
    have, rest = split_record(m["description"])
    diff = list(difflib.unified_diff(have, want, "zenodo", "file", lineterm="", n=0))
    print(f"[{rid}] {d['state']} | {m['title'][:55]!r} | note paras on zenodo {len(have)} / file {len(want)}")
    if diff:
        for l in diff:
            print("    " + l[:170])
    else:
        print("    DIFF: none")
    return m, rest, bool(diff)


def apply_one(rid, want, m, rest):
    new_desc = note_html(want) + rest
    st, d = call("POST", f"/deposit/depositions/{rid}/actions/edit")
    if st not in (201, 200):
        print(f"[{rid}] actions/edit HTTP {st}: {d.get('message')} {d.get('errors','')}")
        return False
    m2 = dict(m); m2["description"] = new_desc
    m2.pop("doi", None); m2.pop("prereserve_doi", None)   # read-only on edit
    st, d = call("PUT", f"/deposit/depositions/{rid}", {"metadata": m2})
    if st != 200:
        print(f"[{rid}] PUT HTTP {st}: {d.get('message')} {d.get('errors','')}")
        return False
    st, d = call("POST", f"/deposit/depositions/{rid}/actions/publish")
    if st not in (202, 200):
        print(f"[{rid}] publish HTTP {st}: {d.get('message')} {d.get('errors','')}")
        return False
    time.sleep(6)
    req = urllib.request.Request(f"{API}/records/{rid}?_={int(time.time())}", headers={"Accept": "application/json"})
    j = json.load(urllib.request.urlopen(req))
    ok = j["metadata"]["description"].count("STATUS NOTE") == 1 and want[0] in html.unescape(re.sub(r"<[^>]+>", " ", j["metadata"]["description"]))
    print(f"[{rid}] published; public API updated={j['updated'][:19]} verify={'OK' if ok else 'MISMATCH'}")
    return ok


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "diff"
    ids = sys.argv[2:] or DEFAULT_IDS
    want = note_paras()
    for i, rid in enumerate(ids, 1):
        print(f"[{i}/{len(ids)}] {rid}")
        res = diff_one(rid, want)
        if res is None:
            continue
        m, rest, changed = res
        if mode == "apply":
            if not changed:
                print("    nothing to apply")
            else:
                apply_one(rid, want, m, rest)
        elif mode != "diff":
            sys.exit("mode must be diff or apply")


if __name__ == "__main__":
    main()
