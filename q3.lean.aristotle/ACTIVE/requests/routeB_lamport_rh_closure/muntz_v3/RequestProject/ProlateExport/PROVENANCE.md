# Prolate Q3 4.26 to Muntz v3 4.28 export provenance

- Source commit: `6e78e4e54fe972fc756cc1843a96d6ae8d94f9d5`
- Export date: `2026-08-02`
- Source file: `q3.lean.aristotle/Q3/Proofs/RouteB/ProlateLayer.lean`
  - Git blob: `71f523672481aa6449c93fd84a5e3ad7db4196f6`
  - SHA-256: `3c2099c97df6cd0fb45f7b367d24898d11c031ed297fe9031b25ee5b9dc0edf4`
  - Export rule: verbatim after this provenance record; imports unchanged.
- Source file: `q3.lean.aristotle/Q3/Proofs/RouteB/ProlateCombinationMuntzRegularity.lean`
  - Git blob: `1d61cf252c4ae4e5ef3b97d53af8701f63be4232`
  - SHA-256: `d3990c1be7288b49f6d63dec42bbfa12e7799a955d80bee24c3ca9dcea9624c0`
  - Export rule: verbatim except the first import is renamed from
    `Q3.Proofs.RouteB.ProlateLayer` to
    `RequestProject.ProlateExport.ProlateLayer`.
- Source commit: `298701cb0a98e82da29b24e89281239eb6c67b5a`
- Source file: `q3.lean.aristotle/Q3/Proofs/RouteB/ProlateModeRegularity.lean`
  - Git blob: `a203ce11b0c8dd21bd4b5c24d01f6293277ce1eb`
  - SHA-256: `d09f80b47386afcddec890de959060e00961c57e19ca9db73a8bdcf507a06177`
  - Export rule: verbatim except the first import is renamed from
    `Q3.Proofs.RouteB.ProlateLayer` to
    `RequestProject.ProlateExport.ProlateLayer`.

The namespace `Q3.RouteB.D0Pstar` is preserved.  The receiver must import these
exports and must not redeclare `ProlatePair` or `prolateCombination`.
