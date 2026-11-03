"""Assemble the owner-facing report from frozen scalar tables."""
from pathlib import Path
from collections import Counter
import csv,json
P=Path(__file__).resolve().parent
def short(v):
    if v in ('',None):return 'UNRESOLVED'
    try:return f'{float(v):.9g}'
    except (ValueError,TypeError):return str(v)
def main():
    c=json.loads((P/'C_conditioning/summary.json').read_text())
    b=list(csv.DictReader((P/'B_stitch/preferred.csv').open()))
    rows=list(csv.DictReader((P/'C_conditioning/conditioning.csv').open()))
    t=['# SOS audit, same-ambient stitch and conditioning', '',
       '**DIAGNOSTIC_NEVER_A_PROOF. Route B = CHALLENGER / NOT_RH.**','',
       'LIT_QUICKCHECK was completed before B/C (`81b657e`); the concurrent independent literature replay (`8bc588d`) is preserved. A is published separately in `4fe4292`, source and independent audit in canon and mirror. This packet contains B/C, all checkpoints, precision receipts and fixed-cutoff sensitivity tables.','',
       '## A: first step log3 SOS','',
       '`FIRST_STEP_LOG3_SOS_PAPER_AUDIT_PASS`. Both embedded generator runs produce payload SHA256 `8b7fb1900093eb47e663ae352e0b52a2ad18043bd5d654e0f1a71aacec5ddcc0`. Bareiss exact divisions/positive minors and independent rational LDL reconstruction pass. Independent operator-error bounds are below 1.784e-18 and 1.741e-18, respectively, hence below 2^-40. The audited source concludes W[f] >= 2^-30 ||f||^2 for support length at most log3. It does not certify arbitrary long histories or their short new extensions. See the separate source/audit and first_step_log3_sos_audit_2026-11-03 packet.','',
       '## B: one step-profile ambient','',
       'All 36 baseline cells use one declared physical step space per m, with both Schur constructions inside that space. Rank and inertia agree at 80/100 digits; the designated 120-digit replay also agrees. The section energy uses fresh-coordinate norm one. When the old block is indefinite, its completion is stationary and the unrestricted old-coordinate infimum is minus infinity.','',
       '|world|m|dim J|section energy|angle(f,J), degrees|full norm(AQ)|requested ratio|',
       '|---|---:|---:|---:|---:|---:|---:|']
    for r in b:
        if r['cutoff']=='cquarter':
            t.append('|'+ '|'.join([r['world'],r['m'],r['quiet_dimension'],short(r['sigma_section']),short(r['angle_f_J_degrees']),short(r['delta_full_AQ']),short(r['ratio'])])+'|')
    t += ['',
       'Key obstruction: zeta m24,c=1/4 has N_A(2)=dim J=31, yet the eliminated D-2I block has only 28 negatives and the quiet Schur has 3. The identity is 31=28+3. Its full quiet residual is 4.07822, so the quiet-below-2 hypothesis fails. Count equality alone is insufficient. The original even-CCM residual theorem is not transferred to this step carrier.','',
       'The proposed universal synchronization of raw Schur signs is not validated: the planted baseline has negative full/old inertia and a positive raw section Schur. The corrected full-inertia comparison passes, while the requested analytic stitch remains unproved. This exception is not counted as a successful optimizer or hidden by dropping old negative directions.','',
       'Resolved DH control: the additional m40 carrier has 949 physical bins, used by both coordinate systems. The old block is numerically positive (minimum 8.72047e-6); the full source minimum is -0.00151499925 and the section Schur minimum is -0.06106305735. Primary/secondary quiet Schur minima at threshold zero are -0.078464955 and -0.008242089. Both coordinates therefore detect the negative line in the same ambient. Under kappa=1 it resides in the eliminated quiet block instead. This is numerical, not an outward-rounded sign certificate.','',
       '## C: literal even CCM, every integer m16..120','',
       f'Coverage: **{c["cells"]}/315 world/m cells**, {c["base_rows"]} base-cutoff rows and {c["all_rows"]} total base/sensitivity rows. No count or residual is copied from the B step carrier. All m are outside the inherited theorem\'s L>=16 asymptotic regime.','',
       '|world|cutoff|cells|J=0|sigma resolved|lambda_r statuses|',
       '|---|---|---:|---:|---:|---|']
    for s in c['summary']:
        t.append(f'|{s["world"]}|{s["cut"]}|{s["cells"]}|{s["J_zero"]}|{s["sigma_resolved"]}|{s["lambda_r_status_counts"]}|')
    t += ['', '|zeta m|cut|dim J|delta=norm(AQ)|N_A(2)-dim J|raw sigma_min|lambda_r|',
          '|---:|---|---:|---:|---:|---:|---:|']
    for r in rows:
        if r['world']=='zeta' and int(r['m']) in [24,65,78,120] and r['cut'] in ['c_quarter','c_half','kappa_one']:
            t.append('|'+ '|'.join([r['m'],r['cut'],r['r'],(short(r['delta'])+' [floor]' if float(r['delta'])<=float(r['delta_numeric_radius']) else short(r['delta'])),r['count_minus_r'],short(r.get('sigma_min')),short(r.get('lambda_r_preferred'))])+'|')
    t += ['',
       'The kappa=1 m24 calibration repeats the known failure: delta=2.956529432>2 and N_A(2)-dim J=-1; the eliminated negative index is 16 rather than 17. Primary/secondary fixed c can make delta very small without saturating the count. At m120 the primary zeta defect is 11 despite delta about 5.9e-6; the secondary defect is 22. These finite observations do not contradict an asymptotic theorem.','',
       'The 111.0295355/111.8746592 pair enters together at m65 for c=1/4, together at m55 for c=1/2, and separately at m77/m78 for kappa=1. Every flagged cutoff is also evaluated at T plus/minus half the local mean spacing, with the same source matrix. The per-zero table flags normalized included gaps below 0.3 and separately retains the last-zero lookahead.','',
       'Conditioning is not a signed-source discriminator: at m120 primary raw sigma is 9.9393e-15 for zeta and 9.8497e-15 for the plant. In every matched cutoff/sensitivity row, the plant adds two real conditions, decreases dim J by two, decreases N_A(2) by one, and therefore increases N_A(2)-dim J by exactly one. The weak raw capacity barely changes while the full relative index sees the quartet.','',
       f'Matched planted rows: {c.get("paired_planted_rows")}; observed (defect increment, count increment, dimension increment): {c.get("paired_planted_difference_counts")}. This is a finite diagnostic, not a proved index law.','',
       'The minimum included zero gap is also insufficient: the same gap can accompany raw singular values differing by many orders as the cutoff changes. At zeta m120 primary/secondary sigmas differ by about 1.38e17. Full weak-pair coordinates/masses, all gaps, interpolation rank and source normalization remain necessary. See CARD_CONDITIONING and CARD_PLANTED_RELATIVE_INDEX.','',
       'A delta marked [floor] lies below the saved floating diagnostic radius; it is not a resolved source residual at that displayed size. Every full CSV row retains delta_numeric_radius. In particular zeta m120 secondary delta about 5.53e-15 is at the floating floor, whereas its scalar lambda_r and raw sigma have separate MP replays.','',
       f'Full guarded Schur status counts: {c["Schur_identity_status_counts"]}. All eliminated indices are retained; unresolved sigma/eigenvalue cases retain explicit status and blank ratios. High-precision scalar eigenvalue replays do not turn float projectors or Schur blocks into interval calculations.','',
       '## Reproduction and analytic handoff','',
       'Read NORMALIZATION.md, B_stitch/RESULT.md and C_conditioning/METHOD.md first. CONDITIONING_DIGEST.csv gives all945 base rows directly with eight-significant-digit display rounding, explicit floating delta floors and diagnostic radii; this rounding is not an accuracy claim. Full scalar CSVs and raw matrix/checkpoint data are retained losslessly in the publication archive when large. Run `python3 unpack_data.py` to restore them, then the scripts in their own directories. PUBLICATION_ARCHIVE.json records every member and part hash; SHA256SUMS records the directly published packet. REPLAY_DEPENDENCIES.json pins existing repository dependencies. No external service credentials are needed for numerical replay.','',
       'The useful handoff is a complete common-threshold inertia ledger with estimates on D-CI, B and G, rather than a raw Schur sign or raw capacity. lambda_r of the sorted full spectrum is not automatically a lower bound on the arbitrary interpolation complement. No cofinal bound, RH proof, source-sign estimate or route-state change is claimed.']
    (P/'RESULT.md').write_text('\n'.join(t)+'\n')
if __name__=='__main__':main()
