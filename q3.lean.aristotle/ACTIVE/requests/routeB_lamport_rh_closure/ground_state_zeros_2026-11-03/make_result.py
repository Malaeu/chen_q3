"""Owner-facing report from the completed finite scalar integration."""
from pathlib import Path
import json,csv
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=100
def fmt(v):return mp.nstr(mp.mpf(v),8) if v not in (None,'') else ''
def main():
    nearest=list(csv.DictReader((P/'NEAREST_SOURCE.csv').open()));near={(q['world'],int(q['m'])):q for q in nearest if q['is_global']=='True'}
    o=json.loads((P/'OVERVIEW.json').read_text());assert o['status']=='COMPLETE_FINITE_DIAGNOSTIC'
    s={(r['world'],int(r['m'])):r for r in csv.DictReader((P/'spectra/spectra.csv').open())}
    rr=list(csv.DictReader((P/'roots/summary.csv').open()));r={(x['world'],int(x['m']),x['parity']):x for x in rr if x['cutoff']=='fixed_c1_4'}
    lines=['# Ground simplicity, parity and Fourier zeros: literal m16..300','',
      '**DIAGNOSTIC_NEVER_A_PROOF. Separate lane from D0; no route-state or RH export.**','',
      'All 285 integer windows, N=m and L=log m, have been computed in zeta, DH and the planted world: 855 world/window cells. Both parity blocks are compared. Source pin: 50777d478c72298ff65c7ffaa2b3783aec183dd6. Later concurrent branch history is preserved.','',
      'Primary cutoff is T=(1+(1+log L)/(4L))*2pi m/L, with fixed c=1/4. Controls at Omega=2pi m/L and 0.8Omega are retained in roots/summary.csv. The even restricted ground and actual full ground are distinct columns; all numerical accuracy/source caveats are in NORMALIZATION.md and the worker methods.','',
      '## Simplicity and parity','',
      '|world|cells|global parity counts|first global odd m|first negative even m|',
      '|---|---:|---|---:|---:|']
    for w in ['zeta','dh','plant']:
        q=o['worlds'][w];lines.append(f'|{w}|{q["spectral_cells"]}|{q["global_parities"]}|{q["first_global_odd"]}|{q["first_negative_even"]}|')
    zeta_parity_sentence=('The finite zeta grounds are numerically isolated and even.' if not o['worlds']['zeta']['global_parities'].get('odd',0) else 'The finite zeta parity test fails; see the first odd global winner in the table.')
    lines+=['',zeta_parity_sentence+' DH first has a negative even ground at m=51, before its first odd global winner at m=54; the plant first has an odd global winner at m=18. Thus a simple even finite ground can already be negative in the DH control. A sign at m=16..300 is not a cofinal theorem.','',
      '|zeta m|lambda_even0|even gap|full gap|',
      '|---:|---:|---:|---:|']
    for m in [16,24,40,80,160,300]:
        q=s['zeta',m];lines.append(f'|{m}|{fmt(q["lambda_even0"])}|{fmt(q["even_gap"])}|{fmt(q["global_gap"])}|')
    lines+=['','The full gap merges the two ordered low pairs; for the zeta m=300 pilot the next state is odd. Absolute gaps are extremely small even though their separation from the arithmetic error floor and their ratios to the ground are large. For macroscopic control minima, the sign or vector of a near-zero second level may remain unresolved while its gap from the ground is resolved; signed-second-level flags are preserved.','',
      '![Ground and gap scales, and parity](SPECTRAL_GAPS.png)','',
      '## Counts and displacement of zeros','',
      'Numerator roots are found without source-zero seeds. Every transform also has exact external harmonic zeros, which must not be counted as recovered zeta zeros. Assignment count and close-match count are different. The table gives the complete physical-strip count, its numerator/forced split, and maximum displacement within the chosen minimum-total-Euclidean-distance one-to-one assignment. With unequal control censuses, tied sums can give different maxima; these maxima are not optimal bottleneck distances.','',
      '|zeta m|source zeros|numerator roots below T|forced external|full transform|close source matches <1e-6|max numerator displacement|',
      '|---:|---:|---:|---:|---:|---:|---:|']
    for m in [16,24,40,80,160,300]:
        q=r['zeta',m,'even'];lines.append('|'+ '|'.join([str(m),q['source_count'],q['polynomial_strip_count'],q['forced_external_count'],q['fourier_strip_count'],q['matched_under_1e_6'],fmt(q['polynomial_only_max_abs_deviation'])])+'|')
    allz=sorted([q for q in r.values() if q['world']=='zeta' and q['parity']=='even'],key=lambda q:int(q['m']))
    badz=[int(q['m']) for q in allz if int(q['matched_under_1e_6'])<int(q['source_count'])]
    worst=max(allz,key=lambda q:mp.mpf(q['polynomial_only_max_abs_deviation']))
    lines+=['', 'At the 1e-6 close-match threshold, the incomplete zeta windows are '+str(badz)+'. The largest early displacement is '+fmt(worst['polynomial_only_max_abs_deviation'])+' at m='+worst['m']+'. Every tested m from '+str(max(badz)+1 if badz else 16)+' through 300 has all source points matched within 1e-6. Count equality alone does not imply exact or tolerance-close locations.']
    zeta_count_sentence=('For zeta the observed finite count identity is `full FT count = source count + forced external count`; numerator/source counts agree on this grid.' if not o['worlds']['zeta']['even_source_numerator_count_mismatches'] and not o['worlds']['zeta']['even_full_count_minus_source_minus_forced'] else 'The zeta count equality has exceptions listed explicitly in OVERVIEW.json.')
    lines+=['',zeta_count_sentence+' This is a reported finite observation, not an exact identity between the source and ground transforms. All individual counts, near misses, one-to-one pairings, and both-side unmatched-under-tolerance counts are retained.','',
      '|m300 actual global ground|parity|source points|non-real source points|FT strip roots|non-real FT strip roots|unrecovered source <1e-6|max in chosen min-sum pairing|',
      '|---|---|---:|---:|---:|---:|---:|---:|']
    for w in ['zeta','dh','plant']:
        par=s[w,300]['global_ground_parity'];q=r[w,300,par];lines.append('|'+ '|'.join([w,par,q['source_count'],q['source_nonreal_count'],q['fourier_strip_count'],q['fourier_nonreal_count'],q['source_unrecovered_at_1e_6'],fmt(q['polynomial_only_max_abs_deviation'])])+'|')
    lines+=['', '|m|DH min-sum max|DH min-sum max/T|plant min-sum max|plant min-sum max/T|','|---:|---:|---:|---:|---:|']
    for m in [16,40,80,160,300]:
        vals=[str(m)]
        for w in ['dh','plant']:
            q=r[w,m,s[w,m]['global_ground_parity']];v=mp.mpf(q['polynomial_only_max_abs_deviation']);vals.extend([fmt(v),fmt(v/mp.mpf(q['T']))])
        lines.append('|'+ '|'.join(vals)+'|')
    lines+=['', 'CONTROL_SCALING.csv retains both controls at every integer m, including the close-match fraction. These are finite displacement curves; no asymptotic law is inferred for the controls.']
    lines+=['', 'Tie-independent control: for every source point, take its nearest candidate below T. This comparison permits shared candidates and is not an injective matching. Numerator-only and full-transform errors differ because the latter includes the forced harmonic lattice. NEAREST_SOURCE.csv retains every physical case at 200 dps.', '', '|m|DH nearest numerator max|DH nearest full-transform max|plant nearest numerator max|plant nearest full-transform max|', '|---:|---:|---:|---:|---:|']
    for m in [16,40,80,160,300]:
        vals=[str(m)]
        for w in ['dh','plant']:
            q=near[w,m];vals.extend([fmt(q['numerator_max_nearest_distance']),fmt(q['full_transform_max_nearest_distance'])])
        lines.append('|'+ '|'.join(vals)+'|')
    lines+=['', 'At m=300 the nearest-candidate source-close counts at 1e-6 are 183/183 for zeta, 0/276 for DH and 0/185 for the plant, including the full harmonic lattice. The zero close counts in these controls therefore do not result from a tied assignment.']
    lines+=['', '|world|first even pure-imaginary root m|first global pure-imaginary root m|global cells with non-real positive-height strip roots|', '|---|---:|---:|---:|']
    for w in ['zeta','dh','plant']:
        q=o['worlds'][w];lines.append(f'|{w}|{q["first_even_pure_imaginary"]}|{q["first_global_pure_imaginary"]}|{len(q["global_off_real_strip_cells"])}|')
    if not any(o['worlds'][w]['global_off_axis_anywhere_cells'] or o['worlds'][w]['even_off_axis_anywhere_cells'] for w in ['zeta','dh','plant']):
        lines+=['','No off-axis numerator roots were found anywhere in these complete finite polynomials, for either the restricted even or actual global grounds. The non-real exceptions in the controls are pure-imaginary axis roots. Consequently the physical-strip restriction does not conceal extra positive-height off-axis roots below T.']
    lines+=['', 'The first non-real DH source pair enters the primary cutoff at m='+str(o['worlds']['dh']['first_source_nonreal_below_T'])+'. This differs from the first negative even minimum and the first odd global winner. Source densities differ between worlds; the raw count alone is not a density-matched discriminator.']
    axis_mismatches={w:o['worlds'][w]['axis_parity_mismatch_cells'] for w in ['zeta','dh','plant']}
    lines+=['', 'Exploratory axis/parity check, seeded by the first DH/plant transitions: mismatch cells between even pure-imaginary-root presence and an odd global winner are '+str(axis_mismatches)+'. See CARD_AXIS_PARITY.md; this is a finite geometric check shared with controls, not an arithmetic conclusion.']
    lines+=['','The DH reference is its numerical census to 900; the m300 primary cutoff is only 370.179625... and contains 8 off-line quartets (16 positive-height non-real points). The plant contains its fixed two non-real positive-height points. These can be missing from the ground transform even when its own strip zeros are all real. Non-real ground-transform zeros therefore need not appear as copies of non-real source zeros.','',
      'Pure-imaginary numerator roots have height zero and are listed separately from positive-height strip roots. They occur in the controls, for example in their m300 even restricted grounds; they are not the missing source quartets. Off-axis/far-strip and pure-imaginary counts remain in the CSV instead of being silently called real.','',
      '![Global-ground zero fidelity and finite scaling](ZERO_FIDELITY.png)','',
      '## How the deviation scales','',
      'The preregistered candidate was -log10(d)=a*m/(log m)^2+b. Five fixed regressors were trained on m=40..160 and evaluated on held-out m=161..300, using actual root precision repeats and excluding arithmetic/reference floors. Threshold entry produces oscillations; pointwise monotonicity was not assumed.','',
      '|regressor|training RMSE, decades|held-out RMSE, decades|held-out maximum error, decades|',
      '|---|---:|---:|---:|']
    for q in o['scaling']:lines.append(f'|{q["model"]}|{q["training_RMSE_decades"]:.5g}|{q["held_out_RMSE_decades"]:.5g}|{q["held_out_max_abs_error_decades"]:.5g}|')
    if o.get('exploratory_edge_scaling'):
        lines+=['','Additional exploratory check, registered after an early validation peek: add the last included source zero depth, phi=(T-gamma_last)/(2pi/L). The untouched test tail is m=261..299, excluding pilot m=300. This is not a second independent preregistered result.','', '|modifier|baseline tail RMSE|with phase tail RMSE|','|---|---:|---:|']
        for q in o['exploratory_edge_scaling']:lines.append(f'|{q["model"]}|{q["baseline_tail_RMSE_decades"]:.5g}|{q["edge_tail_RMSE_decades"]:.5g}|')
    best=o['scaling'][0];lines+=['',f'Best of these finite held-out comparisons: `{best["model"]}`. Exact coefficients and all residuals are in SCALING.csv. This does not identify an asymptotic law or supply a uniform error bound.','',
      '## Precision and independent controls','',
      'The actual m300 even ground is about 2.45e-505, so an arbitrary double-precision near-null vector is inadequate. Analytic source assembly was independently checked against both parity quadrature formulas and the pinned MPFR source. An additional m=300, 2400-bit, 8-panel GL768 quadrature regression checks all worlds and both parity blocks: actual 2184-bit point entries differ by at most 2.631e-657; the higher-precision analytic comparison differs by at most 2.462e-700. These are numerical source regressions, not outward-rounded operator bounds.','',
      'Native ordered HIGH low pairs, residuals, source precision repeats and distinct LOW-vector root replays are retained. Some later LOW controls may use a reviewed shifted refinement with explicit source-perturbation gates, without replacing HIGH ordering; unavailable LOW second pairs are not fabricated. Some zeta root censuses use reviewed continuation plus complete sign-bracket/degree checks, with a full Flint fallback. The source and root methods, per-cell hashes, fallback records and review bindings remain explicit.','',
      'Selected full LOW/HIGH polynomial censuses through m300 agree. The zeta m300 primary roots move by at most 5.061e-147 between independently computed vectors, far below the observed 3.463e-29 source displacement. The separate sign-bracket degree checks certify the rounded LOW polynomial roots only; they do not certify the unknown exact eigenvector or RH. Generic L2 Fourier-error bounds are much looser and remain separately labelled.','',
      'The constant carrier control has zero source matches at 1e-6 in all 54 selected world/window/cutoff tests. Thus the close zeta recovery is not explained by the structural lattice alone. The far numerator-root tail and its universal finite Vieta/boundary-curvature check are documented in CARD_FAR_NUMERATOR_ROOTS.md and BOUNDARY_ROOTS.csv.','',
      'All scalar data: GAPS.csv and ZERO_SUMMARY.csv; all odd-winner m ranges: ODD_RANGES.csv; full precision/raw vectors and roots: the lossless publication archive. Restore before numerical replay, then follow the spectra/ and roots/ methods. The archive manifest and SHA256 inventories verify bytes; independent final review is under review/. No D0 state, cofinal conclusion, or RH claim is changed.']
    (P/'RESULT.md').write_text('\n'.join(lines)+'\n')
if __name__=='__main__':main()
