#!/usr/bin/env python3
"""Additional deterministic census bound from saved address rows; no new scan."""
import csv,json
from pathlib import Path
P=Path(__file__).resolve().parent
rows=list(csv.DictReader((P/'events.csv').open()));inside=[r for r in rows if r['within_census']=='True'];hits=sum(float(r['off_distance_steps'])<=1 for r in inside);outside=len(rows)-len(inside)
ambiguous_inside=sum(r['off_upper_census_ambiguous']=='True' for r in inside)
assert ambiguous_inside==0
out=dict(status='POSTHOC_DETERMINISTIC_CENSOR_BOUND',events=len(rows),within_census=len(inside),known_within_one_hits=hits,above_census=outside,ambiguous_within_census=ambiguous_inside,optimistic_total_hit_fraction=(hits+outside)/len(rows),meaning='Conditional on supplied census below900: even every above-census event becoming a one-step hit cannot reach90%. This is arithmetic from saved rows, not a new fitted prediction or a proof of census completeness.')
(P/'CENSOR_BOUND.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
