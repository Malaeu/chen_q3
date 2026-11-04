"""Stream the complete native strict record-minimum CSV from lossless shards."""
from pathlib import Path
import json,gzip,sys
P=Path(__file__).resolve().parents[1]
first=True
for item in json.loads((P/'RECORDS_INDEX.json').read_text())['parts']:
 with gzip.open(P/item['file'],'rb')as f:
  header=next(f)
  if first:sys.stdout.buffer.write(header);first=False
  for line in f:sys.stdout.buffer.write(line)
