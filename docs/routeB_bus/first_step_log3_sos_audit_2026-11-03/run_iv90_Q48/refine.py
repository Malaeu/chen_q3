import importlib.util
from pathlib import Path
p=Path(__file__).with_name('certify.py')
spec=importlib.util.spec_from_file_location('audited_sos',p)
module=importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
module.iv.dps=90
module.Q=48
module.main()
