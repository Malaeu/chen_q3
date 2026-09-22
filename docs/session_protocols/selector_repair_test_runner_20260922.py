import importlib.util,sys,unittest
from pathlib import Path
sys.path.insert(0,str(Path.cwd()))
import orchestrator
base=Path('/tmp/q3-selector-candidate')
for name,path in [('orchestrator.team_records','team_records.py'),('q3_candidate_tests','test_workflow_runtime.py')]:
 source = Path('orchestrator/team_records.py') if '--baseline' in sys.argv and name == 'orchestrator.team_records' else base/path
 spec=importlib.util.spec_from_file_location(name,source)
 module=importlib.util.module_from_spec(spec);sys.modules[name]=module
 if name=='orchestrator.team_records': orchestrator.team_records=module
 spec.loader.exec_module(module)
 if name == "q3_candidate_tests": module.__file__ = str(Path.cwd()/"orchestrator/tests/test_workflow_runtime.py")
suite=(unittest.TestSuite([unittest.defaultTestLoader.loadTestsFromTestCase(module.TeamRecordsTests),unittest.defaultTestLoader.loadTestsFromTestCase(module.TeamRuntimeTests)]) if '--runtime' in sys.argv else unittest.defaultTestLoader.loadTestsFromModule(module) if '--all' in sys.argv else unittest.defaultTestLoader.loadTestsFromTestCase(module.TeamRecordsTests))
if '--migration-only' in sys.argv:
 suite=unittest.defaultTestLoader.loadTestsFromName('TeamRuntimeTests.test_pinned_engine_recovers_control_10_to_11_migration',module)
result=unittest.TextTestRunner(verbosity=2).run(suite)
sys.exit(not result.wasSuccessful())
