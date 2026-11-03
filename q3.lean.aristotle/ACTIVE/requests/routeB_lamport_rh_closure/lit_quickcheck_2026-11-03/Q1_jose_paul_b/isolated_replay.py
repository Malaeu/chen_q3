import sys, runpy
sys.path.insert(0, '/tmp/litdeps')
script=sys.argv[1]
sys.argv=sys.argv[1:]
runpy.run_path(script,run_name='__main__')
