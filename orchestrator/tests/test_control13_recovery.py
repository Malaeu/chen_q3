"""Source-bound candidate tests, NOT approval of a live recovery.

Set Q3_RECOVERY_BASELINE_ROOT to the extracted baseline/ directory. All
repositories, installation secrets, owners' signoffs and native records created
here are TEST FIXTURES. The named real packet is tested separately for its
missing observation origin; it is not silently made into a positive fixture.
"""
from __future__ import annotations
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import yaml
from orchestrator import workflow_runtime as w, startup_runtime as sr, team_records as tr, control13_recovery as r

SOURCE = Path(w.__file__).resolve().parents[1]
BASE = Path(os.environ.get('Q3_RECOVERY_BASELINE_ROOT', str(SOURCE.parent/'baseline')))
PACKET = Path(os.environ.get('Q3_RECOVERY_PACKET_ROOT', str(SOURCE.parent)))

def git(repo: Path, *args: str) -> str:
    return subprocess.run(['git', *args],cwd=repo,check=True,capture_output=True,text=True).stdout.strip()

def write(path: Path, raw: bytes, mode=0o644):
    path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw);path.chmod(mode)

def doc(data, body):
    return ('---\n'+yaml.safe_dump(data,sort_keys=False)+'---\n'+body).encode()

class Fixture:
    def __init__(self, *, history_prefix=False):
        self.temp=tempfile.TemporaryDirectory(prefix='q3-rec13-test-');self.root=Path(self.temp.name)
        self.repo=self.root/'canonical';self.repo.mkdir()
        git(self.repo,'init','-q','-b','rh_clean');git(self.repo,'config','user.name','Fixture');git(self.repo,'config','user.email','fixture@example.invalid')
        for p,h in r.BASE_HASHES.items():
            if h!='ABSENT':
                b=(BASE/p).read_bytes();assert w._resume_digest(b)==h;write(self.repo/p,b)
        source=b'fixture-only mathematical source\n';write(self.repo/'docs/source.txt',source)
        if history_prefix:
            git(self.repo,'add','--','docs','orchestrator');git(self.repo,'commit','-qm','TEST original report source R')
            self.report_base=git(self.repo,'rev-parse','HEAD')
        prior=yaml.safe_load((BASE/'docs/Codex/RESUME.md').read_text().split('---\n',2)[1])
        self.data=copy.deepcopy(prior)
        secret='17'*32
        self.identity=hashlib.sha256(b'q3-team-installation-v1\0'+bytes.fromhex(secret)).hexdigest()
        self.data['ownership']['installation_ref']=self.identity
        self.data['revision']=1;self.data['previous_sha256']='ABSENT'
        self.data['source_manifest']={'docs/source.txt':w._resume_digest(source)}
        for stage in self.data['stages'].values():
            stage['source_sha256']=r.digest(self.data['source_manifest'])
        self.data['operation']['inputs']={'docs/source.txt':w._resume_digest(source)}
        observations=json.loads((PACKET/'observations.json').read_text())
        self.assignment=copy.deepcopy(observations['assignment']['assignment'])
        self.assignment['owner_installation_ref']=self.identity
        if history_prefix:
            self.assignment['base_commit']=self.report_base
            self.assignment['input_hashes']=[{'path':p,'sha256':w._resume_digest(w._team_git(self.repo,'show',self.report_base+':'+p))}
                for p in ('orchestrator/team_records.py',r.SELECTOR_TEST_PATH)]
        self.data['operation']['subject']['sha256']=tr._assignment_binding_sha(self.assignment)
        self.body='\n# TEST ONLY\n\n'+''.join('## '+name+'\nFixture; no real claim.\n\n' for name in w.RESUME_SECTIONS)
        self.origin=doc(self.data,self.body)
        self.data['revision']=2;self.data['previous_sha256']=w._resume_digest(self.origin)
        self.raw=doc(self.data,self.body+'Notes changed only.\n')
        self.history=w.RESUME_HISTORY_HEADER+w._resume_history_record('goal',0,b'fixture\n')[1]
        self.history+=w._resume_history_record('intent',1,self.origin)[1]+w._resume_history_record('resume',1,self.origin)[1]
        self.history+=w._resume_history_record('intent',2,self.raw)[1]
        write(self.repo/w.RESUME_PATH,self.raw);write(self.repo/w.RESUME_HISTORY_PATH,self.history)
        assignments,_=tr.prepare_assignment(b'# fixture assignments\n',self.assignment,w._resume_digest(b'# fixture assignments\n'))
        write(self.repo/w.TEAM_ASSIGNMENTS,assignments);write(self.repo/w.TEAM_ISSUES,b'# fixture issues\n')
        git(self.repo,'add','--','docs','orchestrator');git(self.repo,'commit','-qm','fixture base')
        if not history_prefix:self.report_base=git(self.repo,'rev-parse','HEAD')
        self.remote_base=git(self.repo,'rev-parse','HEAD')
        if history_prefix:
            write(self.repo/'already-remote.txt',b'TEST already remote, never a delivery change\n')
            git(self.repo,'add','--','already-remote.txt');git(self.repo,'commit','-qm','TEST O after R')
            self.remote_base=git(self.repo,'rev-parse','HEAD')
            self.history+=w._resume_history_record('resume',2,self.raw)[1]
            self.data['revision']=3;self.data['previous_sha256']=w._resume_digest(self.raw)
            self.raw=doc(self.data,self.body+'TEST committed historical continuation.\n')
            self.history+=w._resume_history_record('intent',3,self.raw)[1]
            write(self.repo/w.RESUME_PATH,self.raw);write(self.repo/w.RESUME_HISTORY_PATH,self.history)
            for path in r.HISTORY_PATHS:
                if path not in {str(w.RESUME_PATH),str(w.RESUME_HISTORY_PATH)}:
                    write(self.repo/path,('TEST immutable historical evidence: '+path+'\n').encode())
            git(self.repo,'add','--',*r.HISTORY_PATHS)
            git(self.repo,'commit','-qm','TEST H carries exactly 23 historical paths')
        else:
            git(self.repo,'commit','--allow-empty','-qm','fixture later execution head')
        self.head=git(self.repo,'rev-parse','HEAD')
        write(self.repo/'foreign.txt',b'foreign bytes preserved\n')
        common=self.repo/'.git'
        write(common/'q3-three-body.writer.lock',b'',0o600)
        write(common/w.TEAM_INSTALLATION,w._team_json({'schema':w.TEAM_INSTALLATION,
            'installation_secret':secret,'installation_ref':self.identity}),0o600)
        self.obs={"schema":"q3_team_remote_observation.v1","operation_id":r.CANCEL_ID,"state":"OBSERVED",
            "installation_ref":self.identity,"actor":self.data['owner_thread_id'],"epoch":2,
            "checkpoint_sha256":w._resume_digest(self.origin),"local_head":self.head,
            "remote_commit":"8"*40,"remote_resume_sha256":"7"*64,
            "remote_ownership":copy.deepcopy(self.data['ownership']),"remote_thread":self.data['owner_thread_id'],"evidence":{}}
        self.local={'schema':w.TEAM_LOCAL,'installation_ref':self.identity,'operations':{r.CANCEL_ID:self.obs},'watch':None,'epoch_floor':2}
        self.put_local(self.local)
        self.engine=self.root/'engine'
        git(self.root,'clone','-q',str(self.repo),str(self.engine))
        git(self.engine,'config','user.name','Fixture');git(self.engine,'config','user.email','fixture@example.invalid')
        for p in r.BASE_HASHES:
            write(self.engine/p,(SOURCE/p).read_bytes())
        git(self.engine,'add','--',*r.BASE_HASHES);git(self.engine,'commit','-qm','fixture reviewed candidate NOT real approval')
        self.commit=git(self.engine,'rev-parse','HEAD')
        self.patches=[patch.object(r,'BASE_HEAD',self.head),patch.object(r,'HISTORICAL_REMOTE',self.remote_base),patch.object(w,'REPO',self.engine),
            patch.dict(os.environ,{'CODEX_THREAD_ID':self.data['owner_thread_id'],'Q3_OWNER_EPOCH':'2'})]
        for mod,rel in ((w,'workflow_runtime.py'),(sr,'startup_runtime.py'),(tr,'team_records.py'),(r,'control13_recovery.py')):
            self.patches.append(patch.object(mod,'__file__',str(self.engine/'orchestrator'/rel)))
        for p in self.patches:p.start()
        self.manifest=r.prepare_manifest(self.repo)
        self.mp=self.root/'manifest.json';write(self.mp,w._team_json(self.manifest))
        self.signoff={'schema':r.SIGNOFF_SCHEMA,'approval_class':'OWNER_SIGNOFF','reviewer_id':'HUMAN_OWNER',
            'author_id':'Proshka','owner':r.owner(self.data),'manifest_sha256':r.digest(self.manifest),
            'instruction':'TEST FIXTURE ONLY: approve exact test payload, not any real activation.',
            'independent_acceptance':False,'mathematical_acceptance':False,'publication_authorized':False}
        self.ap=self.root/'TEST_ONLY_signoff.json';write(self.ap,w._team_json(self.signoff))
    def close(self):
        for p in reversed(self.patches):p.stop()
        self.temp.cleanup()
    def put_local(self,value):write(self.repo/'.git'/w.TEAM_LOCAL,w._team_json(value),0o600)
    def current_local(self):return w._team_private_read(self.repo,w.TEAM_LOCAL)
    def execute(self,**kw):
        opts={'candidate':self.mp,'expected_sha256':r.digest(self.manifest),'owner_signoff':self.ap,
              'approved_signoff_sha256':r.digest(self.signoff),'execute':True}
        opts.update(kw);return r.recover_unreserved(self.repo,**opts)
    def recover(self,**kw):return r.recover_unreserved(self.repo,recover_operation=self.manifest['operation_id'],execute=True,**kw)

class RecoveryTests(unittest.TestCase):
    def setUp(self):
        self.f=Fixture();self.addCleanup(self.f.close)
    def untouched(self):
        self.assertEqual(self.f.current_local(),self.f.local)
        self.assertEqual((self.f.repo/w.RESUME_PATH).read_bytes(),self.f.raw)
        for p,h in r.BASE_HASHES.items():self.assertEqual(r._file(self.f.repo,p)['sha256'],h)
    def test_01_actual_old_assignment_is_not_a_reviewer(self):
        obs=json.loads((PACKET/'observations.json').read_text());a=obs['assignment']['assignment']
        self.assertEqual(a['role'],'implementation')
        self.assertEqual(tr._assignment_binding_sha(a),'eb10c67d33051d3d27443dd5a841c1b827e020baca48f1a7b6152bbd3090b6b6')
    def test_02_dry_run_has_no_writes_and_no_approval(self):
        out=r.recover_unreserved(self.f.repo,candidate=self.f.mp,expected_sha256=r.digest(self.f.manifest))
        self.assertEqual(out['status'],'DRY_RUN');self.assertFalse(out['owner_signoff_present']);self.untouched()
    def test_03_missing_owner_signoff_never_activates(self):
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'OWNER_SIGNOFF_REQUIRED'):
            self.f.execute(owner_signoff=None,approved_signoff_sha256=None)
        self.untouched()
    def test_04_author_cannot_be_own_reviewer(self):
        self.f.signoff['reviewer_id']='Proshka';write(self.f.ap,w._team_json(self.f.signoff))
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'OWNER_SIGNOFF_REQUIRED'):self.f.execute()
        self.untouched()
    def test_05_complete_candidate_keeps_math_assignment_index_foreign(self):
        before=r._index_hash(self.f.repo);foreign=r._foreign_hash(self.f.repo)
        a=(self.f.repo/w.TEAM_ASSIGNMENTS).read_bytes()
        out=self.f.execute();self.assertEqual(out['status'],'RECOVERED')
        local=self.f.current_local();self.assertEqual(local['operations'][r.CANCEL_ID]['state'],'NOT_EXECUTED')
        self.assertEqual(local['operations'][self.f.manifest['operation_id']]['integration']['state'],'COMPLETE')
        self.assertEqual((self.f.repo/w.RESUME_PATH).read_bytes(),self.f.raw)
        self.assertEqual((self.f.repo/w.TEAM_ASSIGNMENTS).read_bytes(),a)
        self.assertEqual(r._index_hash(self.f.repo),before);self.assertEqual(r._foreign_hash(self.f.repo),foreign)
        self.assertFalse(out['commit_push_performed']);self.assertFalse(out['independent_acceptance'])
        self.assertEqual(sr.validate_battle_v10_control(self.f.repo).version,13)
        w._team_writer_inventory(self.f.repo)
        git(self.f.repo,'cat-file','-e',self.f.commit+'^{commit}')
    def test_06_completed_replay_never_reapplies(self):
        self.f.execute();before=self.f.current_local()
        self.assertEqual(self.f.recover()['status'],'NOOP');self.assertEqual(before,self.f.current_local())
        write(self.f.repo/'orchestrator/team_records.py',b'foreign third state\n')
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'DESTINATION_THIRD_STATE'):self.f.recover()
        self.assertEqual((self.f.repo/'orchestrator/team_records.py').read_bytes(),b'foreign third state\n')
    def test_07_reserved_target_cannot_cancel(self):
        changed=copy.deepcopy(self.f.local);changed['operations'][r.CANCEL_ID]['state']='RESERVED';self.f.put_local(changed)
        with self.assertRaises(w.WorkflowRuntimeError):self.f.execute()
        self.assertEqual(self.f.current_local(),changed)
    def test_08_unknown_target_cannot_cancel(self):
        changed=copy.deepcopy(self.f.local);changed['operations'][r.CANCEL_ID]['state']='UNKNOWN';self.f.put_local(changed)
        with self.assertRaises(w.WorkflowRuntimeError):self.f.execute()
        self.assertEqual(self.f.current_local(),changed)
    def test_09_native_evidence_rejects_even_if_target_says_observed(self):
        changed=copy.deepcopy(self.f.local);changed['operations']['native']={'state':'CONFIRMED','observation':{'assignment_id':r.ASSIGNMENT_ID}}
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'NATIVE_OR_LAUNCH_BINDING'):
            r.prove_unreserved(self.f.repo,self.f.raw,self.f.data,changed,self.f.assignment)
        self.untouched()
    def test_10_missing_private_store_does_not_mean_no_effect(self):
        (self.f.repo/'.git'/w.TEAM_LOCAL).unlink()
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'PRIVATE_STATE_MISSING'):self.f.execute()
        self.assertFalse((self.f.repo/'.git'/w.TEAM_LOCAL).exists())
    def test_11_wrong_epoch_refused(self):
        with patch.dict(os.environ,{'Q3_OWNER_EPOCH':'3'}),self.assertRaisesRegex(w.WorkflowRuntimeError,'OWNER_OR_EPOCH'):self.f.execute()
        self.untouched()
    def test_12_wrong_actor_refused(self):
        with patch.dict(os.environ,{'CODEX_THREAD_ID':'other'}),self.assertRaisesRegex(w.WorkflowRuntimeError,'OBSERVER_ONLY'):self.f.execute()
        self.untouched()
    def test_13_source_hash_drift_refused(self):
        write(self.f.repo/'orchestrator/team_records.py',b'drift\n')
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'DESTINATION_THIRD_STATE'):self.f.execute()
        self.assertEqual(self.f.current_local(),self.f.local)
    def test_14_foreign_dirty_drift_refused(self):
        write(self.f.repo/'foreign.txt',b'new foreign\n')
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'PREIMAGE_CHANGED'):self.f.execute()
        self.assertEqual(self.f.current_local(),self.f.local)
    def test_15_index_drift_refused(self):
        git(self.f.repo,'add','--','foreign.txt')
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'PREIMAGE_CHANGED'):self.f.execute()
        self.assertEqual(self.f.current_local(),self.f.local)
    def test_16_symlink_destination_refused(self):
        p=self.f.repo/'orchestrator/team_records.py';p.unlink();p.symlink_to(self.f.repo/'foreign.txt')
        with self.assertRaises(w.WorkflowRuntimeError):self.f.execute()
        self.assertEqual((self.f.repo/'foreign.txt').read_bytes(),b'foreign bytes preserved\n')
    def test_17_copied_files_do_not_confirm_an_actual_launch(self):
        self.f.execute();data=w._team_current(self.f.repo)[1]
        self.assertEqual(data['operation']['state'],'INTENT');self.assertEqual(data['operation']['evidence'],[])
        for fun in (w.team_observe_remote,w.team_reserve_effect):
            with self.assertRaisesRegex(w.WorkflowRuntimeError,'TERMINAL_LAUNCH_CANNOT_REPLAY'):
                fun(self.f.repo,operation_id=r.CANCEL_ID)
    def test_18_unrelated_unknown_prevents_activation(self):
        local=copy.deepcopy(self.f.local);local['operations']['other']={'state':'UNKNOWN'}
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'OUTSTANDING_EFFECT'):
            r.prove_unreserved(self.f.repo,self.f.raw,self.f.data,local,self.f.assignment)
    def test_19_observation_origin_really_missing_in_supplied_fragment(self):
        o=json.loads((PACKET/'observations.json').read_text());versions={}
        for key,value in o['checkpoint_archive_since_371'].items():
            kind,n,d=key.split('-',2);raw=value.encode();self.assertEqual(w._resume_digest(raw),d)
            versions[key]=(kind,int(n),raw)
        raw=o['checkpoint_archive_since_371']['intent-374-d95491621856728f1f65430bd3521fe89f38f7c29a5eed9bf9442bf92e6e6ce9'].encode()
        data,_=w._resume_document(raw)
        with patch.object(w,'_resume_history',return_value=versions),self.assertRaisesRegex(w.WorkflowRuntimeError,'OBSERVATION_ORIGIN_MISSING:c36b7c'):
            r._history_origin(self.f.repo,raw,data,o['operation'])
    def test_20_intermediate_machine_drift_not_hidden_by_final_agreement(self):
        d0,_=w._resume_document(self.f.origin);d1=copy.deepcopy(d0)
        d1['revision']=2;d1['previous_sha256']=w._resume_digest(self.f.origin);d1['pins']['source_commit']='1'*40
        b1=doc(d1,self.f.body);d2=copy.deepcopy(d0);d2['revision']=3;d2['previous_sha256']=w._resume_digest(b1);b2=doc(d2,self.f.body)
        history={'a':('intent',1,self.f.origin),'b':('intent',2,b1),'c':('intent',3,b2)}
        with patch.object(w,'_resume_history',return_value=history),self.assertRaisesRegex(w.WorkflowRuntimeError,'HISTORY_MACHINE_DRIFT'):
            r._history_origin(self.f.repo,b2,d2,self.f.obs)
    def test_21_output_budget_boundaries_keep_math_hold(self):
        value={'schema':w.TEAM_PLAN_SCHEMA,'status':'HOLD','holds':['NODE_REGISTRY_EXACT_EDGE_REQUIRED'],'pad':''}
        n=len(w.render_plan_v10(value).encode());value['pad']='x'*(16384-n)
        self.assertEqual(len(w.render_plan_v10(value).encode()),16384)
        value['pad']+='x';out=json.loads(w.render_plan_v10(value))
        self.assertEqual(out['status'],'FATAL');self.assertFalse(out['run_authorized']);self.assertEqual(w.TEAM_PLAN_MAX_BYTES,16384)
    def test_22_postinstall_checkpoint_only_known_drift(self):
        self.f.execute();data=w._team_current(self.f.repo)[1];proposed=copy.deepcopy(data)
        proposed['revision']+=1;proposed['previous_sha256']=w._resume_digest(self.f.raw)
        proposed['operation']['state']='CONFIRMED'
        proposed['operation']['evidence']=['control13_recovery:'+self.f.manifest['operation_id']+':'+r.digest(self.f.manifest)]
        plan={'startup':{'control_version':13,'fatal_errors':['STARTUP_CONTROL_BLOB_DRIFT']},
              'holds':['STARTUP_CONTROL_BLOB_DRIFT','NODE_REGISTRY_EXACT_EDGE_REQUIRED']}
        self.assertTrue(r.completed_checkpoint_allowed(self.f.repo,proposed,plan))
        w._team_owner_transition(self.f.repo,data,proposed)
        bad=copy.deepcopy(proposed);bad['pins']['source_commit']='f'*40
        self.assertFalse(r.completed_checkpoint_allowed(self.f.repo,bad,plan))
        badplan=copy.deepcopy(plan);badplan['startup']['fatal_errors'].append('STARTUP_SOURCE_CORRUPT')
        self.assertFalse(r.completed_checkpoint_allowed(self.f.repo,proposed,badplan))
        badplan=copy.deepcopy(plan);badplan['startup']['fatal_errors_omitted']=1
        self.assertFalse(r.completed_checkpoint_allowed(self.f.repo,proposed,badplan))
    def test_23_original_implementation_role_not_relabelled(self):
        data=copy.deepcopy(self.f.assignment);data['role']='independent-checker'
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'ORIGINAL_IMPLEMENTATION_BINDING'):
            r.prove_unreserved(self.f.repo,self.f.raw,self.f.data,self.f.local,data)
    def test_24_old_guard_sees_pending_before_new_control(self):
        original=w._team_local_save
        def crash(repo,before,after,epoch):
            original(repo,before,after,epoch)
            raise RuntimeError('TEST_CRASH_AFTER_PENDING')
        with patch.object(w,'_team_local_save',side_effect=crash),self.assertRaisesRegex(RuntimeError,'TEST_CRASH'):self.f.execute()
        self.assertEqual(sr.validate_battle_v10_control(self.f.repo).version,12)
        self.assertIsNotNone(w._team_pending_integration(self.f.repo))
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'TEAM_INTEGRATION_PENDING'):
            with w._execution_writer_epoch(self.f.repo):pass
        self.assertEqual(self.f.current_local()['operations'][r.CANCEL_ID]['state'],'OBSERVED')
        self.assertEqual(self.f.recover()['status'],'RECOVERED')
    def test_25_fresh_manifest_cannot_replace_pending(self):
        original=w._team_local_save
        def crash(repo,before,after,epoch):original(repo,before,after,epoch);raise RuntimeError('CRASH')
        with patch.object(w,'_team_local_save',side_effect=crash),self.assertRaises(RuntimeError):self.f.execute()
        self.f.manifest['author_id']='other';write(self.f.mp,w._team_json(self.f.manifest))
        with self.assertRaises(w.WorkflowRuntimeError):self.f.execute()
        self.assertEqual(self.f.current_local()['operations'][r.CANCEL_ID]['state'],'OBSERVED')
    def test_26_authorization_cannot_claim_independent_acceptance(self):
        self.f.signoff['independent_acceptance']=True;write(self.f.ap,w._team_json(self.f.signoff))
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'OWNER_SIGNOFF_REQUIRED'):self.f.execute()
        self.untouched()

class CrashBoundaryTests(unittest.TestCase):
    def test_every_file_boundary_and_lost_final_receipt(self):
        for step in range(1,len(r.BASE_HASHES)+1):
            with self.subTest(step=step):
                f=Fixture()
                try:
                    original=w._resume_cas_bytes;calls=[0]
                    def crash(*a,**kw):
                        original(*a,**kw);calls[0]+=1
                        if calls[0]==step:raise RuntimeError('TEST_CRASH')
                    with patch.object(w,'_resume_cas_bytes',side_effect=crash),self.assertRaisesRegex(RuntimeError,'TEST_CRASH'):f.execute()
                    self.assertEqual(f.current_local()['operations'][r.CANCEL_ID]['state'],'OBSERVED')
                    with self.assertRaisesRegex(w.WorkflowRuntimeError,'TEAM_INTEGRATION_PENDING'):w._team_pending_guard(f.repo)
                    f.mp.unlink();f.ap.unlink()
                    self.assertEqual(f.recover()['status'],'RECOVERED')
                    self.assertEqual(f.recover()['status'],'NOOP')
                finally:f.close()
        f=Fixture()
        try:
            original=w._team_local_save;calls=[0]
            def crash(*a,**kw):
                original(*a,**kw);calls[0]+=1
                if calls[0]==2:raise RuntimeError('TEST_LOST_FINAL_RECEIPT')
            with patch.object(w,'_team_local_save',side_effect=crash),self.assertRaisesRegex(RuntimeError,'TEST_LOST_FINAL_RECEIPT'):f.execute()
            self.assertEqual(f.current_local()['operations'][r.CANCEL_ID]['state'],'NOT_EXECUTED')
            self.assertEqual(f.recover()['status'],'NOOP')
        finally:f.close()

class RHCBindingTests(unittest.TestCase):
    def setUp(self):
        self.f=Fixture();self.addCleanup(self.f.close)
        self.f.execute()
        a=copy.deepcopy(self.f.assignment)
        a.update(schema=tr.REPAIR_ASSIGNMENT_SCHEMA,assignment_id='NEW_INDEPENDENT_REVIEW',role='independent-checker',
                 assignee='independent-fixture',base_commit=self.f.head,
                 input_hashes=[{'path':'orchestrator/team_records.py','sha256':w._resume_digest((BASE/'orchestrator/team_records.py').read_bytes())}],
                 permitted_paths=['orchestrator/team_records.py'])
        a['review_binding']={'report_base_commit':self.f.report_base,'candidate_commit':self.f.commit,'candidate_manifest':[{'path':'orchestrator/team_records.py','sha256':w._resume_digest((SOURCE/'orchestrator/team_records.py').read_bytes())}]}
        self.a=tr._validate_assignment(a)
        self.payload={'issue_id':'issue-'+'a'*64,'repair_subject_type':'repository-repair','repair_subject_id':'repair-fixture','candidate_manifest':[{'path':'orchestrator/team_records.py','sha256':w._resume_digest((SOURCE/'orchestrator/team_records.py').read_bytes())}]}
        self.artifact={'schema':tr.REPAIR_REVIEW_V2_SCHEMA,**self.payload,'base_commit':self.f.report_base,
                       'execution_commit':self.f.head,'candidate_commit':self.f.commit,'verdict':'REPAIR_APPROVED'}
    def check_artifact(self,artifact=None,allowed=True,a=None):
        raw=tr.canonical_json(artifact or self.artifact)
        result={'assignment_id':self.a['assignment_id'],'output_locator':'evidence/review.json','output_sha256':w._resume_digest(raw)}
        context=tr.TrustedTeamContext(self.f.data['owner_thread_id'],'local',self.f.identity,2,
            self.f.data['owner_thread_id'],{}, {'evidence/review.json':raw},repair_v2_allowed=allowed)
        return tr._require_repair_review_artifact(self.payload,a or self.a,result,context,expected_base_commit=self.f.report_base)
    def test_27_exact_rhc_review_consumed(self):
        self.assertEqual(len({self.f.report_base,self.f.head,self.f.commit}),3)
        self.assertEqual(self.check_artifact()['candidate_commit'],self.f.commit)
        self.assertEqual(w._team_review_input_commit(self.f.repo,self.a),self.f.report_base)
    def test_28_v2_not_enabled_under_old_context(self):
        with self.assertRaisesRegex(tr.TeamRecordError,'V2_NOT_ENABLED'):self.check_artifact(allowed=False)
    def test_29_each_wrong_coordinate_refused(self):
        for field in ('base_commit','execution_commit','candidate_commit'):
            bad=copy.deepcopy(self.artifact);bad[field]='f'*40
            with self.subTest(field=field),self.assertRaises(tr.TeamRecordError):self.check_artifact(bad)
    def test_30_wrong_candidate_manifest_refused(self):
        bad=copy.deepcopy(self.artifact);bad['candidate_manifest'][0]['sha256']='b'*64
        with self.assertRaisesRegex(tr.TeamRecordError,'RHC_BINDING'):self.check_artifact(bad)
    def test_31_implementation_cannot_use_v2(self):
        bad=copy.deepcopy(self.a);bad['role']='implementation'
        with self.assertRaisesRegex(tr.TeamRecordError,'REVIEW_ONLY'):tr._validate_assignment(bad)
    def test_32_v1_does_not_gain_historical_base_exception(self):
        a=copy.deepcopy(self.a);a['schema']=tr.ASSIGNMENT_SCHEMA;del a['review_binding'];a['base_commit']='e'*40
        old=copy.deepcopy(self.artifact);old['schema']=tr.REPAIR_REVIEW_SCHEMA;old.pop('candidate_commit');old.pop('execution_commit')
        with self.assertRaisesRegex(tr.TeamRecordError,'ASSIGNMENT_BASE_MISMATCH'):self.check_artifact(old,a=a)
    def test_33_v2_requires_v2_review_artifact(self):
        old=copy.deepcopy(self.artifact);old['schema']=tr.REPAIR_REVIEW_SCHEMA;old.pop('candidate_commit');old.pop('execution_commit')
        with self.assertRaisesRegex(tr.TeamRecordError,'V2_ARTIFACT_REQUIRED'):self.check_artifact(old)
    def test_34_old_assignment_cannot_be_upgraded_by_update(self):
        initial=(self.f.repo/w.TEAM_ASSIGNMENTS).read_bytes();state=tr.read_registry(initial,'assignments')
        row=state['assignments'][r.ASSIGNMENT_ID];bad=copy.deepcopy(self.a)
        bad.update(assignment_id=r.ASSIGNMENT_ID,operation='UPDATE',previous_assignment_event_sha256=row['last_event_sha256'],
                   previous_assignment_sha256=tr._payload_sha(row['assignment']))
        with self.assertRaises(tr.TeamRecordError):tr.prepare_assignment(initial,bad,w._resume_digest(initial))
    def test_35_launch_still_requires_current_execution_head(self):
        data=copy.deepcopy(self.f.data);data['operation']['id']='NEW_LAUNCH'
        data['operation']['subject']={'kind':'ASSIGNMENT','id':self.a['assignment_id'],'sha256':tr._assignment_binding_sha(self.a)}
        rows={'assignments':{self.a['assignment_id']:{'assignment':self.a}}}
        with patch.object(w,'_team_assignments',return_value=rows):
            out=w._team_launch_binding(self.f.repo,data);self.assertEqual(out['head'],self.f.head)
            bad=copy.deepcopy(self.a);bad['base_commit']='a'*40;rows['assignments'][self.a['assignment_id']]['assignment']=bad
            data['operation']['subject']['sha256']=tr._assignment_binding_sha(bad)
            with self.assertRaisesRegex(w.WorkflowRuntimeError,'LAUNCH_BINDING_CHANGED'):w._team_launch_binding(self.f.repo,data)


class AdditionalBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.f=Fixture();self.addCleanup(self.f.close)
    def test_36_legitimate_import_expansion_not_engine_drift(self):
        import sys, types
        before=w._team_integration_engine(self.f.repo)
        name='orchestrator._TEST_IMPORTED_LATER'
        mod=types.ModuleType(name);mod.__file__=str(self.f.engine/'orchestrator/tests/test_control13_recovery.py')
        with patch.dict(sys.modules,{name:mod}):
            after=w._team_integration_engine(self.f.repo)
            self.assertNotEqual(before,after)
            self.assertTrue(r._same_engine(before,after))
            wrong=copy.deepcopy(before);wrong['commit']='f'*40
            self.assertFalse(r._same_engine(wrong,after))
            wrong=copy.deepcopy(before);wrong['source_sha256']['orchestrator/workflow_runtime.py']='f'*64
            self.assertFalse(r._same_engine(wrong,after))
    def test_37_checkpoint_real_cas_after_recovery(self):
        self.f.execute()
        prior=w._team_current(self.f.repo)[1];nextdata=copy.deepcopy(prior)
        nextdata['revision']+=1;nextdata['previous_sha256']=w._resume_digest(self.f.raw)
        nextdata['operation']['state']='CONFIRMED'
        nextdata['operation']['evidence']=['control13_recovery:'+self.f.manifest['operation_id']+':'+r.digest(self.f.manifest)]
        path=self.f.root/'checkpoint.json.md';payload=doc(nextdata,self.f.body);write(path,payload)
        # Only the unavailable deep startup plan is injected, not the checkpoint writer.
        plan={'status':'FATAL','startup':{'control_version':13,'team_runtime_version':1,
              'fatal_errors':['STARTUP_CONTROL_BLOB_DRIFT']},
              'holds':['STARTUP_CONTROL_BLOB_DRIFT','NODE_REGISTRY_EXACT_EDGE_REQUIRED']}
        with patch.object(w,'live_plan_v10',return_value=plan):
            result=w.resume_checkpoint(self.f.repo,candidate=path,expected_sha256=w._resume_digest(self.f.raw))
        self.assertEqual(result['status'],'SAVED')
        self.assertEqual((self.f.repo/w.RESUME_PATH).read_bytes(),payload)
        got=w._team_current(self.f.repo)[1]
        for key in ('pins','stages','source_manifest','ownership'):
            self.assertEqual(got[key],prior[key])
        self.assertEqual(got['operation']['state'],'CONFIRMED')
        self.assertEqual(self.f.current_local()['operations'][r.CANCEL_ID]['state'],'NOT_EXECUTED')
    def test_38_wrong_checkpoint_receipt_rejected(self):
        self.f.execute();prior=w._team_current(self.f.repo)[1];bad=copy.deepcopy(prior)
        bad['operation']['state']='CONFIRMED';bad['operation']['evidence']=['claim:agent-launched']
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'CHECKPOINT_EVIDENCE_REQUIRED'):
            w._team_owner_transition(self.f.repo,prior,bad)
    def test_39_foreign_drift_mid_install_keeps_pending(self):
        original=w._resume_cas_bytes;calls=[0]
        def changed(*a,**kw):
            original(*a,**kw);calls[0]+=1
            if calls[0]==1:write(self.f.repo/'foreign.txt',b'foreign concurrent change\n')
        with patch.object(w,'_resume_cas_bytes',side_effect=changed),self.assertRaisesRegex(w.WorkflowRuntimeError,'FINAL_PREIMAGE_CHANGED'):
            self.f.execute()
        self.assertEqual(self.f.current_local()['operations'][r.CANCEL_ID]['state'],'OBSERVED')
        self.assertIsNotNone(w._team_pending_integration(self.f.repo))
    def test_42_unknown_private_state_and_malformed_manifest_refused(self):
        bad=copy.deepcopy(self.f.local);bad['operations']['strange']={'state':'FUTURE_UNKNOWN'}
        self.f.put_local(bad)
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'UNCLASSIFIED_OPERATION_STATE'):
            r.prove_unreserved(self.f.repo,self.f.raw,self.f.data,bad,self.f.assignment)
        malformed=copy.deepcopy(self.f.manifest);malformed['files']=[False]
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'MANIFEST_EXACT_SCOPE'):r.validate_manifest(malformed)
    def test_43_large_saved_engine_has_bounded_pending_card(self):
        original=w._team_local_save
        def stop(repo,before,after,epoch):original(repo,before,after,epoch);raise RuntimeError('AFTER_PENDING')
        with patch.object(w,'_team_local_save',side_effect=stop),self.assertRaises(RuntimeError):self.f.execute()
        saved=copy.deepcopy(self.f.current_local()['operations'][self.f.manifest['operation_id']]['integration'])
        saved['engine']['source_sha256'].update({'orchestrator/module_'+str(i)+'.py':'a'*64 for i in range(600)})
        plan=r.recovery_plan(self.f.repo,self.f.manifest['operation_id'],saved)
        self.assertLess(len(w.render_plan_v10(plan).encode()),16384)
        self.assertEqual(plan['holds'],['CONTROL13_RECOVERY_PENDING','NODE_REGISTRY_EXACT_EDGE_REQUIRED'])
        self.assertEqual(plan['continuation']['recovery']['engine']['saved_metadata_sha256'],r.digest(saved['engine']))
    def test_44_publication_prefix_scope_rejected_before_reservation(self):
        self.f.execute()
        write(self.f.repo/'unpublished-evidence.txt',b'earlier unpublished evidence\n')
        git(self.f.repo,'add','--','unpublished-evidence.txt')
        git(self.f.repo,'commit','-qm','fixture extra unpublished history')
        head=git(self.f.repo,'rev-parse','HEAD');data=copy.deepcopy(self.f.data);data['pins']['head']=head
        inputs={'orchestrator/team_records.py':w._resume_digest((SOURCE/'orchestrator/team_records.py').read_bytes())}
        data['operation']={'id':'repair-fixture:publication','kind':'PUBLISH','state':'INTENT','command':'publication',
             'subject':{'kind':'REPAIR','id':'repair-fixture','sha256':r.digest(inputs)},'inputs':inputs,'evidence':[]}
        observed={**self.f.obs,'remote_commit':self.f.report_base};before=self.f.current_local()
        # This plant supplies a prior review so the tested gate is cumulative Git scope.
        # It is not a synthetic positive publication approval.
        with patch.object(w,'_team_publication_repair',return_value='issue-fixture'),self.assertRaisesRegex(w.WorkflowRuntimeError,'EXISTING_HISTORY_OUTSIDE_SCOPE'):
            w._team_publication_snapshot(self.f.repo,self.f.raw,data,observed)
        self.assertEqual(self.f.current_local(),before)
    def test_40_plan_printed_fatal_returns_two(self):
        import io, sys
        oversized={'schema':w.TEAM_PLAN_SCHEMA,'status':'READY','run_authorized':True,'padding':'x'*20000}
        with patch.object(w,'live_plan_v10',return_value=oversized),patch.object(sys,'argv',['workflow_runtime.py','--root',str(self.f.repo),'plan']),patch('sys.stdout',new_callable=io.StringIO) as out:
            code=w.main()
        self.assertEqual(code,2);self.assertEqual(json.loads(out.getvalue())['status'],'FATAL')
        self.assertLessEqual(len(out.getvalue().encode()),16384)
    def test_41_actual_native_chain_v2_and_missing_native_refused(self):
        from dataclasses import replace
        self.f.execute()
        a=copy.deepcopy(self.f.assignment)
        a.update(schema=tr.REPAIR_ASSIGNMENT_SCHEMA,assignment_id='NEW_CHECKER_NATIVE',role='independent-checker',
                 assignee='checker-native-fixture',base_commit=self.f.head,subject='repair-fixture',
                 resolved_model='gpt-5.6-luna',resolved_effort='max',
                 input_hashes=[{'path':'orchestrator/team_records.py','sha256':w._resume_digest((BASE/'orchestrator/team_records.py').read_bytes())}],
                 permitted_paths=['orchestrator/team_records.py'])
        a['review_binding']={'report_base_commit':self.f.report_base,'candidate_commit':self.f.commit,'candidate_manifest':[{'path':'orchestrator/team_records.py','sha256':w._resume_digest((SOURCE/'orchestrator/team_records.py').read_bytes())}]}
        a=tr._validate_assignment(a)
        payload={'schema':tr.ISSUE_TRANSITION_SCHEMA,'issue_id':'issue-'+'a'*64,'report_id':'report-'+'b'*64,
                 'transition':'FIX_VERIFIED','actor_id':a['assignee'],'actor_role':'independent-checker',
                 'source_binding':[{'locator':'git:'+self.f.report_base+':'+row['path'],'sha256':row['sha256']} for row in a['input_hashes']],
                 'reason':'TEST ONLY: repair review','previous_event_sha256':'d'*64,'previous_state_sha256':'e'*64,
                 'repair_subject_type':'repository-repair','repair_subject_id':'repair-fixture',
                 'candidate_manifest':[{'path':'orchestrator/team_records.py','sha256':w._resume_digest((SOURCE/'orchestrator/team_records.py').read_bytes())}]}
        artifact={'schema':tr.REPAIR_REVIEW_V2_SCHEMA,'issue_id':payload['issue_id'],'repair_subject_type':payload['repair_subject_type'],
                  'repair_subject_id':payload['repair_subject_id'],'base_commit':self.f.report_base,'execution_commit':self.f.head,
                  'candidate_commit':self.f.commit,'candidate_manifest':[{'path':'orchestrator/team_records.py','sha256':w._resume_digest((SOURCE/'orchestrator/team_records.py').read_bytes())}],'verdict':'REPAIR_APPROVED'}
        output=tr.canonical_json(artifact);output_hash=w._resume_digest(output)
        observations=[]
        for phase,state in [('LAUNCH','RUNNING'),('RESULT','COMPLETED')]:
            eh=[{'locator':'evidence/'+phase.lower()+'.out','sha256':output_hash if phase=='RESULT' else 'a'*64},
                {'locator':'provider/'+phase.lower()+'.json','sha256':'a'*64}]
            observations.append({'schema':tr.NATIVE_OBSERVATION_SCHEMA,'assignment_id':a['assignment_id'],'phase':phase,
              'operation_id':'native-'+phase.lower(),'owner_task':a['owner_task'],'owner_installation_ref':a['owner_installation_ref'],
              'owner_epoch':a['owner_epoch'],'assignee':a['assignee'],'native_agent_id':'agent-TEST-only','native_owner_task':a['owner_task'],
              'requested_model':a['requested_model'],'requested_effort':a['requested_effort'],'resolved_model':a['resolved_model'],
              'resolved_effort':a['resolved_effort'],'subject':a['subject'],'state':state,
              'output_locator':eh[0]['locator'],'output_sha256':eh[0]['sha256'],'provider_receipt_locator':eh[1]['locator'],
              'provider_receipt_sha256':eh[1]['sha256'],'payload_sha256':tr._assignment_binding_sha(a),
              'evidence_sha256':w._resume_digest(tr.canonical_json(eh)),
              'source_sha256':w._resume_digest(tr.canonical_json(a['input_hashes']))})
        payload['evidence']=[{'locator':'evidence/result.out','sha256':output_hash}]
        ctx=tr.TrustedTeamContext(a['owner_task'],a['owner_host'],a['owner_installation_ref'],a['owner_epoch'],
                  a['owner_task'],{a['assignment_id']:observations},{'evidence/result.out':output},repair_v2_allowed=True)
        reg={'assignments':{a['assignment_id']:{'assignment':a}}}
        result=tr.validate_issue_event_actor(payload,reg,ctx,expected_base_commit=self.f.report_base)
        self.assertEqual(result['actor_class'],'independent')
        original_sources={row['path']:row['sha256'] for row in a['input_hashes']}
        candidate_sources={row['path']:row['sha256'] for row in a['review_binding']['candidate_manifest']}
        self.assertNotEqual(original_sources,candidate_sources)
        w._team_validate_repair_source_set(payload['source_binding'],original_sources)
        with self.assertRaises(w.WorkflowRuntimeError):
            w._team_validate_repair_source_set(payload['source_binding'],candidate_sources)
        issue={'issue_id':payload['issue_id'],'state':'FIX_VERIFIED','report':{'base_commit':self.f.report_base},
               'repair_subject_id':'repair-fixture','repair_candidate_manifest':a['review_binding']['candidate_manifest'],
               'repair_sources':original_sources}
        issues={'issues':{issue['issue_id']:issue},'events':[{'issue_id':issue['issue_id'],'payload':payload}]}
        data=copy.deepcopy(self.f.data);data['operation']={'command':'publication','id':'repair-fixture:publication',
            'subject':{'kind':'REPAIR','id':'repair-fixture','sha256':r.digest(candidate_sources)}}
        # Only the registry/native adapter inputs are fixtures; full validators execute.
        with patch.object(tr,'read_registry',return_value=issues),patch.object(w,'_team_assignments',return_value=reg),patch.object(w,'_team_assignment_context',return_value=ctx):
            self.assertEqual(w._team_publication_repair(self.f.repo,data,candidate_sources),issue['issue_id'])
            issue['repair_sources']=candidate_sources
            with self.assertRaisesRegex(w.WorkflowRuntimeError,'SOURCE_BINDING_CHANGED'):
                w._team_publication_repair(self.f.repo,data,candidate_sources)
        with self.assertRaises(tr.TeamRecordError):
            tr.validate_issue_event_actor(payload,reg,replace(ctx,observations={}),expected_base_commit=self.f.report_base)
        badobs=copy.deepcopy(observations);badobs[1]['native_agent_id']='another-agent'
        with self.assertRaises(tr.TeamRecordError):
            tr.validate_issue_event_actor(payload,reg,replace(ctx,observations={a['assignment_id']:badobs}),expected_base_commit=self.f.report_base)
        with self.assertRaises(tr.TeamRecordError):
            tr.validate_issue_event_actor(payload,reg,replace(ctx,repair_v2_allowed=False),expected_base_commit=self.f.report_base)



def native_bundle(assignment, *, phase, output, agent_id='TEST_NATIVE_NONAUTHOR_AGENT'):
    """SYNTHETIC provider fixture; never usable as evidence for a live operation."""
    import base64
    artifacts={}
    oid=assignment['assignment_id']+':'+phase.lower()
    observed={'schema':tr.NATIVE_OBSERVATION_SCHEMA,'assignment_id':assignment['assignment_id'],
        'phase':phase,'operation_id':oid,'owner_task':assignment['owner_task'],
        'owner_installation_ref':assignment['owner_installation_ref'],'owner_epoch':assignment['owner_epoch'],
        'assignee':assignment['assignee'],'native_agent_id':agent_id,'native_owner_task':assignment['owner_task'],
        'requested_model':assignment['requested_model'],'requested_effort':assignment['requested_effort'],
        'resolved_model':assignment['requested_model'],'resolved_effort':assignment['requested_effort'],
        'subject':assignment['subject'],'state':'RUNNING' if phase=='LAUNCH' else 'COMPLETED',
        'payload_sha256':tr._assignment_binding_sha(assignment),
        'source_sha256':w._resume_digest(tr.canonical_json(assignment['input_hashes']))}
    for prefix,raw in [('output',output),('provider_receipt',w._team_json({'TEST_ONLY_NATIVE_PROVIDER':True,'phase':phase,'agent_id':agent_id}))]:
        loc='docs/session_protocols/test-provider/'+assignment['assignment_id']+'-'+phase+'-'+prefix+'.json'
        observed[prefix+'_locator']=loc;observed[prefix+'_sha256']=w._resume_digest(raw)
        artifacts[loc]=base64.b64encode(raw).decode()
    observed['evidence_sha256']=w._resume_digest(tr.canonical_json([
        {'locator':observed[p+'_locator'],'sha256':observed[p+'_sha256']} for p in ('output','provider_receipt')]))
    return {'observation':observed,'artifacts':artifacts}


def review_request_fixture(f):
    quote='TEST ONLY: bounded checkpoint/cancellation/publication recovery; keep limit 16384 and guards.'
    source='TEST FIXTURE USER INSTRUCTION\n'+quote+'\n'
    grant={'recorded_by':f.data['owner_thread_id'],'source_locator':'fixture:owner-instruction',
        'source_text':source,'source_sha256':w._resume_digest(source.encode()),'instruction':quote,
        'scope':r.SCOPED_WORK,'cancel_operation_id':r.CANCEL_ID,'plan_max_bytes':16384,'exact_manifest_human_approved':False}
    a=copy.deepcopy(f.assignment)
    a.update(assignment_id=r.review_operation_id(f.manifest),schema=tr.ASSIGNMENT_SCHEMA,
        assignee='TEST_DISTINCT_OPERATIONAL_REVIEWER',role='independent-checker',subject=r.digest(f.manifest),
        base_commit=f.commit,input_hashes=[{'path':p,'sha256':h} for p,h in sorted(r.combined_source_manifest(f.manifest).items())],
        permitted_paths=sorted(r.BASE_HASHES),resolved_model=None,resolved_effort=None,
        requested_model='gpt-5.6-terra',requested_effort='medium',
        owner_task=f.data['owner_thread_id'],owner_host=f.data['owner_host_id'],owner_epoch=2,
        owner_installation_ref=f.identity,operation='CREATE',status='ASSIGNED',
        previous_assignment_sha256='ABSENT',previous_assignment_event_sha256='ABSENT')
    return {'schema':r.REVIEW_SCHEMA,'manifest':f.manifest,'grant':grant,'assignment':a,'read_only':True}


def operational_review_fixture(f, *, complete=True):
    remote=f.root/'remote.git';git(f.root,'clone','-q','--bare',str(f.repo),str(remote))
    git(remote,'update-ref','refs/heads/rh_clean',f.remote_base)
    git(f.repo,'remote','add','origin',str(remote))
    request=review_request_fixture(f);path=f.root/'TEST_ONLY_review_request.json';write(path,w._team_json(request))
    out=r.reserve_operational_review(f.repo,candidate=path,expected_sha256=r.digest(request))
    assert out['execute_once'] is False
    oid=r.review_operation_id(f.manifest)
    if not complete:return request,path
    permit=r.operational_launch_permit(f.repo,operation_id=oid);assert permit['execute_once'] is True
    result={'schema':r.REVIEW_RESULT_SCHEMA,'reviewer_id':request['assignment']['assignee'],'author_ids':f.manifest['author_ids'],
            'manifest_sha256':r.digest(f.manifest),'engine_commit':f.commit,'combined_source_manifest':r.combined_source_manifest(f.manifest),
            'read_only':True,'checks':sorted(r.REQUIRED_CHECKS),'verdict':'ACTIVATION_CANDIDATE_APPROVED'}
    for phase,raw in [('LAUNCH',b'TEST read-only native launch\n'),('RESULT',w._team_json(result))]:
        bundle=native_bundle(request['assignment'],phase=phase,output=raw)
        ep=f.root/('TEST_ONLY_'+phase+'.json');write(ep,w._team_json(bundle))
        out=r.observe_operational_review(f.repo,operation_id=oid,candidate=ep,expected_sha256=r.digest(bundle))
    return out['activation_record']


class OperationalReviewTests(unittest.TestCase):
    """Real reservation/CAS/Git/native validators; all provider observations are fixtures."""
    def setUp(self): self.f=Fixture()
    def tearDown(self):self.f.close()
    def test_01_distinct_review_then_eight_file_recovery(self):
        a=operational_review_fixture(self.f)
        self.assertNotEqual(a['operational_review']['reviewer_id'],self.f.data['owner_thread_id'])
        self.assertIn(self.f.data['owner_thread_id'],a['operational_review']['author_ids'])
        ap=self.f.root/'TEST_activation.json';write(ap,w._team_json(a))
        out=r.recover_unreserved(self.f.repo,candidate=self.f.mp,expected_sha256=r.digest(self.f.manifest),
            activation_record=ap,expected_activation_sha256=r.digest(a),execute=True)
        self.assertEqual(out['status'],'RECOVERED');self.assertEqual(len(out['files']),8)
        row=next(x for x in self.f.manifest['files'] if x['path']==r.SELECTOR_TEST_PATH)
        self.assertNotEqual(row['before_sha256'],row['sha256'])
        self.assertEqual(w._resume_digest((self.f.repo/r.SELECTOR_TEST_PATH).read_bytes()),row['sha256'])
        self.assertEqual((self.f.repo/'foreign.txt').read_bytes(),b'foreign bytes preserved\n')
    def test_02_pending_review_fences_old_writers_preserves_old_intent(self):
        request,path=operational_review_fixture(self.f,complete=False)
        self.assertEqual(w._team_current(self.f.repo)[1]['operation']['id'],r.CANCEL_ID)
        self.assertEqual(self.f.current_local()['operations'][r.CANCEL_ID]['state'],'OBSERVED')
        self.assertEqual(sr.validate_battle_v10_control(self.f.repo).version,12)
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'TEAM_INTEGRATION_PENDING'):
            w._team_pending_guard(self.f.repo)
        saved=w._team_pending_integration(self.f.repo)[1]
        plan=r.operational_review_plan(self.f.repo,r.review_operation_id(self.f.manifest),saved)
        self.assertLess(len(w.render_plan_v10(plan).encode()),16384)
        self.assertIn('NODE_REGISTRY_EXACT_EDGE_REQUIRED',plan['holds'])
    def test_03_lost_launch_permit_never_replayed(self):
        request,path=operational_review_fixture(self.f,complete=False);oid=r.review_operation_id(self.f.manifest)
        self.assertTrue(r.operational_launch_permit(self.f.repo,operation_id=oid)['execute_once'])
        self.assertFalse(r.operational_launch_permit(self.f.repo,operation_id=oid)['execute_once'])
        self.assertFalse(r.reserve_operational_review(self.f.repo,candidate=path,expected_sha256=r.digest(request))['execute_once'])
        with self.assertRaises(w.WorkflowRuntimeError):self.f.execute()
    def test_04_author_cannot_reserve_review(self):
        req=review_request_fixture(self.f);req['assignment']['assignee']=self.f.data['owner_thread_id']
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'DISTINCT_READONLY'):r._review_request(req)
        req['assignment']['assignee']='Proshka'
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'DISTINCT_READONLY'):r._review_request(req)
    def test_05_missing_author_rejected(self):
        m=copy.deepcopy(self.f.manifest);m['author_ids']=['Proshka']
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'MANIFEST_IDENTITY'):r.validate_manifest(m)
    def test_06_native_observation_requires_consumed_permit(self):
        req,path=operational_review_fixture(self.f,complete=False);b=native_bundle(req['assignment'],phase='LAUNCH',output=b'TEST\n')
        ep=self.f.root/'test-evidence.json';write(ep,w._team_json(b))
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'PERMIT_REQUIRED'):
            r.observe_operational_review(self.f.repo,operation_id=r.review_operation_id(self.f.manifest),candidate=ep,expected_sha256=r.digest(b))
    def test_07_wrong_provider_bytes_rejected_before_write(self):
        req,path=operational_review_fixture(self.f,complete=False);oid=r.review_operation_id(self.f.manifest)
        r.operational_launch_permit(self.f.repo,operation_id=oid);before=self.f.current_local()
        b=native_bundle(req['assignment'],phase='LAUNCH',output=b'TEST\n')
        b['artifacts'][b['observation']['provider_receipt_locator']]='Y2hhbmdlZA=='
        ep=self.f.root/'test-evidence.json';write(ep,w._team_json(b))
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'HASH_CHANGED'):
            r.observe_operational_review(self.f.repo,operation_id=oid,candidate=ep,expected_sha256=r.digest(b))
        self.assertEqual(before,self.f.current_local())
    def test_08_fabricated_activation_without_reserved_provider_review_rejected(self):
        a=operational_review_fixture(self.f);local=self.f.current_local();local['operations'].pop(r.review_operation_id(self.f.manifest));self.f.put_local(local)
        ap=self.f.root/'activation.json';write(ap,w._team_json(a))
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'CHECKED_NATIVE_OPERATIONAL_REVIEW_REQUIRED'):
            r.recover_unreserved(self.f.repo,candidate=self.f.mp,expected_sha256=r.digest(self.f.manifest),activation_record=ap,expected_activation_sha256=r.digest(a),execute=True)
    def test_09_changed_source_before_permit_stops_without_launch(self):
        operational_review_fixture(self.f,complete=False)
        write(self.f.repo/'orchestrator/team_records.py',b'THIRD STATE\n')
        with self.assertRaises(w.WorkflowRuntimeError):r.operational_launch_permit(self.f.repo,operation_id=r.review_operation_id(self.f.manifest))
        saved=self.f.current_local()['operations'][r.review_operation_id(self.f.manifest)]['integration']
        self.assertFalse(saved['launch_attempted'])
    def test_10_different_agent_result_is_not_same_review(self):
        a=operational_review_fixture(self.f)
        saved=copy.deepcopy(self.f.current_local()['operations'][r.review_operation_id(self.f.manifest)]['integration'])
        saved['native'][1]['native_agent_id']='OTHER_NATIVE_AGENT'
        with self.assertRaises(tr.TeamRecordError):r._review_result(saved)


    def test_11_prepare_request_is_read_only_and_uses_reserved_reviewer_profile(self):
        req=review_request_fixture(self.f);before=self.f.current_local()
        result=r.prepare_operational_review_request(self.f.repo,self.f.manifest,req['grant'],
            reviewer_id='TEST_NEW_NONAUTHOR',next_check='2026-09-22T23:00:00+00:00')
        self.assertEqual(result['assignment']['requested_model'],'gpt-5.6-terra')
        self.assertEqual(result['assignment']['requested_effort'],'medium')
        self.assertEqual(r._review_request(result),self.f.manifest)
        self.assertEqual(before,self.f.current_local())
    def test_12_endpoint_drift_blocks_native_permit(self):
        operational_review_fixture(self.f,complete=False)
        git(self.f.repo,'remote','set-url','origin',str(self.f.root/'DIFFERENT_REMOTE.git'))
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'REVIEW_ENDPOINT_CHANGED'):
            r.operational_launch_permit(self.f.repo,operation_id=r.review_operation_id(self.f.manifest))
        self.assertFalse(self.f.current_local()['operations'][r.review_operation_id(self.f.manifest)]['integration']['launch_attempted'])


class ScopedAuthorityTests(unittest.TestCase):
    """Instructions, reviewer and native observations here are TEST FIXTURES."""
    def setUp(self):
        self.f=Fixture()
        self.auth=operational_review_fixture(self.f)
        self.authfile=self.f.root/'TEST_ONLY_activation.json'
        self.before=copy.deepcopy(self.f.current_local())
    def tearDown(self):self.f.close()
    def run_scoped(self,*,execute=True):
        write(self.authfile,w._team_json(self.auth))
        return r.recover_unreserved(self.f.repo,candidate=self.f.mp,expected_sha256=r.digest(self.f.manifest),
            activation_record=self.authfile,expected_activation_sha256=r.digest(self.auth),execute=execute)
    def reject(self,pattern):
        with self.assertRaisesRegex(w.WorkflowRuntimeError,pattern):self.run_scoped()
        self.assertEqual(self.before,self.f.current_local())
        for path,sha in r.BASE_HASHES.items():self.assertEqual(w._resume_digest(w._resume_file(self.f.repo,Path(path))),sha)
    def test_scoped_01_grant_review_without_human_signoff(self):
        out=self.run_scoped();self.assertEqual(out['status'],'RECOVERED')
        saved=self.f.current_local()['operations'][self.f.manifest['operation_id']]['integration']
        self.assertNotIn('signoff',saved);self.assertEqual(saved['activation_record'],self.auth)
        self.assertFalse(out['independent_acceptance']);self.assertFalse(out['mathematical_acceptance'])
        self.assertEqual(self.f.current_local()['operations'][r.CANCEL_ID]['state'],'NOT_EXECUTED')
        self.assertEqual(w._team_assignments(self.f.repo)['assignments'][r.ASSIGNMENT_ID]['assignment']['role'],'implementation')
    def test_scoped_02_preflight_no_writes(self):
        out=self.run_scoped(execute=False)
        self.assertFalse(out['owner_signoff_present']);self.assertTrue(out['scoped_activation_present'])
        self.assertEqual(self.before,self.f.current_local())
    def test_scoped_03_no_review(self):
        self.auth['operational_review']={};self.reject('NONAUTHOR_OPERATIONAL_REVIEW_REQUIRED')
    def test_scoped_04_author_not_reviewer(self):
        self.auth['operational_review']['reviewer_id']='Proshka';self.reject('NONAUTHOR_OPERATIONAL_REVIEW_REQUIRED')
    def test_scoped_05_not_renamed_human_signoff(self):
        self.auth['operational_review']['reviewer_id']='HUMAN_OWNER';self.reject('NONAUTHOR_OPERATIONAL_REVIEW_REQUIRED')
    def test_scoped_06_false_human_approval(self):
        self.auth['grant']['exact_manifest_human_approved']=True;self.reject('SCOPED_GRANT_SCOPE_INVALID')
    def test_scoped_07_limit_cannot_expand(self):
        self.auth['grant']['plan_max_bytes']=32768;self.reject('SCOPED_GRANT_SCOPE_INVALID')
    def test_scoped_08_other_launch_cannot_cancel(self):
        self.auth['grant']['cancel_operation_id']='ANOTHER_LAUNCH';self.reject('SCOPED_GRANT_SCOPE_INVALID')
    def test_scoped_09_instruction_absent_from_source(self):
        self.auth['grant']['instruction']='UNSEEN CONSENT';self.reject('SCOPED_GRANT_SOURCE_INVALID')
    def test_scoped_10_source_digest(self):
        self.auth['grant']['source_sha256']='0'*64;self.reject('SCOPED_GRANT_SOURCE_INVALID')
    def test_scoped_11_seven_is_not_whole_scope(self):
        del self.auth['operational_review']['combined_source_manifest'][r.SELECTOR_TEST_PATH]
        self.reject('NONAUTHOR_OPERATIONAL_REVIEW_REQUIRED')
    def test_scoped_12_no_admission_or_push(self):
        for key in ('mathematical_acceptance','native_repair_acceptance','publication_authorized'):
            self.auth[key]=True;self.reject('SCOPED_AUTHORIZATION_INVALID');self.auth[key]=False
    def test_scoped_13_stale_review(self):
        self.auth['operational_review']['manifest_sha256']='0'*64;self.reject('NONAUTHOR_OPERATIONAL_REVIEW_REQUIRED')
    def test_scoped_14_reserved_effect(self):
        local=copy.deepcopy(self.before);local['operations']['other']={'state':'RESERVED'}
        self.f.put_local(local)
        with self.assertRaises(w.WorkflowRuntimeError):self.run_scoped()
        self.assertEqual(local,self.f.current_local())
    def test_scoped_15_copy_crash_input_loss(self):
        original=w._resume_cas_bytes;calls=[0]
        def stop(*args,**kwargs):
            original(*args,**kwargs);calls[0]+=1
            if calls[0]==2:raise RuntimeError('TEST_COPY_INTERRUPTION')
        with patch.object(w,'_resume_cas_bytes',side_effect=stop),self.assertRaisesRegex(RuntimeError,'TEST_COPY_INTERRUPTION'):
            self.run_scoped()
        self.assertIsNotNone(w._team_pending_integration(self.f.repo))
        self.assertEqual(self.f.current_local()['operations'][r.CANCEL_ID]['state'],'OBSERVED')
        with self.assertRaises(w.WorkflowRuntimeError):w._team_pending_guard(self.f.repo)
        self.authfile.unlink();self.f.mp.unlink()
        self.assertEqual(self.f.recover()['status'],'RECOVERED')
        self.assertEqual(self.f.recover()['status'],'NOOP')
    def test_scoped_16_selector_drift(self):
        write(self.f.repo/r.SELECTOR_TEST_PATH,b'omitted selector regression\n')
        with self.assertRaises(w.WorkflowRuntimeError):self.run_scoped()
        self.assertEqual(self.before,self.f.current_local())
    def test_scoped_17_changed_engine(self):
        write(self.f.engine/'engine-extra.txt',b'different engine\n')
        git(self.f.engine,'add','--','engine-extra.txt');git(self.f.engine,'commit','-qm','fixture changed engine')
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'ENGINE_COMMIT_CHANGED'):self.run_scoped()
        self.assertEqual(self.before,self.f.current_local())
    def test_scoped_18_review_evidence(self):
        self.auth['operational_review']['evidence']*=2;self.reject('OPERATIONAL_REVIEW_EVIDENCE_INVALID')
        self.auth['operational_review']['evidence']=[];self.reject('NONAUTHOR_OPERATIONAL_REVIEW_REQUIRED')


    def test_scoped_19_compact_cannot_bypass_unclosed_publication_issue(self):
        self.run_scoped()
        inputs={str(w.RESUME_PATH):w._resume_digest(self.f.raw),
                str(w.RESUME_HISTORY_PATH):w._resume_digest(self.f.history)}
        payload=w._team_json(inputs);sha=w._resume_digest(payload)
        relative='docs/session_protocols/team-evidence-'+sha+'.bin'
        write(self.f.repo/relative,payload)
        data=copy.deepcopy(self.f.data)
        data['operation']={'kind':'PUBLISH','state':'INTENT','id':'TEST_COMPACT_FIRST',
            'command':'publication','subject':{'kind':'REPAIR','id':'TEST_COMPACT_FIRST','sha256':sha},
            'inputs':{relative:sha},'evidence':[]}
        issues={'issues':{'test-open-issue':{'issue_id':'test-open-issue','state':'FIX_VERIFIED',
                                         'report':{'affected_operations':['publication']}}}}
        # Give the negative test completed map intake; it must STILL hit the real
        # unresolved-issue gate. This is not a positive end-to-end publication.
        with patch.object(w,'_team_publication_intake',return_value=None), \
                patch.object(tr,'read_registry',return_value=issues), \
                self.assertRaisesRegex(w.WorkflowRuntimeError,'TEAM_DEPENDENT_OPERATION_HELD'):
            w._team_publication_snapshot(self.f.repo,self.f.raw,data,self.f.obs)


class CombinedPublicationShapeTests(unittest.TestCase):
    """Real Git/validator tests of eight paths and ancestry, NOT live publication."""
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix='q3-combined-publication-')
        self.repo=Path(self.temp.name)
        git(self.repo,'init','-q','-b','rh_clean');git(self.repo,'config','user.name','TEST');git(self.repo,'config','user.email','test@example.invalid')
        self.paths=sorted(r.BASE_HASHES)
        for p in self.paths:
            if r.BASE_HASHES.get(p)!='ABSENT':write(self.repo/p,b'TEST original '+p.encode()+b'\n')
        git(self.repo,'add','.');git(self.repo,'commit','-qm','TEST R original')
        self.R=git(self.repo,'rev-parse','HEAD');self.O=self.R
        self.inputs=[{'path':p,'sha256':w._resume_digest((self.repo/p).read_bytes())}
                     for p in ('orchestrator/team_records.py',r.SELECTOR_TEST_PATH)]
        write(self.repo/'owned-but-not-repair-evidence.txt',b'TEST earlier evidence\n')
        git(self.repo,'add','.');git(self.repo,'commit','-qm','TEST H unpublished prefix')
        self.H=git(self.repo,'rev-parse','HEAD')
        for p in self.paths:write(self.repo/p,(SOURCE/p).read_bytes())
        git(self.repo,'add','--',*self.paths);git(self.repo,'commit','-qm','TEST aggregate repair')
        self.C=git(self.repo,'rev-parse','HEAD')
        self.manifest=[{'path':p,'sha256':w._resume_digest((self.repo/p).read_bytes())} for p in self.paths]
    def tearDown(self):self.temp.cleanup()
    def test_combined_01_exact_eight_commit(self):
        self.assertEqual(len(self.inputs),2);self.assertEqual(len(self.manifest),8)
        result=w._team_validate_repair_candidate(self.repo,{'candidate_commit':self.C,'candidate_manifest':self.manifest},base_commit=self.R)
        self.assertEqual(set(result),set(self.paths))
    def test_combined_02_seven_omits_regressions(self):
        rows=[x for x in self.manifest if x['path']!=r.SELECTOR_TEST_PATH]
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'DIFF_MISMATCH'):
            w._team_validate_repair_candidate(self.repo,{'candidate_commit':self.C,'candidate_manifest':rows},base_commit=self.R)
    def test_combined_03_delta_commit_not_aggregate(self):
        write(self.repo/'orchestrator/control13_recovery.py',b'TEST later delta\n')
        git(self.repo,'add','.');git(self.repo,'commit','-qm','TEST partial latest delta')
        rows=[{'path':p,'sha256':w._resume_digest((self.repo/p).read_bytes())} for p in self.paths]
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'DIFF_MISMATCH'):
            w._team_validate_repair_candidate(self.repo,{'candidate_commit':git(self.repo,'rev-parse','HEAD'),'candidate_manifest':rows},base_commit=self.R)
    def test_combined_04_unpublished_prefix_is_ninth_path(self):
        changed=set(git(self.repo,'diff','--name-only',self.O,self.C).splitlines())
        self.assertEqual(changed-set(self.paths),{'owned-but-not-repair-evidence.txt'})
        self.assertFalse(changed.issubset(set(self.paths)))
    def test_combined_05_two_r_inputs_eight_c_outputs(self):
        observed=json.loads((PACKET/'observations.json').read_text())['assignment']['assignment']
        a=copy.deepcopy(observed)
        a.update(schema=tr.REPAIR_ASSIGNMENT_SCHEMA,assignment_id='TEST_NEW_INDEPENDENT_REVIEW',
                 assignee='test-distinct-reviewer',role='independent-checker',base_commit=self.H,
                 input_hashes=self.inputs,permitted_paths=self.paths)
        a['review_binding']={'report_base_commit':self.R,'candidate_commit':self.C,'candidate_manifest':self.manifest}
        checked=tr._validate_assignment(a)
        self.assertEqual(len(checked['input_hashes']),2)
        self.assertEqual(len(checked['review_binding']['candidate_manifest']),8)
        with patch.object(sr,'validate_battle_v10_control',return_value=sr.ControlIdentity('a'*64,13,'ACTIVE','CHALLENGER_NOT_RH','PX_RH_CLAIM',1)):
            self.assertEqual(w._team_review_input_commit(self.repo,checked),self.R)
        bindings=[{'locator':'git:'+self.R+':'+x['path'],'sha256':x['sha256']} for x in self.inputs]
        w._team_validate_repair_source_set(bindings,{x['path']:x['sha256'] for x in self.inputs})
        with self.assertRaises(w.WorkflowRuntimeError):
            w._team_validate_repair_source_set(bindings,{x['path']:x['sha256'] for x in self.manifest})



class DeliveryHarness:
    """Real transition functions/Git; initial history and provider actions are fixtures.

    Only deep live_plan_v10 is substituted in checkpoint calls: mathematical
    startup dependencies are deliberately not claimed installed by this test.
    """
    def __init__(self):
        self.f=Fixture(history_prefix=True);f=self.f;self.repo=f.repo
        self.trace=[]
        self.original_math=copy.deepcopy({k:f.data[k] for k in ('source_manifest','stages')})
        self.rinputs=[{'path':p,'sha256':w._resume_digest(w._team_git(f.repo,'show',f.report_base+':'+p))}
                      for p in ('orchestrator/team_records.py',r.SELECTOR_TEST_PATH)]
        report={'schema':tr.ISSUE_REPORT_SCHEMA,'reporter_task':'TEST_ORIGINAL_REPORTER',
          'reporter_host':'TEST_LOCAL','assignment_id':'TEST_ORIGINAL_REPORT_ASSIGNMENT','attempt_id':'TEST_ORIGINAL_ATTEMPT',
          'observed_at':'2026-09-22T12:00:00+00:00','subject_id':'TEST_SELECTOR','subject_type':'code-defect',
          'base_commit':f.report_base,'input_paths':self.rinputs,'severity':'MEDIUM','suspected_class':'CODE_DEFECT',
          'expected_behavior':'TEST source binding and publication preserve evidence.',
          'expected_rule_source':{'locator':'TEST/original-rule','sha256':'a'*64},
          'actual_behavior':'TEST original defect','reproduction':'TEST synthetic initial issue, not a live review.',
          'affected_operations':['publication'],'evidence':[{'locator':'TEST/initial-reproduction','sha256':'b'*64}],
          'uncertainty':'Synthetic initial state. All subsequent transitions execute actual runtime.'}
        raw=(f.repo/w.TEAM_ISSUES).read_bytes();raw,_=tr.prepare_report(raw,report,w._resume_digest(raw))
        write(f.repo/w.TEAM_ISSUES,raw)
        for state,actor,role in [('REPRODUCING',f.data['owner_thread_id'],'owner'),
                                  ('CONFIRMED_RULE_CONFLICT','TEST_INITIAL_CLASSIFIER','independent-checker'),
                                  ('ASSIGNED',f.data['owner_thread_id'],'owner')]:
            event=self.event(state,actor,role)
            raw=(f.repo/w.TEAM_ISSUES).read_bytes();raw,_=tr.prepare_issue_event(raw,event,w._resume_digest(raw))
            write(f.repo/w.TEAM_ISSUES,raw)
        # Scope is frozen only AFTER exact initial issue fixture is installed.
        f.manifest=r.prepare_manifest(f.repo);write(f.mp,w._team_json(f.manifest))
        self.activation=operational_review_fixture(f)
        ap=f.root/'TEST_CHAIN_activation.json';write(ap,w._team_json(self.activation))
        result=r.recover_unreserved(f.repo,candidate=f.mp,expected_sha256=r.digest(f.manifest),
                                   activation_record=ap,expected_activation_sha256=r.digest(self.activation),execute=True)
        assert result['status']=='RECOVERED';self.trace.append('RECOVERY_COMPLETE')
        old=copy.deepcopy(w._team_current(f.repo)[1]['operation']);old['state']='CONFIRMED'
        old['evidence']=['control13_recovery:'+f.manifest['operation_id']+':'+r.digest(f.manifest)]
        self.checkpoint(old);self.trace.append('OLD_NOT_EXECUTED_CHECKPOINTED')
        olda=w._team_assignments(f.repo)['assignments'][r.ASSIGNMENT_ID]
        update=copy.deepcopy(olda['assignment']);update.update(operation='UPDATE',status='CANCELLED',
          previous_assignment_event_sha256=olda['last_event_sha256'],previous_assignment_sha256=tr._assignment_state_sha(olda['assignment']))
        self.record('assignment',update,w.TEAM_ASSIGNMENTS);self.trace.append('OLD_IMPLEMENTATION_CANCELLED')
        self.plan=r.combined_delivery_plan(f.repo,candidate_commit=f.commit,implementer='TEST_FIXED_CANDIDATE_PRODUCER',
          reviewer='TEST_DISTINCT_NATIVE_REVIEWER',next_check='2026-09-22T23:00:00+00:00')
        self.producer,self.reviewer=self.plan['assignments']
        self.inputs={x['path']:x['sha256'] for x in self.plan['candidate_manifest']}
        for a in self.plan['assignments']:self.record('assignment',a,w.TEAM_ASSIGNMENTS)
    def close(self):self.f.close()
    def issue(self):
        return next(iter(tr.read_registry((self.repo/w.TEAM_ISSUES).read_bytes(),'issues',archive_loader=lambda p:w._resume_file(self.repo,Path(p)))['issues'].values()))
    def event(self,state,actor,role,*,evidence=None,commit=None):
        i=self.issue()
        p={'schema':tr.ISSUE_TRANSITION_SCHEMA,'issue_id':i['issue_id'],'report_id':i['report_id'],
           'transition':state,'actor_id':actor,'actor_role':role,
           'evidence':evidence or [{'locator':'TEST/initial-transition','sha256':'c'*64}],
           'source_binding':[{'locator':'git:'+self.f.report_base+':'+x['path'],'sha256':x['sha256']} for x in self.rinputs],
           'reason':'TEST evidence for '+state,'previous_event_sha256':i['last_event_sha256'],'previous_state_sha256':tr._state_sha(i)}
        if state in tr.REPAIR_STATES:p.update(repair_subject_type='repository-repair',repair_subject_id=self.f.assignment['subject'])
        if state in {'FIX_VERIFIED','FIX_COMMITTED','FIX_PUSH_VERIFIED'}:p['candidate_manifest']=self.plan['candidate_manifest']
        if commit is not None:p['candidate_commit']=commit
        return p
    def record(self,kind,payload,path):
        ep=self.f.root/('TEST_record_'+str(len(self.trace))+'.json');write(ep,w._team_json(payload))
        result=w.team_record(self.repo,kind=kind,candidate=ep,expected_sha256=w._resume_digest((self.repo/path).read_bytes()))
        assert result['status'] in {'RECORDED','NOOP'}
        return result
    def checkpoint(self,operation,*,integration=None,head=None):
        raw,data,body=w._team_current(self.repo);n=copy.deepcopy(data)
        n.update(revision=data['revision']+1,previous_sha256=w._resume_digest(raw))
        n['operation']=copy.deepcopy(operation)
        if head is not None:n['pins']['head']=head
        candidate=self.f.root/'TEST_next_checkpoint.txt';write(candidate,doc(n,body))
        def diagnostic_plan(*args,**kwargs):
            current=git(self.repo,'rev-parse','HEAD')
            if current==self.f.head:
                return {'status':'FATAL','holds':['STARTUP_CONTROL_BLOB_DRIFT','NODE_REGISTRY_EXACT_EDGE_REQUIRED'],
                  'startup':{'control_version':13,'fatal_errors':['STARTUP_CONTROL_BLOB_DRIFT'],'fatal_errors_omitted':0}}
            return {'status':'HOLD','holds':['NODE_REGISTRY_EXACT_EDGE_REQUIRED'],
                    'startup':{'control_version':13,'fatal_errors':[],'fatal_errors_omitted':0}}
        with patch.object(w,'live_plan_v10',side_effect=diagnostic_plan):
            result=w.resume_checkpoint(self.repo,candidate=candidate,expected_sha256=w._resume_digest(raw),integration_candidate=integration)
        assert result['status']=='SAVED'
        for k in ('source_manifest','stages'):assert w._team_current(self.repo)[1][k]==self.original_math[k]
        return result
    def native(self,a,output):
        import base64
        op={'kind':'ASSIGN','state':'INTENT','id':a['assignment_id']+':launch','evidence':[],
            'subject':{'kind':'ASSIGNMENT','id':a['assignment_id'],'sha256':tr._assignment_binding_sha(a)},'command':'agent-launch','inputs':{}}
        self.checkpoint(op)
        w.team_observe_remote(self.repo,operation_id=op['id']);w.team_reserve_effect(self.repo,operation_id=op['id'])
        with w._execution_writer_epoch(self.repo) as epoch:
            w.team_guard(self.repo,command='agent-launch',paths=[],effect=True)
        bundles=[]
        for phase,out in [('LAUNCH',b'TEST real provider boundary is synthetic here\n'),('RESULT',w._team_json(output))]:
            b=native_bundle(a,phase=phase,output=out,agent_id='TEST_NATIVE_'+a['assignee'])
            # Simulated external immutable evidence materialization, NOT fabricated by runtime.
            for loc,encoded in b['artifacts'].items():write(self.repo/loc,base64.b64decode(encoded))
            ep=self.f.root/('TEST_observe_'+phase+'.json');write(ep,w._team_json(b['observation']))
            r0=w.team_observe_native(self.repo,candidate=ep,expected_sha256=w._resume_digest(ep.read_bytes()))
            assert r0['status']=='OBSERVED';bundles.append(b)
        op['state']='CONFIRMED';op['evidence']=[bundles[0]['observation']['provider_receipt_locator']]
        self.checkpoint(op)
        # Execution completion is observed, not inferred from successful repair acceptance.
        row=w._team_assignments(self.repo)['assignments'][a['assignment_id']]
        update=copy.deepcopy(row['assignment']);observed=bundles[-1]['observation']
        update.update(operation='UPDATE',status='DONE',resolved_model=observed['resolved_model'],
            resolved_effort=observed['resolved_effort'],previous_assignment_event_sha256=row['last_event_sha256'],
            previous_assignment_sha256=tr._assignment_state_sha(row['assignment']))
        self.record('assignment',update,w.TEAM_ASSIGNMENTS)
        return observed
    def accept_native_repair(self):
        a=self.producer;b=a['review_binding']
        result={'schema':'q3_control13_fixed_candidate_result.v1','report_base_commit':self.f.report_base,
          'execution_commit':self.f.head,'candidate_commit':self.f.commit,'candidate_manifest':b['candidate_manifest'],
          'delivery_prefix':b['delivery_prefix'],'author_ids':b['author_ids'],
          'verdict':'CANDIDATE_READY_FOR_INDEPENDENT_REVIEW','mathematical_acceptance':False}
        obs=self.native(a,result)
        evidence=[{'locator':obs['output_locator'],'sha256':obs['output_sha256']}]
        self.record('issue-event',self.event('FIX_CANDIDATE',a['assignee'],'implementation',evidence=evidence),w.TEAM_ISSUES)
        self.trace.append('FIX_CANDIDATE_FROM_REAL_VALIDATORS')
        a=self.reviewer;b=a['review_binding'];issue=self.issue()
        review={'schema':tr.REPAIR_REVIEW_V3_SCHEMA,'issue_id':issue['issue_id'],
          'repair_subject_type':issue['repair_subject_type'],'repair_subject_id':issue['repair_subject_id'],
          'base_commit':self.f.report_base,'execution_commit':self.f.head,'candidate_commit':self.f.commit,
          'candidate_manifest':b['candidate_manifest'],'delivery_prefix':b['delivery_prefix'],'author_ids':b['author_ids'],'verdict':'REPAIR_APPROVED'}
        obs=self.native(a,review);self.review_obs=obs
        evidence=[{'locator':obs['output_locator'],'sha256':obs['output_sha256']}]
        self.record('issue-event',self.event('FIX_VERIFIED',a['assignee'],'independent-checker',evidence=evidence),w.TEAM_ISSUES)
        self.trace.append('FIX_VERIFIED_FROM_DISTINCT_NATIVE_RESULT')
        assert self.issue()['repair_sources']=={x['path']:x['sha256'] for x in self.rinputs}
    def reserve_publication(self):
        sub=self.issue()['repair_subject_id'];oid=sub+':publication'
        op={'kind':'PUBLISH','state':'INTENT','id':oid,'evidence':[],
            'subject':{'kind':'REPAIR','id':sub,'sha256':r.digest(self.inputs)},'command':'publication','inputs':self.inputs}
        self.checkpoint(op,head=self.f.head)
        w.team_observe_remote(self.repo,operation_id=oid);out=w.team_reserve_effect(self.repo,operation_id=oid)
        self.trace.append('FRESH_REMOTE_AND_COMPOSED_RESERVATION')
        saved=w._team_local_operation(self.repo,oid)['publication']['snapshot']
        assert len(saved['files'])==8 and len(saved['carried_prefix']['files'])==23
        return oid
    def publish_reserved(self,oid):
        paths=sorted(self.inputs);before={p:(self.repo/p).read_bytes() for p in [str(w.RESUME_PATH),str(w.RESUME_HISTORY_PATH),'foreign.txt']}
        with w._execution_writer_epoch(self.repo,publication_operation=oid) as epoch:
            w.team_guard(self.repo,command='publication',paths=paths,publication_stage='prepare',writer_epoch=epoch)
            git(self.repo,'add','--',*paths);git(self.repo,'commit','-qm','TEST exact eight-file operational repair')
            P=git(self.repo,'rev-parse','HEAD')
            w.team_guard(self.repo,command='publication',paths=paths,publication_stage='publish',writer_epoch=epoch)
        self.trace.append('NATIVE_COMMIT_AND_ONE_PUSH_PERMIT')
        git(self.repo,'push','origin',P+':refs/heads/rh_clean')
        record={'schema':'q3_team_effect_observation.v1','operation_id':oid,'outcome':'CONFIRMED','evidence':self.inputs}
        rp=self.f.root/'TEST_CONFIRM_PUBLICATION.json';write(rp,w._team_json(record))
        out=w.team_confirm_effect(self.repo,operation_id=oid,candidate=rp,expected_sha256=w._resume_digest(rp.read_bytes()))
        assert out['outcome']=='CONFIRMED'
        self.trace.append('ACTUAL_LOCAL_BARE_PUSH_AND_REMOTE_READBACK')
        for path,value in before.items():assert (self.repo/path).read_bytes()==value
        assert git(self.f.root/'remote.git','rev-parse','refs/heads/rh_clean')==P
        assert git(self.repo,'diff','--name-only',self.f.head,P).splitlines()==paths
        r.check_carried_history(self.repo,self.plan['delivery_prefix'],P)
        op=copy.deepcopy(w._team_current(self.repo)[1]['operation']);op['state']='CONFIRMED';op['evidence']=[str(rp)]
        # Evidence paths in checkpoint are descriptive strings, actual receipt is independently checked.
        self.checkpoint(op)
        ev=[{'locator':'git:'+P+':'+p,'sha256':h} for p,h in sorted(self.inputs.items())]
        for state in ('FIX_COMMITTED','FIX_PUSH_VERIFIED'):
            self.record('issue-event',self.event(state,self.f.data['owner_thread_id'],'owner',evidence=ev,commit=P),w.TEAM_ISSUES)
            self.trace.append(state)
        return P

    def publish_compact_metadata(self):
        """Second publication uses the UNCHANGED compact path after genuine FIX_PUSH."""
        import base64
        base=git(self.repo,'rev-parse','HEAD')
        assert self.issue()['state']=='FIX_PUSH_VERIFIED'
        # Exact owned paths are enumerated before intake; no foreign blanket add.
        paths=[str(w.RESUME_PATH),str(w.RESUME_HISTORY_PATH),str(w.TEAM_ASSIGNMENTS),str(w.TEAM_ISSUES)]
        paths += [p.relative_to(self.repo).as_posix() for p in sorted((self.repo/'docs/session_protocols').glob('team-record-*.json'))]
        paths += [p.relative_to(self.repo).as_posix() for p in sorted((self.repo/'docs/session_protocols/test-provider').glob('*.json'))]
        inputs={p:w._resume_digest((self.repo/p).read_bytes()) for p in sorted(set(paths))}
        for p in (str(w.RESUME_PATH),str(w.RESUME_HISTORY_PATH)):
            inputs[p]=w._resume_digest(w._team_git(self.repo,'show',base+':'+p))
        raw=w._team_json(inputs);sha=w._resume_digest(raw);loc='docs/session_protocols/team-evidence-'+sha+'.bin'
        assignment=self.producer
        mid='TEST_METADATA_MAP_INTAKE'
        manifest={'schema':'q3_team_integration.v1','mode':'EVIDENCE_INTAKE','operation_id':mid,
          'owner_task':self.f.data['owner_thread_id'],'installation_ref':self.f.identity,'epoch':2,
          'expected_head':base,'implementer_assignment':assignment['assignment_id'],
          'assignment_sha256':tr._assignment_binding_sha(assignment),'checker_assignment':None,'candidate_commit':None,
          'files':[{'path':loc,'before_sha256':'ABSENT','sha256':sha,'content_base64':base64.b64encode(raw).decode()}]}
        mf=self.f.root/'TEST_MAP_INTAKE.json';write(mf,w._team_json(manifest))
        op={'kind':'COMPUTE','state':'INTENT','id':mid,'evidence':[],
          'subject':{'kind':'REPAIR','id':mid,'sha256':r.digest(manifest)},
          'command':'workflow-team-integrate-candidate','inputs':{}}
        self.checkpoint(op,integration=mf,head=base)
        w.team_observe_remote(self.repo,operation_id=mid);w.team_reserve_effect(self.repo,operation_id=mid)
        result=w.team_integrate_candidate(self.repo,candidate=mf);assert result['status']=='INTEGRATED'
        op['state']='CONFIRMED';op['evidence']=[loc];self.checkpoint(op)
        oid='TEST_COMPACT_METADATA_PUBLICATION'
        op={'kind':'PUBLISH','state':'INTENT','id':oid,'evidence':[],
          'subject':{'kind':'REPAIR','id':oid,'sha256':sha},'command':'publication','inputs':{loc:sha}}
        self.checkpoint(op,head=base)
        w.team_observe_remote(self.repo,operation_id=oid);w.team_reserve_effect(self.repo,operation_id=oid)
        snapshot=w._team_local_operation(self.repo,oid)['publication']['snapshot']
        assert snapshot['mode']=='COMPACT' and 'carried_prefix' not in snapshot
        final_paths=sorted(snapshot['files'])
        foreign=(self.repo/'foreign.txt').read_bytes()
        with w._execution_writer_epoch(self.repo,publication_operation=oid) as epoch:
            prepare=w.team_guard(self.repo,command='publication',paths=final_paths,publication_stage='prepare',writer_epoch=epoch)
            assert prepare['execute_once'] is True
            git(self.repo,'add','--',*final_paths);git(self.repo,'commit','-qm','TEST exact metadata after verified repair')
            tip=git(self.repo,'rev-parse','HEAD')
            pub=w.team_guard(self.repo,command='publication',paths=final_paths,publication_stage='publish',writer_epoch=epoch)
            assert pub['execute_once'] is True
        git(self.repo,'push','origin',tip+':refs/heads/rh_clean')
        record={'schema':'q3_team_effect_observation.v1','operation_id':oid,'outcome':'CONFIRMED','evidence':{loc:sha}}
        rp=self.f.root/'TEST_COMPACT_CONFIRM.json';write(rp,w._team_json(record))
        out=w.team_confirm_effect(self.repo,operation_id=oid,candidate=rp,expected_sha256=w._resume_digest(rp.read_bytes()))
        assert out['outcome']=='CONFIRMED'
        assert (self.repo/'foreign.txt').read_bytes()==foreign
        assert git(self.f.root/'remote.git','rev-parse','refs/heads/rh_clean')==tip
        op['state']='CONFIRMED';op['evidence']=[loc];self.checkpoint(op)
        assert self.issue()['state']=='FIX_PUSH_VERIFIED'
        self.trace.append('UNCHANGED_COMPACT_METADATA_PUSH_AND_REMOTE_READBACK')
        self.trace.append('FINAL_CHECKPOINT_CONFIRMED_NO_RECURSIVE_PUSH')
        return tip


class FullDeliveryChainTests(unittest.TestCase):
    def test_01_operational_review_migration_native_lifecycle_and_real_local_push(self):
        h=DeliveryHarness();self.addCleanup(h.close)
        h.accept_native_repair();oid=h.reserve_publication();P=h.publish_reserved(oid)
        self.assertEqual(h.issue()['state'],'FIX_PUSH_VERIFIED')
        self.assertEqual(w._team_current(h.repo)[1]['operation']['state'],'CONFIRMED')
        self.assertEqual(w._team_current(h.repo)[1]['source_manifest'],h.original_math['source_manifest'])
        self.assertEqual(w._team_assignments(h.repo)['assignments'][r.ASSIGNMENT_ID]['assignment']['role'],'implementation')
        self.assertEqual(w._team_assignments(h.repo)['assignments'][r.ASSIGNMENT_ID]['assignment']['status'],'CANCELLED')
        self.assertTrue(git(h.repo,'merge-base','--is-ancestor',h.f.head,P)=='')
        for a in (h.producer,h.reviewer):self.assertEqual(w._team_assignments(h.repo)['assignments'][a['assignment_id']]['assignment']['status'],'DONE')
        tip=h.publish_compact_metadata()
        self.assertTrue(git(h.repo,'merge-base','--is-ancestor',P,tip)=='')
        print('TEST_ONLY_CHAIN:',json.dumps(h.trace))



class DeliveryNegativeTests(unittest.TestCase):
    def test_01_missing_native_review_rejected_before_intent_write(self):
        h=DeliveryHarness();self.addCleanup(h.close)
        before=(h.repo/w.RESUME_PATH).read_bytes();local=h.f.current_local()
        sub=h.issue()['repair_subject_id']
        op={'kind':'PUBLISH','state':'INTENT','id':sub+':publication','evidence':[],
          'subject':{'kind':'REPAIR','id':sub,'sha256':r.digest(h.inputs)},'command':'publication','inputs':h.inputs}
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'NATIVE_FIX_VERIFIED_REQUIRED'):
            h.checkpoint(op,head=h.f.head)
        self.assertEqual(before,(h.repo/w.RESUME_PATH).read_bytes())
        self.assertEqual(local,h.f.current_local())
    def test_02_foreign_drift_blocks_prepare_without_commit(self):
        h=DeliveryHarness();self.addCleanup(h.close);h.accept_native_repair();oid=h.reserve_publication()
        write(h.repo/'foreign.txt',b'TEST uncooperative foreign edit\n')
        with w._execution_writer_epoch(h.repo,publication_operation=oid) as epoch:
            with self.assertRaisesRegex(w.WorkflowRuntimeError,'FOREIGN_PREIMAGE_CHANGED'):
                w.team_guard(h.repo,command='publication',paths=sorted(h.inputs),publication_stage='prepare',writer_epoch=epoch)
        self.assertEqual(git(h.repo,'rev-parse','HEAD'),h.f.head)
        self.assertFalse(w._team_local_operation(h.repo,oid)['publication']['push_attempted'])
        with self.assertRaises(w.WorkflowRuntimeError):w._team_pending_guard(h.repo)
    def test_03_actual_remote_drift_blocks_before_reservation(self):
        h=DeliveryHarness();self.addCleanup(h.close);h.accept_native_repair()
        remote=h.f.root/'remote.git'
        tree=git(remote,'rev-parse',h.f.remote_base+'^{tree}')
        changed=git(remote,'-c','user.name=TEST','-c','user.email=test@example.invalid',
                    'commit-tree',tree,'-p',h.f.remote_base,'-m','TEST remote competing owner commit')
        git(remote,'update-ref','refs/heads/rh_clean',changed)
        with self.assertRaises(w.WorkflowRuntimeError):h.reserve_publication()
        row=w._team_local_operation(h.repo,h.issue()['repair_subject_id']+':publication')
        self.assertEqual(row['state'],'OBSERVED');self.assertNotIn('publication',row)
        self.assertEqual(git(h.repo,'rev-parse','HEAD'),h.f.head)
    def test_04_pending_publication_blocks_lifecycle_writer(self):
        h=DeliveryHarness();self.addCleanup(h.close);h.accept_native_repair();oid=h.reserve_publication()
        before=(h.repo/w.TEAM_ISSUES).read_bytes()
        event=h.event('FIX_COMMITTED',h.f.data['owner_thread_id'],'owner',
          evidence=[{'locator':'git:'+h.f.commit+':'+p,'sha256':sha} for p,sha in h.inputs.items()],commit=h.f.commit)
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'TEAM_PUBLICATION_PENDING'):
            h.record('issue-event',event,w.TEAM_ISSUES)
        self.assertEqual(before,(h.repo/w.TEAM_ISSUES).read_bytes())
    def test_05_wrong_eight_file_native_result_cannot_fix_candidate(self):
        h=DeliveryHarness();self.addCleanup(h.close);a=h.producer;b=a['review_binding']
        output={'schema':'q3_control13_fixed_candidate_result.v1','report_base_commit':h.f.report_base,
          'execution_commit':h.f.head,'candidate_commit':h.f.commit,'candidate_manifest':b['candidate_manifest'][:-1],
          'delivery_prefix':b['delivery_prefix'],'author_ids':b['author_ids'],
          'verdict':'CANDIDATE_READY_FOR_INDEPENDENT_REVIEW','mathematical_acceptance':False}
        obs=h.native(a,output);before=(h.repo/w.TEAM_ISSUES).read_bytes()
        event=h.event('FIX_CANDIDATE',a['assignee'],'implementation',
          evidence=[{'locator':obs['output_locator'],'sha256':obs['output_sha256']}])
        with self.assertRaisesRegex(tr.TeamRecordError,'FIXED_CANDIDATE_NATIVE_OUTPUT_MISMATCH'):
            h.record('issue-event',event,w.TEAM_ISSUES)
        self.assertEqual(before,(h.repo/w.TEAM_ISSUES).read_bytes())
    def test_06_push_permit_cannot_be_reissued_or_false_cancelled(self):
        h=DeliveryHarness();self.addCleanup(h.close);h.accept_native_repair();oid=h.reserve_publication();paths=sorted(h.inputs)
        with w._execution_writer_epoch(h.repo,publication_operation=oid) as epoch:
            self.assertTrue(w.team_guard(h.repo,command='publication',paths=paths,publication_stage='prepare',writer_epoch=epoch)['execute_once'])
            git(h.repo,'add','--',*paths);git(h.repo,'commit','-qm','TEST commit before LOST push permit')
            self.assertTrue(w.team_guard(h.repo,command='publication',paths=paths,publication_stage='publish',writer_epoch=epoch)['execute_once'])
            self.assertFalse(w.team_guard(h.repo,command='publication',paths=paths,publication_stage='publish',writer_epoch=epoch)['execute_once'])
        before=h.f.current_local()
        record={'schema':'q3_team_effect_observation.v1','operation_id':oid,'outcome':'NOT_EXECUTED','evidence':h.inputs}
        fp=h.f.root/'TEST_NOT_EXECUTED.json';write(fp,w._team_json(record))
        with self.assertRaisesRegex(w.WorkflowRuntimeError,'UNKNOWN_IS_NOT_NOT_EXECUTED'):
            w.team_confirm_effect(h.repo,operation_id=oid,candidate=fp,expected_sha256=w._resume_digest(fp.read_bytes()))
        self.assertEqual(before,h.f.current_local())
        with self.assertRaises(w.WorkflowRuntimeError):w._team_pending_guard(h.repo)


class PrefixExactnessTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix='q3-prefix-exactness-');self.repo=Path(self.temp.name)
        git(self.repo,'init','-q','-b','rh_clean');git(self.repo,'config','user.name','TEST');git(self.repo,'config','user.email','test@example.invalid')
        write(self.repo/'base.txt',b'TEST base\n');git(self.repo,'add','.');git(self.repo,'commit','-qm','TEST O')
        self.O=git(self.repo,'rev-parse','HEAD')
    def tearDown(self):self.temp.cleanup()
    def head(self):
        for p in r.HISTORY_PATHS:write(self.repo/p,('TEST history '+p+'\n').encode())
        git(self.repo,'add','--',*r.HISTORY_PATHS);git(self.repo,'commit','-qm','TEST H')
        return git(self.repo,'rev-parse','HEAD')
    def test_01_exact_prefix_revalidated_and_mutated_final_blob_rejected(self):
        H=self.head()
        with patch.object(r,'BASE_HEAD',H),patch.object(r,'HISTORICAL_REMOTE',self.O):
            p=r.delivery_prefix_manifest(self.repo,remote_base=self.O,head=H)
            r.validate_delivery_prefix(self.repo,p)
            write(self.repo/r.HISTORY_PATHS[0],b'TEST rewritten committed history\n')
            git(self.repo,'add','--',r.HISTORY_PATHS[0]);git(self.repo,'commit','-qm','TEST forbidden history rewrite')
            with self.assertRaisesRegex(w.WorkflowRuntimeError,'CARRIED_HISTORY_REWRITTEN'):
                r.check_carried_history(self.repo,p,git(self.repo,'rev-parse','HEAD'))
    def test_02_transient_foreign_path_not_hidden_by_endpoint_diff(self):
        write(self.repo/'hidden.txt',b'TEST unreviewed intermediate bytes\n');git(self.repo,'add','.');git(self.repo,'commit','-qm','TEST hidden add')
        git(self.repo,'rm','-q','--','hidden.txt');git(self.repo,'commit','-qm','TEST hidden removal')
        H=self.head()
        with patch.object(r,'BASE_HEAD',H),patch.object(r,'HISTORICAL_REMOTE',self.O),self.assertRaisesRegex(w.WorkflowRuntimeError,'HISTORICAL_TRANSIENT_OUTSIDE_SCOPE'):
            r.delivery_prefix_manifest(self.repo,remote_base=self.O,head=H)
    def test_03_twentyfourth_path_cannot_expand_allowlist(self):
        H=self.head();write(self.repo/'extra.txt',b'TEST no blanket expansion\n');git(self.repo,'add','.');git(self.repo,'commit','-qm','TEST extra')
        H=git(self.repo,'rev-parse','HEAD')
        with patch.object(r,'BASE_HEAD',H),patch.object(r,'HISTORICAL_REMOTE',self.O),self.assertRaises(w.WorkflowRuntimeError):
            r.delivery_prefix_manifest(self.repo,remote_base=self.O,head=H)
    def test_04_wrong_declared_hash_cannot_validate(self):
        H=self.head()
        with patch.object(r,'BASE_HEAD',H),patch.object(r,'HISTORICAL_REMOTE',self.O):
            p=r.delivery_prefix_manifest(self.repo,remote_base=self.O,head=H)
            p['files'][r.HISTORY_PATHS[0]]['sha256']='0'*64
            with self.assertRaises(w.WorkflowRuntimeError):r.validate_delivery_prefix(self.repo,p)



    def test_05_no_unreviewed_post_h_commits_even_when_endpoint_tree_matches(self):
        H=self.head()
        with patch.object(r,'BASE_HEAD',H),patch.object(r,'HISTORICAL_REMOTE',self.O):
            prefix=r.delivery_prefix_manifest(self.repo,remote_base=self.O,head=H)
            git(self.repo,'commit','--allow-empty','-qm','TEST unreviewed extra parent after H')
            git(self.repo,'commit','--allow-empty','-qm','TEST same tree endpoint')
            with self.assertRaisesRegex(w.WorkflowRuntimeError,'DELIVERY_NOT_SINGLE_CHILD_OF_H'):
                r.check_carried_history(self.repo,prefix,git(self.repo,'rev-parse','HEAD'))


class StartupManifestContractTests(unittest.TestCase):
    """Run the REAL complete declared-surface validator, not just writer inventory."""
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix='q3-manifest-contract-');self.repo=Path(self.temp.name)
        self.channel={'schema':'q3_channel_runtime.v1','control_status':'ACTIVE','active_proshka_phase':None,
            'active_exploration':None,'last_exploration_close':None,
            'mathematical_authority_mode':'CODEX_PROSHKA_FULL_EXCEPT_PX_RH_CLAIM','px_rh_claim_state':'NOT_READY',
            'operational_action_pending':None,'meter':{name:0 for name in ('phases_opened','fresh_chats_opened',
                'delegated_strategic_review_calls','exploration_review_calls','px_rh_claim_requests',
                'ordinary_goal_close_calls','mathematical_owner_deferral_violations','fanout_violations','forced_rollovers')}}
        write(self.repo/sr.CHANNEL_RUNTIME_REL,w._team_json(self.channel))
        write(self.repo/w.TOOLS,(SOURCE/w.TOOLS).read_bytes())
    def tearDown(self):self.temp.cleanup()
    def validate(self):
        pairs=tuple((p,sr._path_fingerprint(self.repo,p)) for p in (sr.CHANNEL_RUNTIME_REL,sr.TOOL_MANIFEST_REL))
        return sr._validate_declared_startup_surfaces(self.repo,pairs)
    def test_01_all_new_registered_tools_pass_actual_full_schema(self):
        self.assertEqual(self.validate(),())
    def test_02_missing_audience_or_authority_is_rejected_by_same_validator(self):
        original=(self.repo/w.TOOLS).read_bytes()
        for field in ('audience','authority','approval','trigger','records_to','last_verified'):
            tools=yaml.safe_load(original)
            entry=next(t for group in tools['tool_families'].values() for t in group['tools'] if t['id']=='workflow-team-recovery-review')
            entry.pop(field,None);write(self.repo/w.TOOLS,yaml.safe_dump(tools,sort_keys=False).encode())
            self.assertIn('STARTUP_TOOL_MANIFEST_INVALID',self.validate())
        write(self.repo/w.TOOLS,original)

if __name__=='__main__':unittest.main()
