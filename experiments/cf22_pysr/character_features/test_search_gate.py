import copy,gzip,json,tempfile,unittest
from pathlib import Path
import search


class SearchGateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data=json.loads(gzip.decompress((Path(__file__).parent/'dataset.json.gz').read_bytes()))

    def reject(self,data):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp);(p/'data.json').write_text(json.dumps(data))
            with self.assertRaises(ValueError):search.run(p/'data.json',p/'run')
            self.assertFalse((p/'run').exists())

    def test_bad_split_rejected_before_any_fit(self):
        data=dict(self.data);data['rows']=list(data['rows']);data['rows'][0]=dict(data['rows'][0]);data['rows'][0]['split']='omit'
        self.reject(data)

    def test_numeric_collision_rejected_before_any_fit(self):
        data=dict(self.data);data['rows']=list(data['rows']);data['rows'][1]=dict(data['rows'][1]);
        data['rows'][1]['features']=data['rows'][0]['features'];data['rows'][1]['feature_intervals']=data['rows'][0]['feature_intervals'];data['rows'][1]['target']={'lower':'999','upper':'1000'}
        self.reject(data)


if __name__=='__main__':unittest.main()
