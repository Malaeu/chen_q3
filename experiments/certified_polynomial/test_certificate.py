import copy
import unittest
from constructor import build_report
from verify_certificate import verify


class ReplayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report = build_report()

    def test_accept(self):
        self.assertEqual(verify(self.report)['status'], 'PASS')

    def test_tampering_rejected(self):
        paths = [
            (('contract','domain'), ['0','1']),
            (('candidate','coefficients','c'), '13/50'),
            (('bad_candidate','verification','counterexample','x'), '0'),
            (('families',0,'certificate','uniform_x'), '2'),
            (('families',0,'lower'), '1/5'),
            (('families',1,'certificate','objective_lower_bound'), '2'),
            (('families',1,'upper'), '1/4'),
        ]
        for path, value in paths:
            with self.subTest(path=path):
                report = copy.deepcopy(self.report)
                node = report
                for key in path[:-1]:
                    node = node[key]
                node[path[-1]] = value
                with self.assertRaises(ValueError):
                    verify(report)


if __name__ == '__main__':
    unittest.main()
