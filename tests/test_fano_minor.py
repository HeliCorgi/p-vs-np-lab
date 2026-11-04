import copy
import json
from pathlib import Path
import unittest

from pnp_lab.fano_minor import quotient_binary_groups, verify_fano_minor
from pnp_lab.ternary_support import three_cnf_to_weight_two_supports


class FanoMinorTests(unittest.TestCase):
    def setUp(self):
        self.cert=json.loads((Path(__file__).resolve().parents[1]/'examples/graphic_fano_minor.json').read_text())
        self.gs=three_cnf_to_weight_two_supports(self.cert['source_variables'],self.cert['source_cnf']).supports

    def test_fixture_and_binary_quotient(self):
        self.assertEqual(verify_fano_minor(self.gs,self.cert)['quotient_coordinates'],list(range(1,8)))
        pr,meta=quotient_binary_groups(self.gs)
        self.assertEqual(meta,{'binary_groups':9,'contracted_rank':9,'fixed_point':True})
        c=dict(self.cert,contract=self.cert['contract'][9:],expected_contracted_rank=10)
        self.assertEqual(verify_fano_minor(pr,c)['minor_rank'],3)

    def test_forged_certificate_and_graphic_relation_rejected(self):
        for edit in (lambda c:c['keep'].__setitem__(2,c['keep'][0]),
                     lambda c:c['keep'].__setitem__(3,[20,0,2]),
                     lambda c:c['contract'].append(c['contract'][0]),
                     lambda c:c['contract'][0].__setitem__(0,-1),
                     lambda c:c['expected_quotient_coordinates'].__setitem__(6,5)):
            bad=copy.deepcopy(self.cert);edit(bad)
            with self.assertRaises(ValueError):verify_fano_minor(self.gs,bad)
        with self.assertRaises(ValueError):
            verify_fano_minor([(0,x) for x in [1,2,3,4,5,6,8]],{'contract':[],'keep':[[i,0,1] for i in range(7)]})
