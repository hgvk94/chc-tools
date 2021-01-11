import z3 # type: ignore
import sys, os

def get_preds(exp):
    preds=[]
    if z3.is_app(exp) and z3.is_func_decl(exp.decl()) and exp.decl().kind() == z3.Z3_OP_UNINTERPRETED and exp.decl().range() == z3.BoolSort():
            preds.append(exp.decl().name())
    else:
        for c in exp.children():
            preds.extend(get_preds(c))
    return preds
class Preds():
    def __init__(self, fname):
        self._fp = z3.Fixedpoint()
        self._fp.parse_file(fname)
        self._preds = []
        assert(len(self._fp.get_rules()) == 0)
    def get_preds(self):
        for a in self._fp.get_assertions():
            assert(a.is_forall())
            preds=[]
            preds.extend(get_preds(a.body()))
            for p in preds:
                if not p in self._preds:
                    self._preds.append(p)

    def __repr__(self):
        s = ""
        for a in self._fp.get_assertions():
            s = s + str(a) + "\n"
        return s

def processDir (root):
    '''Recursively process all files in the root directory'''
    for root, dirs, files in os.walk(root):
        for name in files:
            processFile (os.path.join(root, name))

def processFile(fname):
    p = Preds(fname)
    p.get_preds()
    print(p._preds)

def main():
    processDir(sys.argv[1])
    return 0


if __name__ == '__main__':
    sys.exit(main())
