import z3 # type: ignore
import sys, os
#'append', 'incsome', '%some', '%size', '%append',  'some-rest',  'inc&back',  '%take_some_rest', 'sum', 'prod', 'some', '%inc', '%take_some', 'inck', '%sum',  'back', 'pushback', 'inc'

#The list of predicates that define length in the benchmarks
LENGTH_PREDS = ['%length', 'length']
SUM_PREDS = ['%sum', 'sum']
SIZE_PREDS = ['%size']
PROD_PREDS = ['prod']

def is_recursive_adt(dt):
    if not dt.kind() == z3.Z3_DATATYPE_SORT:
        return False
    n = dt.num_constructors()
    for i in range(n):
        c = dt.constructor(i)
        num_args = c.arity()
        for j in range(num_args):
            arg_sort = c.domain(j)
            if arg_sort == dt:
                return True
    return False
#from horndb
def ground_quantifier(qexpr):
    body = qexpr.body()

    var_list = list()
    for i in reversed(range(qexpr.num_vars())):
        vi_name = qexpr.var_name(i)
        vi_sort = qexpr.var_sort(i)
        vi = z3.Const(vi_name, vi_sort)
        var_list.append(vi)

    body = z3.substitute_vars(body, *var_list)
    return body, var_list


def get_preds(exp, ctx):
    preds=[]
    if z3.is_app(exp) and exp.decl().kind() == z3.Z3_OP_UNINTERPRETED and exp.decl().range() == z3.BoolSort(ctx):
            preds.append(exp.decl())
    else:
        for c in exp.children():
            preds.extend(get_preds(c, ctx))
    return preds

def get_adts(exp, ctx):
    adts = []
    if not z3.is_app(exp):
        return adts
    if exp.sort_kind() == z3.Z3_DATATYPE_SORT:
        adts.append(exp.sort())
    else:
        for c in exp.children():
            adts.extend(get_adts(c, ctx))
    return adts

def contains_func_app(exp, func):
    if not z3.is_app(exp):
        return False
    if exp.decl() == func:
        return True
    for f in exp.children():
        if contains_func_app(f, func):
            return True
    return False

def get_tree_csr(tree_sort):
    assert(tree_sort.num_constructors() == 2)
    if tree_sort.constructor(0).arity() == 0:
        nil_cons = tree_sort.constructor(0)
        ins_cons = tree_sort.constructor(1)
        i = 1
    else:
        ins_cons = tree_sort.constructor(0)
        nil_cons = tree_sort.constructor(1)
        i = 0
    assert(nil_cons.arity() == 0)
    assert(ins_cons.arity() == 3)
    if not ins_cons.domain(0) == tree_sort:
        lc_sel = tree_sort.accessor(i, 1)
        rc_sel = tree_sort.accessor(i, 2)
        val_sel = tree_sort.accessor(i, 0)
    elif not ins_cons.domain(1) == tree_sort:
        lc_sel = tree_sort.accessor(i, 0)
        rc_sel = tree_sort.accessor(i, 2)
        val_sel = tree_sort.accessor(i, 1)
    else:
        lc_sel = tree_sort.accessor(i, 0)
        rc_sel = tree_sort.accessor(i, 1)
        val_sel = tree_sort.accessor(i, 2)
    return nil_cons, lc_sel, rc_sel, val_sel

def get_list_csr(list_sort):
    assert(list_sort.num_constructors() == 2)
    if list_sort.constructor(0).arity() == 0:
        nil_cons = list_sort.constructor(0)
        ins_cons = list_sort.constructor(1)
        i = 1
    else:
        ins_cons = list_sort.constructor(0)
        nil_cons = list_sort.constructor(1)
        i = 0
    assert(nil_cons.arity() == 0)
    assert(ins_cons.arity() == 2)
    if ins_cons.domain(1) == list_sort:
        tail_sel = list_sort.accessor(i, 1)
        head_sel = list_sort.accessor(i, 0)
    else:
        tail_sel = list_sort.accessor(i, 0)
        head_sel = list_sort.accessor(i, 1)
    return nil_cons, head_sel, tail_sel

def create_length_rf(list_sort, ret_sort, ctx):
    length = z3.RecFunction('length', list_sort, ret_sort)
    x = z3.Const('x', list_sort)
    nil_cons, head_sel, tail_sel = get_list_csr(list_sort)
    z3.RecAddDefinition(length, x, z3.If(x == nil_cons(), 0, 1 + length(tail_sel(x)), ctx=ctx))
    return length

def create_prod_rf(list_sort, ret_sort, ctx):
    prod = z3.RecFunction('prod', list_sort, ret_sort)
    x = z3.Const('x', list_sort)
    nil_cons, head_sel, tail_sel = get_list_csr(list_sort)
    z3.RecAddDefinition(prod, x, z3.If(x == nil_cons(), 0, head_sel(x) * prod(tail_sel(x)), ctx=ctx))
    return prod

def create_sum_rf(sort, ret_sort, ctx):
    if "list" in sort.name().lower():
        return create_sum_list_rf(sort, ret_sort, ctx)
    elif "tree" in sort.name().lower():
        return create_sum_tree_rf(sort, ret_sort, ctx)
    else:
        assert(False)

def create_size_rf(tree_sort, ret_sort, ctx):
    size = z3.RecFunction('size', tree_sort, ret_sort)
    x = z3.Const('x', tree_sort)
    nil_cons, lc_sel, rc_sel, val_sel = get_tree_csr(tree_sort)
    assert(val_sel.range() == ret_sort)
    z3.RecAddDefinition(size, x, z3.If(x == nil_cons(), 0, 1 + size(lc_sel(x)) + size(rc_sel(x)), ctx=ctx))
    return size


def create_sum_tree_rf(tree_sort, ret_sort, ctx):
    sum = z3.RecFunction('sum', tree_sort, ret_sort)
    x = z3.Const('x', tree_sort)
    nil_cons, lc_sel, rc_sel, val_sel = get_tree_csr(tree_sort)
    z3.RecAddDefinition(sum, x, z3.If(x == nil_cons(), 0, val_sel(x) + sum(lc_sel(x)) + sum(rc_sel(x)), ctx=ctx))
    return sum

def create_sum_list_rf(list_sort, ret_sort, ctx):
    sum = z3.RecFunction('sum', list_sort, ret_sort)
    x = z3.Const('x', list_sort)
    nil_cons, head_sel, tail_sel = get_list_csr(list_sort)
    z3.RecAddDefinition(sum, x, z3.If(x == nil_cons(), 0, head_sel(x) + sum(tail_sel(x)), ctx=ctx))
    return sum

#An rf tuple contains a rf, the list of predicates that define it, and a function that creates the z3 rf
class rf_tuple():
    def __init__(self, name, PREDS, create_rf):
        self._name = name
        self._PREDS = PREDS
        self._create_rf = create_rf
        self._z3_fun_def = None

    def has_z3_fun_def(self):
        return not self._z3_fun_def is None
    def set_z3_fun_def(self, fun_def):
        self._z3_fun_def = fun_def

LENGTH_RF = rf_tuple('length', LENGTH_PREDS, create_length_rf)
SUM_RF = rf_tuple('sum', SUM_PREDS, create_sum_rf)
SIZE_RF = rf_tuple('size', SIZE_PREDS, create_size_rf)
PROD_RF = rf_tuple('prod', PROD_PREDS, create_prod_rf)

class Preds():
    def __init__(self, fname):
        ## TODO: figure out which context to use
        self._ctx = z3.Context()
        self._fp = z3.Fixedpoint(ctx=self._ctx)
        self._fp.parse_file(fname)
        self._preds = []
        self._adts = []
        self._rf_preds = []
        self._length_fun = None
        self._sum_fun = None
        self._assertions = self._fp.get_assertions()
        self._rf_tuples = [LENGTH_RF, SUM_RF, SIZE_RF, PROD_RF]
        assert(len(self._fp.get_rules()) == 0)

    def conjoin_all_rf(self):
        self.populate_rf_preds()
        for f in self._rf_tuples:
            res = self.add_rf(f._PREDS, f._create_rf)
            if not res is None:
                self.conjoin_rf(res, f._PREDS)

    def add_rf(self, RF_PREDS, create_rf):
        for pred in self._preds:
            if pred.name() in RF_PREDS:
                assert(pred.arity() == 2)
                if pred.domain(0).kind() == z3.Z3_DATATYPE_SORT:
                    adt_sort = pred.domain(0)
                    ret_sort = pred.domain(1)
                else:
                    adt_sort = pred.domain(1)
                    ret_sort = pred.domain(0)
                assert(adt_sort.kind() == z3.Z3_DATATYPE_SORT)
                return create_rf(adt_sort, ret_sort, self._ctx)
        return None

    #Let p(a, b) be a predicate in RF_PREDS.
    #This method will conjoin each occurrence of p(a, b) with rf_def(a) = b
    def conjoin_rf(self, rf_def, RF_PREDS):
        new_assertions = []
        for a in self._assertions:
            clause, vs = ground_quantifier(a)
            #If the clause does not have a tail, it cannot be a RF
            if not z3.is_implies(clause):
                new_assertions.append(a)
                continue
            head = clause.arg(1)
            tail = clause.arg(0)
            #Skip clauses whose head is RF
            if z3.is_app(head) and head.decl().name() in RF_PREDS:
                new_assertions.append(a)
                continue
            new_literals = []
            if z3.is_and(tail):
                for c in tail.children():
                    if z3.is_app(c) and c.decl().name() in RF_PREDS:
                        assert(len(c.children()) == 2)
                        assert(c.arg(0).sort() == rf_def.domain(0))
                        rf_app = rf_def(c.arg(0))
                        eq = rf_app == c.arg(1)
                        new_literals.append(eq)
                    else:
                        #only top level applications of rf
                        assert(not contains_func_app(c, rf_def))
            elif z3.is_app(tail) and tail.decl().name() in RF_PREDS:
                assert(len(tail.children()) == 2)
                assert(tail.arg(0).sort() == rf_def.domain(0))
                rf_app = rf_def(tail.arg(0))
                eq = rf_app == tail.arg(1)
                new_literals.append(eq)

            if new_literals:
                new_tail = z3.And(*new_literals, tail)
                new_clause = z3.Implies(new_tail, head)
                new_assertion = z3.ForAll(vs, new_clause)
                new_assertions.append(new_assertion)
            else:
                new_assertions.append(a)
        self._assertions = new_assertions

    def bench_str(self):
        import io

        out = io.StringIO()
        new_fp = z3.Fixedpoint(ctx = self._ctx)
        for f in self._assertions:
            new_fp.add(f)
        out.write("(set-logic HORN)\n")
        out.write(str(new_fp))
        out.write("(check-sat)")
        return out.getvalue()

    #fetch all clauses of the form p1(args1) ==> p2(args2) where set(args2) = set(args1)
    def get_redundant_clauses(self):
        strange_clauses = []
        for a in self._assertions:
            assert(a.is_forall)
            body = a.body()
            if (z3.is_implies(body)):
                head = body.arg(1)
                tail = body.arg(0)
                if z3.is_and(tail) and tail.num_args() == 1:
                    tail = tail.arg(0)
                if z3.is_app(head) and z3.is_app(tail) and set(tail.children()) == set(head.children()):
                    strange_clauses.append((head.decl().name(), tail.decl().name()))
        return strange_clauses

    #populate _preds with all the predicates in the CHC
    def populate_preds(self):
        #don't populate if already present
        if self._preds:
            return
        for a in self._assertions:
            assert(a.is_forall())
            self._preds.extend(get_preds(a.body(), self._ctx))
        #remove duplicates
        self._preds = list(dict.fromkeys(self._preds))

    #populate _rf_preds with all _preds that define a catamorphism
    def populate_rf_preds(self):
        if self._rf_preds:
            return
        self.populate_preds()
        redundant_clauses = self.get_redundant_clauses()
        # collect all predicates that have recursive clauses of their own
        for pred in self._preds:
            for a in self._assertions:
                assert(a.is_forall())
                body = a.body()
                if (z3.is_implies(body)):
                    head = body.arg(1)
                    tail = body.arg(0)
                    if z3.is_app(head) and head.decl().name() == pred.name() and head.decl().arity() == 2:
                        arg1 = head.arg(0).sort()
                        arg2 = head.arg(1).sort()
                        if not (is_recursive_adt(arg1) or is_recursive_adt(arg2)):
                            continue
                        tail_preds = list(dict.fromkeys(get_preds(tail, self._ctx)))
                        if len(tail_preds) == 1:
                            if tail_preds[0] == pred:
                                self._rf_preds.append(pred)
                            else:
                                for (h, b) in redundant_clauses:
                                    if b == pred.name() and h == tail_preds[0].name():
                                        self._rf_preds.append(h)

    #populate _adts with all the adts in the CHC
    def populate_adts(self):
        #don't populate if already present
        if self._adts:
            return
        for a in self._assertions:
            self._adts.extend(get_adts(a.body(), self._ctx))
        self._adts = list(dict.fromkeys(self._adts))

    #get all the constructors of all the adts in _adts
    def get_adt_cons(self, res):
        self.populate_adts()
        for a in self._adts:
            adt = [a]
            n = a.num_constructors()
            for i in range(n):
                adt.append(a.constructor(i))
            adt_s = str(adt)
            if adt_s not in res:
                res.add(adt_s)

def processDir (root):
    '''Recursively process all files in the root directory'''
    os.mkdir("bench")
    for root, dirs, files in os.walk(root):
        for name in files:
            _, folder_name = os.path.split(root)
            bench_name = folder_name + "-" +name
            out_file = open("bench/"+bench_name, 'w+')
            processFile(os.path.join(root, name), out_file)

def processFile(fname, out_file = sys.stdout):
    p = Preds(fname)
    p.conjoin_all_rf()
    out_file.write(p.bench_str())

def main():
    arg = sys.argv[1]
    if os.path.isfile(arg):
        path, fname = os.path.split(arg)
        _, foldername = os.path.split(path)
        new_fname = foldername + "-" + fname
        f = open(new_fname, 'w+')
        processFile(arg, out_file=f)
    else:
        processDir(arg)
    return 0


if __name__ == '__main__':
    sys.exit(main())
