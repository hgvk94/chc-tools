import z3 # type: ignore
import sys, os
#'append', 'incsome', '%some', '%size', '%append',  'some-rest',  'inc&back',  '%take_some_rest', 'sum', 'prod', 'some', '%inc', '%take_some', 'inck', '%sum',  'back', 'pushback', 'inc'


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

REC_FUNS = ["length", "prod", "size", "sum"]
#TODO: figure out how to do this automatically
def get_rfs(exp, ctx):
    rfs=[]
    if z3.is_quantifier(exp):
        rfs.extend(get_rfs(exp.body(), ctx))
    if z3.is_app(exp) and exp.decl().name() in REC_FUNS and exp.decl().range() != z3.BoolSort(ctx):
            rfs.append(exp.decl())
    else:
        for c in exp.children():
            rfs.extend(get_rfs(c, ctx))
    return rfs

def contains_func_app(exp, func):
    if not z3.is_app(exp):
        return False
    if exp.decl() == func:
        return True
    for f in exp.children():
        if contains_func_app(f, func):
            return True
    return False

#Check whether any of the unary rf in \p rfs can take as input
#one of the arguments of p
def contains_rf_arg(p, rfs, ctx):
    for i in range(p.arity()):
        d = p.domain(i)
        for rf in rfs:
            if rf.domain(0) == d:
                return True
    return False

#Matches a predicate with a new abstract predicate
#contains all the literals required for term abstraction
class abs_pred():
    def __init__(self, pred, rfs, ctx):
        self._ctx = ctx
        self._pred = pred
        self._abstractions = []
        self._original_args = []
        for i in range(pred.arity()):
            self._original_args.append(pred.domain(i))
        for (i, f) in enumerate(self._original_args):
            if f.kind() == z3.Z3_DATATYPE_SORT:
                for rf in rfs:
                    if rf.domain(0) == f:
                        self._abstractions.append((rf, i))
        domain = []
        domain.extend(self._original_args)
        domain.extend([f.range() for (f, _) in self._abstractions])
        self._new_pred = z3.Function(pred.name() + "-abs", *domain, z3.BoolSort(self._ctx))

    def get_sorts(self):
        return [f.range() for (f, _) in self._abstractions]

    def mk_new_pred(self, args, new_vars):
        assert(len(new_vars) == len(self._abstractions))
        new_args = [*args, *new_vars]
        return self._new_pred(*new_args)

    def mk_body(self, args, new_vars):
        assert(len(args) == len(self._original_args))
        assert(len(new_vars) == len(self._abstractions))
        body = []
        for (j, (f, i)) in enumerate(self._abstractions):
            lhs = f(args[i])
            rhs = new_vars[j]
            eq = lhs == rhs
            body.append(eq)
        return body


class Term_abs():
    def __init__(self, fname):
        self._ctx = z3.Context()
        self._fp = z3.Fixedpoint(ctx=self._ctx)
        self._fp.parse_file(fname)
        self._preds = []
        self._new_preds = []
        self._adts = []
        self._rf_preds = []
        self._assertions = self._fp.get_assertions()
        self._rfs = []
        for a in self._assertions:
            self._rfs.extend(get_rfs(a, self._ctx))
        self._rfs = list(dict.fromkeys(self._rfs))
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
                    strange_clauses.append((head.decl(), tail.decl()))
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
        self._rf_preds.extend([f for (_, f) in redundant_clauses])
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
                                    if b == pred and h == tail_preds[0]:
                                        self._rf_preds.append(h)

    def get_new_pred_for(self, pred):
        for p in self._new_preds:
            if p._pred == pred:
                return p
        return None

    def should_create_new_pred(self, p):
        if p in self._rf_preds:
            return False
        if not contains_rf_arg(p, self._rfs, self._ctx):
            return False
        return True
    def populate_new_preds(self):
        for p in self._preds:
            if self.should_create_new_pred(p):
                new_pred = abs_pred(p, self._rfs, self._ctx)
                self._new_preds.append(new_pred)

    def do_term_abs(self):
        self.populate_rf_preds()
        self.populate_new_preds()
        new_assertions = []
        for a in self._assertions:
            qbody, vs = ground_quantifier(a)
            if not z3.is_implies(qbody):
                assert(z3.is_app(qbody))
                new_pred =  self.get_new_pred_for(qbody.decl())
                new_vars = []
                if new_pred:
                    new_var_sorts = new_pred.get_sorts()
                    for f in new_var_sorts:
                        new_var = z3.FreshConst(f)
                        new_vars.append(new_var)
                    new_qbody = new_pred.mk_new_pred(qbody.args, new_vars)
                    literals = new_pred.mk_body(qbody.args, new_vars)
                    if literals:
                        new_assertion = z3.ForAll([vs, new_vars], z3.And(*literals, new_qbody))
                        new_assertions.append(new_assertion)
                    else:
                        new_assertions.append(a)
                else:
                    new_assertions.append(a)
            else:
                tail = qbody.arg(0)
                head = qbody.arg(1)
                new_vars = []
                extra_lits = []
                tail_preds = []
                #process head
                new_head = self.get_new_pred_for(head.decl())
                if new_head:
                    new_var_sorts = new_head.get_sorts()
                    for f in new_var_sorts:
                        new_var = z3.FreshConst(f)
                        new_vars.append(new_var)
                    new_head_abs = new_head.mk_new_pred(head.children(), new_vars)
                    extra_lits.extend(new_head.mk_body(head.children(), new_vars))
                tail_children = []
                if not z3.is_and(tail):
                    tail_children.append(tail)
                else:
                    tail_children.extend(tail.children())
                interp_tail = []
                for c in tail_children:
                    if z3.is_app(c) and c.decl().kind() == z3.Z3_OP_UNINTERPRETED and c.decl().range() == z3.BoolSort(self._ctx):
                        new_c = self.get_new_pred_for(c.decl())
                        if new_c:
                            vars = []
                            new_var_sorts = new_c.get_sorts()
                            for f in new_var_sorts:
                                new_var = z3.FreshConst(f)
                                vars.append(new_var)
                            new_c_abs = new_c.mk_new_pred(c.children(), vars)
                            new_vars.extend(vars)
                            extra_lits.extend(new_c.mk_body(c.children(), vars))
                            tail_preds.append(new_c_abs)
                        else:
                            tail_preds.append(c)
                    else:
                        interp_tail.append(c)

                if extra_lits:
                    new_tail = z3.And(*extra_lits, *tail_preds, *interp_tail)
                    if new_head:
                        h = new_head_abs
                    else:
                        h = head
                    chc = z3.Implies(new_tail, h)
                    new_assertion = z3.ForAll([*vs, *new_vars], chc)
                    new_assertions.append(new_assertion)
                else:
                    new_assertions.append(a)
        assert(len(self._assertions) == len(new_assertions))
        temp_preds = []
        for f in new_assertions:
            temp_preds.extend(get_preds(f, self._ctx))
        temp_preds = list(dict.fromkeys(temp_preds))
        assert(len(temp_preds) == len(self._preds))
        self._assertions = new_assertions


def processDir (root):
    '''Recursively process all files in the root directory'''
    os.mkdir("termabs")
    for root, dirs, files in os.walk(root):
        for name in files:
            if not name.endswith(".smt2"):
                continue
            _, folder_name = os.path.split(root)
            bench_name = folder_name + "-" +name
            out_file = open("termabs/"+bench_name, 'w+')
            processFile(os.path.join(root, name), out_file)

def processFile(fname, out_file = sys.stdout):
    print("processing " + fname)
    p = Term_abs(fname)
    p.do_term_abs()
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
