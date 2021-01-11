import pysmt
import sys

import functools
import collections

from pysmt.smtlib.parser import SmtLibZ3Parser, SmtLibCommand
from pysmt.exceptions import UnknownSmtLibCommandError, PysmtValueError, PysmtSyntaxError

class chcRFpredparser(SmtLibZ3Parser):
    def __init__(self, env=None, interactive=False):
        super().__init__(env, interactive)
        self.commands["declare-datatype"] = self._cmd_declare_datatype
        self.commands["declare-datatypes"] = self._cmd_declare_datatypes

        self.commands["set-logic"] = self._cmd_set_logic

    def _cmd_set_logic(self, current, tokens):
        elements = self.parse_atoms(tokens, current, 1)
        name = elements[0]
        return SmtLibCommand(current, [None])


    def parse_cnstr_args(self, current, tokens, params):
        cur = tokens.consume()
        if cur != '(':
            tokens.add_extra_token(cur)
            return None, None
        sel_name = tokens.consume()
        arg_type = self.parse_type(tokens, current, type_params = params)
        self.consume_closing(tokens, current)
        print("finished parsing args ", sel_name, arg_type)
        return sel_name, arg_type

    def parse_cnstr(self, current, tokens, params, type_):
        cur = tokens.consume()
        cst = []
        if cur == ')':
            # no constructor
            tokens.add_extra_token(')')
            return cst
        if cur != '(':
            #null-ary constructor
            cnstr_name = cur
            cnstr = self._get_var(cnstr_name, type_)
            self.cache.bind(cnstr_name, cnstr)
            cst.append(cnstr)
            return cst
        #constructor with arguments
        cnstr_name = tokens.consume()
        sel_names = []
        args = []
        while True:
            sel_name, arg_type = self.parse_cnstr_args(current, tokens, params)
            if sel_name == None:
                assert(arg_type == None)
                self.consume_closing(tokens, current)
                break
            sel_names.append(sel_name)
            args.append(arg_type)

        assert(len(args) > 0)
        cnstr_sort = self.env.type_manager.FunctionType(type_, args)
        cnstr = self._get_var(cnstr_name, cnstr_sort)
        cst.append(cnstr)
        assert(cnstr.symbol_type().is_function_type())
        self.cache.bind(cnstr_name, \
                    functools.partial(self._function_call_helper, cnstr))

        for i in range(len(sel_names)):
            sel_name = sel_names[i]
            arg_type = args[i]
            sel_sort = self.env.type_manager.FunctionType(arg_type, [type_])
            sel_fun = self._get_var(sel_name, sel_sort)
            self.cache.bind(sel_name, \
                    functools.partial(self._function_call_helper, sel_fun))

            # testor = create_testor(sel_name, type_, arg_type)
            cst.append(sel_fun)
            # tests.append(testor)
        print("finished parsing cnstr ", cst)
        return cst

    def parse_dt_cnstrs(self, current, tokens, typename):
        self.consume_opening(tokens, current)
        cur = tokens.consume()
        params = []
        if str(cur) == "par":
            tokens.consume()
            cur = tokens.consume()
            while cur != ')':
                p_type = self.env.type_manager.Type(cur, 0)
                self.cache.bind(cur, p_type)
                params.append(p_type)
                cur = tokens.consume()
            cur = tokens.consume()
        assert (cur == '(')
        type_ = self.env.type_manager.Type(typename, len(params))
        self.cache.bind(typename, type_)
        type_inst = self.env.type_manager.get_type_instance(type_, *params)
        types = [type_inst]
        while True:
           #treating params as types instead of type parameters
           cst = self.parse_cnstr(current, tokens, [], type_inst)
           if not cst:
               self.consume_closing(tokens, current)
               break;
           types.extend(cst)
        print("finished cnstrs")
        self.consume_closing(tokens, current)
        return types

    def _cmd_declare_datatype(self, current, tokens):
        typename = self.parse_atom(tokens, current)
        type_ = self.parse_dt_cnstrs(current, tokens, typename)
        return SmtLibCommand(current, type_)

    def _cmd_declare_datatypes(self, current, tokens):
        self.consume_opening(tokens, current)
        cur = tokens.consume()
        types = []
        while cur != ')':
            type_name = self.parse_atom(tokens, current)
            arity = self.parse_atom(tokens, current)
            types.append(type_name)
            self.consume_closing(tokens, current)
            cur = tokens.consume()
        self.consume_opening(tokens, current)
        dt = []
        for t in types:
            elements = self.parse_dt_cnstrs(current, tokens, t)
            dt.extend(elements)
        self.consume_closing(tokens, current)
        self.consume_closing(tokens, current)
        print("finished datatypes")
        print(dt)
        return SmtLibCommand(current, dt)

    def _cmd_declare_rel(self, current, tokens):
        """(declare-rel <symbol> (<sort>*))"""
        rel = self.parse_atom(tokens, current)
        args_sort = self.parse_params(tokens, current)
        self.consume_closing(tokens, current)

        fn_sort = self.env.type_manager.BOOL()

        if args_sort:
            fn_sort = self.env.type_manager.FunctionType(fn_sort, args_sort)

        fn = self._get_var(rel, fn_sort)
        if fn.symbol_type().is_function_type():
            self.cache.bind(rel, \
                            functools.partial(self._function_call_helper, fn))
        else:
            self.cache.bind(rel, fn)
        return SmtLibCommand(current, [fn])

    def parse_preds(self, script):
        s = self.get_script_fname(script)
        decls = s.filter_by_command_name("declare-rel")
        for cmd in decls:
            print(cmd)

def main():
    parser = chcRFpredparser()
    try:
        p = parser.parse_preds(sys.argv[1])
        print(p)
    except PysmtSyntaxError as e:
        print(e)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
