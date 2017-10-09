#! /usr/bin/env python3
'''2017CAD PA1 - Reduction of Ordered Binary Decision Diagram (ROBDD)
'''

import sys
import logging
from collections import defaultdict

logging.basicConfig(level=logging.INFO)
# logging.basicConfig(level=logging.DEBUG)

class Vertex:
    '''Vertex in ROBDD.
    '''
    def __init__(self, var, ite_expr, lo=None, hi=None):
        self.var = var # say, symbol in AIG
        self.high_v = hi # right child
        self.low_v = lo # left child
        self.ite_expr = ite_expr

class ROBDD:
    '''A ROBDD to represent the Boolean functions of input1 and input2.
    '''
    def __init__(self, argv):
        self.input1 = argv[0]
        self.input2 = argv[1]
        self.input3 = argv[2]
        self.output = argv[3]
        self.vertices = []
        self.uni_tbl = {} # (var, low_v, high_v) -> vertex
        self.static_low = None
        self.static_high = None
        self.init_static_vertex() # initialize s0 (low) and s1 (high) for ROBDD
        self.g_vtx = None # output of input1
        self.h_vtx = None # output of input2
        self.q_vtx = None # output of input3

    def init_static_vertex(self):
        '''Create 0 and 1 vertices.
        '''
        self.static_high = Vertex('~', '1')
        self.static_low = Vertex('~', '0')
        self.vertices.append(self.static_high)
        self.vertices.append(self.static_low)

    def run(self):
        '''1. Read in AIGs from <input1> and <input2>
        2. Construct ROBDD based on the AIGs
        3. Read in Boolean function of 'g' and 'h' in <input3>
        4. Represent this Boolean function using ITE and ROBDD
        5. Dump in ITE format to <output>
        '''
        self.g_vtx = self.build_from_aig(self.input1)
        self.h_vtx = self.build_from_aig(self.input2)
        print("Input1: {}".format(self.g_vtx.ite_expr))
        print("Input2: {}".format(self.h_vtx.ite_expr))
        self.q_vtx = self.build_from_bool_func(self.input3)
        print("Input3: {}".format(self.q_vtx.ite_expr))
        self.dump()

    def build_from_aig(self, aig_file):
        '''Build ROBDD described in a specified aig file.
        '''
        literal_to_vtx = {}
        uncreated_literals = defaultdict(list)
        input_literals = []
        output_literal = None

        with open(aig_file, 'r') as f:
            print('Parsing {}'.format(aig_file))
            header = f.readline()
            cnts = (int(cnt) for cnt in header.split()[1:])
            (max_var_cnt, in_cnt, latch_cnt, out_cnt, and_cnt) = cnts
            if latch_cnt != 0:
                raise NotImplementedError('Expected latch number: 0, got {}'.format(latch_cnt))
            # get input literals
            for _ in range(in_cnt):
                literal = f.readline().split()[0]
                input_literals.append(literal)
                # print(literal)
            # get output literals
            for _ in range(out_cnt):
                literal = f.readline().split()[0]
                output_literal = literal
                # print(literal)
            # skip the and lines at the first parsing
            for _ in range(and_cnt):
                f.readline()
            # parse symbols of input and output
            for _ in range(in_cnt + out_cnt):
                type_, var = f.readline().split()[0:2]
                pos = int(type_[1:])
                literal = input_literals[pos]
                # meet output or latch symbol, next loop
                if type_.startswith('o') or type_.startswith('l'):
                    continue
                elif ((var, self.static_low, self.static_high) not in self.uni_tbl and
                      type_.startswith('i')):
                    input_vtx = self.add_input_vtx(var)
                    logging.debug('    Create new input vertex: {} ({})'.format(input_vtx.var, literal))
                    assert input_vtx == self.uni_tbl[(var, self.static_low, self.static_high)], 'Error in setting input vertex'
                input_vtx = self.uni_tbl[(var, self.static_low, self.static_high)]
                literal_to_vtx[literal] = input_vtx
                # create inverted inputs e.g. literal 3, 5, 7...
                inv_input_vtx = self.add_inv_vtx(input_vtx)
                literal_to_vtx[str(int(literal)+1)] = inv_input_vtx
                logging.debug('    Set neg input vertex: {} ({})'.format(inv_input_vtx.var, str(int(literal)+1)))

            # second parsing, skip input and output lines and parse only AND lines
            f.seek(0)
            for _ in range(in_cnt+out_cnt+1):
                f.readline() # header, input or output lines
            # parse AND lines
            for _ in range(and_cnt):
                out_literal, in_literal1, in_literal2 = f.readline().split()[0:3]
                logging.debug('{} {} {}'.format(out_literal, in_literal1, in_literal2))
                if in_literal1 in literal_to_vtx and in_literal2 in literal_to_vtx:
                    logging.debug('    In2 {}'.format(literal_to_vtx[in_literal2].ite_expr))
                    logging.debug('    In1 {}'.format(literal_to_vtx[in_literal1].ite_expr))
                    # AND
                    vtx = self.ite(literal_to_vtx[in_literal1],
                                   literal_to_vtx[in_literal2], self.static_low, 'a')
                    # NOT
                    inv_vtx = self.add_inv_vtx(vtx)

                    and_out_literal = out_literal if int(out_literal) % 2 == 0 else str(int(out_literal)-1)
                    inv_out_literal = out_literal if int(out_literal) % 2 == 1 else str(int(out_literal)+1)

                    literal_to_vtx[and_out_literal] = vtx
                    literal_to_vtx[inv_out_literal] = inv_vtx
                    logging.debug('    Set vertex: {} ({})'.format(vtx.ite_expr, and_out_literal))
                    logging.debug('    Set vertex: {} ({})'.format(inv_vtx.ite_expr, inv_out_literal))

                    if and_out_literal in uncreated_literals:
                        for (out_l, in_l1, in_l2) in uncreated_literals[and_out_literal]:
                            logging.debug('        To handle literal: {}'.format(out_l))
                            if (in_l1 not in literal_to_vtx) or (in_l2 not in literal_to_vtx):
                                continue
                            # AND
                            vtx = self.ite(literal_to_vtx[in_l1],
                                           literal_to_vtx[in_l2], self.static_low, 'a')
                            # INV
                            inv = self.add_inv_vtx(vtx)
                            literal_to_vtx[out_l] = vtx
                            literal_to_vtx[str(int(out_l)+1)] = inv
                            logging.debug('        Set vertex: {} ({})'.format(vtx.ite_expr, out_l))
                            logging.debug('        Set vertex: {} ({})'.format(inv.ite_expr, str(int(out_l)+1)))
                    if inv_out_literal in uncreated_literals:
                        for (out_l, in_l1, in_l2) in uncreated_literals[inv_out_literal]:
                            logging.debug('        To handle unset literal: {}'.format(out_l))
                            if (in_l1 not in literal_to_vtx) or (in_l2 not in literal_to_vtx):
                                continue
                            # AND
                            vtx = self.ite(literal_to_vtx[in_l1],
                                           literal_to_vtx[in_l2], self.static_low, 'a')
                            # INV
                            inv = self.add_inv_vtx(vtx)
                            literal_to_vtx[out_l] = vtx
                            literal_to_vtx[str(int(out_l)+1)] = inv
                            logging.debug('        Set vertex: {} ({})'.format(vtx.ite_expr, out_l))
                            logging.debug('        Set vertex: {} ({})'.format(inv.ite_expr, str(int(out_l)+1)))
                else:
                    # consider that input literals may not be set and added to "literal_to_vtx" yet
                    # append input literals into "uncreated_literals" for further handling
                    and_out_literal = out_literal if int(out_literal) % 2 == 0 else str(int(out_literal)-1)
                    # record only the even litteral output
                    if in_literal1 not in literal_to_vtx:
                        uncreated_literals[in_literal1].append((and_out_literal, in_literal1, in_literal2))
                    if in_literal2 not in literal_to_vtx:
                        uncreated_literals[in_literal2].append((and_out_literal, in_literal1, in_literal2))
            return literal_to_vtx[output_literal]

    def add_input_vtx(self, var):
        '''Add input vertex if not created.
        '''
        new_input_vtx = Vertex(var, var, self.static_low, self.static_high)
        self.uni_tbl[(var, self.static_low, self.static_high)] = new_input_vtx
        self.vertices.append(new_input_vtx)
        return new_input_vtx

    def add_inv_vtx(self, vtx):
        '''Add inverted vertex.
        '''
        inv_vtx = self.ite(vtx, self.static_low, self.static_high, vtx.var)
        return inv_vtx

    def ite(self, f_vtx, g_vtx, h_vtx, var):
        '''If-then-else operation, which is used to apply Boolean operation on a ROBDD.
        ITE(F, G, H) = FG + F'H
        '''
        # terminal case
        if f_vtx is self.static_high:
            return g_vtx
        elif f_vtx is self.static_low:
            return h_vtx
        elif g_vtx is self.static_high and h_vtx is self.static_low:
            return f_vtx
        elif g_vtx is h_vtx:
            return g_vtx
        else:
            cur_var = var
            # restrict to high
            f_high_vtx = self._restrict(f_vtx, cur_var, 'high')
            g_high_vtx = self._restrict(g_vtx, cur_var, 'high')
            h_high_vtx = self._restrict(h_vtx, cur_var, 'high')
            # restrict to low
            f_low_vtx = self._restrict(f_vtx, cur_var, 'low')
            g_low_vtx = self._restrict(g_vtx, cur_var, 'low')
            h_low_vtx = self._restrict(h_vtx, cur_var, 'low')
            next_var = chr(ord(cur_var)+1)
            new_high_vtx = self.ite(f_high_vtx, g_high_vtx, h_high_vtx, next_var)
            new_low_vtx = self.ite(f_low_vtx, g_low_vtx, h_low_vtx, next_var)
            if new_high_vtx is new_low_vtx:
                return new_high_vtx
            else:
                if (cur_var, new_low_vtx, new_high_vtx) not in self.uni_tbl:
                    ite_expr = 'ITE({}, {}, {})'.format(cur_var, new_high_vtx.ite_expr,
                                                        new_low_vtx.ite_expr)
                    new_vtx = Vertex(cur_var, ite_expr, new_low_vtx, new_high_vtx)
                    logging.debug("        Create new vertex: {}, lo: {}, hi: {}, as {}".format(cur_var, new_low_vtx.ite_expr, new_high_vtx.ite_expr, ite_expr))
                    self.uni_tbl[(cur_var, new_low_vtx, new_high_vtx)] = new_vtx
                    self.vertices.append(new_vtx)
                    return new_vtx
                else:
                    return self.uni_tbl[(cur_var, new_low_vtx, new_high_vtx)]

    def _restrict(self, f_vtx, res_var, res_value):
        '''Restrict a function (vertex) to high (right child).
        f_vtx: func
        res_var: a char
        '''
        cur_var = f_vtx.var
        if ord(cur_var) > ord(res_var):
            return f_vtx
        elif ord(cur_var) == ord(res_var):
            if res_value == 'low':
                return f_vtx.low_v
            elif res_value == 'high':
                return f_vtx.high_v
            else:
                raise TypeError("res_value should be either 'high' or 'low'")
        else:
            raise TypeError("Expected lower restriction variable")

    def build_from_bool_func(self, file):
        '''Parse Boolean function in input3 and construct ITE expression.
        '''
        with open(file, 'r') as f:
            print('Parsing {}'.format(file))
            expr = f.readline().strip()
        # print(expr)
        and_exprs = expr.split('+')
        # print(and_exprs)
        and_results = [] # the resut after applying AND
        for mul_expr in and_exprs:
            # print(mul_expr)
            vars_ = mul_expr.split('*')
            # print('-> {}'.format(vars_))

            itervars = iter(vars_)
            first_var = next(itervars)
            vtx = self.get_root_vtx(first_var)
            for var in itervars:
                next_vtx = self.get_root_vtx(var)
                # print('{} * {}'.format(vtx.ite_expr, next_vtx.ite_expr))
                vtx = self.ite(vtx, next_vtx, self.static_low, 'a')
                # print('  -> {}'.format(vtx.ite_expr))
            and_results.append(vtx)
        iter_or_rslt = iter(and_results)
        vtx = next(iter_or_rslt)
        for res in iter_or_rslt:
            vtx = self.ite(vtx, self.static_high, res, 'a')
        # print(vtx.ite_expr)
        return vtx

    def get_root_vtx(self, var_str):
        '''Get the vertex of root given string like 'g', 'h', "g'", "h'".
        '''
        var_str = var_str.strip()
        if var_str.endswith("'") and len(var_str) != 2:
            tmp = var_str.split()
            var_str = ''.join(tmp)
        if var_str == 'g':
            return self.g_vtx
        elif var_str == 'h':
            return self.h_vtx
        elif var_str == "g'":
            return self.ite(self.g_vtx, self.static_low, self.static_high, 'a')
        elif var_str == "h'":
            return self.ite(self.h_vtx, self.static_low, self.static_high, 'a')
        else:
            raise TypeError('''Expected one of "g", "h", "g'" and "h'", got "{}"'''.format(var_str))

    def dump(self):
        '''Dump Boolean function in ITE format to file.
        This includes ITE of input1, input2 and input3.
        '''
        # dump file, add period before end of line
        with open(self.output, 'wt') as out_f:
            print("{}.".format(self.g_vtx.ite_expr), file=out_f)
            print("{}.".format(self.h_vtx.ite_expr), file=out_f)
            print("{}.".format(self.q_vtx.ite_expr), file=out_f)

def main():
    '''Main funciton.
    '''
    if len(sys.argv) != 5:
        sys.exit("Usage: python ROBDD.py <input1> <input2> <input3> <output>")

    print('CAD PA1 - ROBDD')
    robdd = ROBDD(sys.argv[1:5])
    robdd.run()

if __name__ == '__main__':
    main()
