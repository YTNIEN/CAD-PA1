#! /usr/bin/env python3
'''2017CAD PA1 - Reduction of Ordered Binary Decision Diagram (ROBDD)
'''

import sys

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
    def __init__(self, inputs):
        self.input1 = inputs[0]
        self.input2 = inputs[1]
        self.input3 = inputs[2]
        self.vertices = []
        self.uni_tbl = {} # (var, low_v, high_v) -> vertex
        self.static_low = None
        self.static_high = None
        self.init_static_vertex() # initialize s0 (low) and s1 (high) for ROBDD

    def init_static_vertex(self):
        '''Create 0 and 1 vertices.
        '''
        self.static_high = Vertex('~', '1')
        self.static_low = Vertex('~', '0')
        self.vertices.append(self.static_high)
        self.vertices.append(self.static_low)

    def run(self):
        '''1. Read AIG from two input files.
        2. Dump corresponding two ROBDD in ITE format.
        '''
        self.build_from_aig(self.input1)
        # self.build_from_aig(self.input2)

    def build_from_aig(self, aig_file):
        '''Build ROBDD described in a specified aig file.
        '''
        literal_to_vtx = {}
        uncreated_literals = {}
        in_literals = []
        out_literal = None

        with open(aig_file, 'r') as f:
            print('Parsing {}'.format(aig_file))
            header = f.readline()
            cnts = (int(cnt) for cnt in header.split()[1:])
            (max_var_cnt, in_cnt, latch_cnt, out_cnt, and_cnt)  = cnts
            if latch_cnt != 0:
                raise NotImplementedError('Expected latch number: 0, got {}'.format(latch_cnt))
            # get input literals
            for _ in range(in_cnt):
                literal = f.readline().split()[0]
                in_literals.append(literal)
                print(literal)
            # get output literals
            for _ in range(out_cnt):
                literal = f.readline().split()[0]
                out_literal = literal
                print(literal)
            # skip the and lines at the first parsing
            for _ in range(and_cnt):
                f.readline()
            # parse symbols of input and output
            for _ in range(in_cnt + out_cnt):
                type_, var = f.readline().split()[0:2]
                pos = int(type_[1:])
                literal = in_literals[pos]
                # meet output or latch symbol, next loop
                if type_.startswith('o') or type_.startswith('l'):
                    continue
                elif ((var, self.static_low, self.static_high) not in self.uni_tbl and
                      type_.startswith('i')):
                    input_vtx = self.add_input_vtx(var)
                    print('    Create new input vertex: {} ({})'.format(input_vtx.var, literal))
                assert input_vtx == self.uni_tbl[(var, self.static_low, self.static_high)], 'Error in setting input vertex'
                literal_to_vtx[literal] = input_vtx
                # create inverted inputs e.g. literal 3, 5, 7...
                inv_input_vtx = self.add_inv_vtx(input_vtx)
                literal_to_vtx[str(int(literal)+1)] = inv_input_vtx
                print('    Set neg input vertex: {} ({})'.format(inv_input_vtx.var, str(int(literal)+1)))

            # second parsing, skip input and output lines and parse only AND lines
            f.seek(0)
            for _ in range(in_cnt+out_cnt+1):
                f.readline() # header, input or output lines
            # parse AND lines
            for _ in range(and_cnt):
                out_literal, in_literal1, in_literal2 = f.readline().split()[0:3]
                print('{} {} {}'.format(out_literal, in_literal1, in_literal2))
                if in_literal1 in literal_to_vtx and in_literal2 in literal_to_vtx:
                    # AND
                    print('    In1 {}'.format(literal_to_vtx[in_literal1].ite_expr))
                    print('    In2 {}'.format(literal_to_vtx[in_literal2].ite_expr))
                    new_vtx = self.ite(literal_to_vtx[in_literal1], literal_to_vtx[in_literal2], self.static_low, 'a')
                    # NOT
                    new_inv_vtx = self.add_inv_vtx(new_vtx)
                    if int(out_literal) % 2 == 0:
                        literal_to_vtx[out_literal] = new_vtx
                        literal_to_vtx[str(int(out_literal)+1)] = new_inv_vtx
                        print('    Set vertex: {} ({})'.format(new_vtx.ite_expr, str(int(out_literal))))
                        print('    Set vertex: {} ({})'.format(new_inv_vtx.ite_expr, str(int(out_literal)+1)))
                    else:
                        # out_literal is a odd number
                        literal_to_vtx[str(int(out_literal)-1)] = new_vtx
                        literal_to_vtx[out_literal] = new_inv_vtx
                        print('    Set vertex: {} ({})'.format(new_vtx.ite_expr, str(int(out_literal)-1)))
                        print('    Set vertex: {} ({})'.format(new_inv_vtx.ite_expr, str(int(out_literal))))
                else:
                    # TODO: consider that literals of input are not set and add to "literal_to_vtx" yet
                    if in_literal1 not in literal_to_vtx:
                        # TODO: add to uncreated_
                        pass
                    if in_literal2 not in literal_to_vtx:
                        # TODO:
                        pass

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
            cur_var = f_vtx.var
            # restrict to high
            f_high_vtx = self.restrict(f_vtx, cur_var, 'high')
            g_high_vtx = self.restrict(g_vtx, cur_var, 'high')
            h_high_vtx = self.restrict(h_vtx, cur_var, 'high')
            # restrict to low
            f_low_vtx = self.restrict(f_vtx, cur_var, 'low')
            g_low_vtx = self.restrict(g_vtx, cur_var, 'low')
            h_low_vtx = self.restrict(h_vtx, cur_var, 'low')
            next_var = chr(ord(cur_var)+1)
            new_high_vtx = self.ite(f_high_vtx, g_high_vtx, h_high_vtx, next_var)
            new_low_vtx = self.ite(f_low_vtx, g_low_vtx, h_low_vtx, next_var)
            if new_high_vtx is new_low_vtx:
                return new_high_vtx
            else:
                if (cur_var, new_low_vtx, new_high_vtx) not in self.uni_tbl:
                    ite_expr = 'ITE[{}, {}, {}]'.format(cur_var, new_high_vtx.ite_expr,
                                                        new_low_vtx.ite_expr)
                    new_vtx = Vertex(cur_var, ite_expr, new_low_vtx, new_high_vtx)
                    print("        Create new vertex: {}, lo: {}, hi: {}, as {}".format(cur_var, new_low_vtx.ite_expr,  new_high_vtx.ite_expr, ite_expr))
                    self.uni_tbl[(cur_var, new_low_vtx, new_high_vtx)] = new_vtx
                    self.vertices.append(new_vtx)
                    return new_vtx
                else:
                    return self.uni_tbl[(cur_var, new_low_vtx, new_high_vtx)]

    def restrict(self, f_vtx, res_var, res_value):
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


def main():
    '''Main funciton.
    '''
    if len(sys.argv) != 5:
        sys.exit("Usage: python ROBDD.py <input1> <input2> <input3> <output>")

    print('CAD PA1 - ROBDD')
    robdd = ROBDD(sys.argv[1:4])
    robdd.run()




if __name__ == '__main__':
    main()
