# -*- coding: utf-8 -*-
from matchpy.expressions import (
    Arity, Operation, Symbol, Wildcard, SymbolWildcard, make_dot_variable, make_plus_variable, make_star_variable,
    make_symbol_variable
)

from multiset import Multiset

class SpecialSymbol(Symbol):
    pass


f = Operation.new('f', Arity.variadic)
f2 = Operation.new('f2', Arity.variadic)
f_u = Operation.new('f_u', Arity.unary)
f_i = Operation.new('f_i', Arity.variadic, one_identity=True)
f_c = Operation.new('f_c', Arity.variadic, commutative=True)
f2_c = Operation.new('f2_c', Arity.variadic, commutative=True)
f_a = Operation.new('f_a', Arity.variadic, associative=True)
f_ac = Operation.new('f_ac', Arity.variadic, associative=True, commutative=True)
a = Symbol('a')
b = Symbol('b')
c = Symbol('c')
d = Symbol('d')
s = SpecialSymbol('s')
_ = Wildcard.dot()
_s = Wildcard.symbol()
_ss = Wildcard.symbol(SpecialSymbol)
x_ = make_dot_variable('x')
s_ = make_symbol_variable('s')
ss_ = make_symbol_variable('ss', SpecialSymbol)
y_ = make_dot_variable('y')
z_ = make_dot_variable('z')
__ = Wildcard.plus()
x__ = make_plus_variable('x')
y__ = make_plus_variable('y')
z__ = make_plus_variable('z')
___ = Wildcard.star()
x___ = make_star_variable('x')
y___ = make_star_variable('y')
z___ = make_star_variable('z')

test_simplified = [
    (f_i(a),                                                            a),
    (f_i(a, b),                                                         f_i(a, b)),
    (f_i(_),                                                            _),
    (f_i(___),                                                          f_i(___)),
    (f_i(__),                                                           f_i(__)),
    (f_i(x_),                                                           x_),
    (f_i(x___),                                                         f_i(x___)),
    (f_i(x__),                                                          f_i(x__)),
    (f_a(f_a(a)),                                                       f_a(a)),
    (f_a(f_a(a, b)),                                                    f_a(a, b)),
    (f_a(a, f_a(b)),                                                    f_a(a, b)),
    (f_a(f_a(a), b),                                                    f_a(a, b)),
    (f_a(f(a)),                                                         f_a(f(a))),
    (f_c(a, b),                                                         f_c(a, b)),
    (f_c(b, a),                                                         f_c(a, b)),
]

for i in test_simplified:
    assert i[0] == i[1]

test_syntactic = [
    (a,             True),
    (x_,            True),
    (_,             True),
    (x___,          False),
    (___,           False),
    (x__,           False),
    (__,            False),
    (f(a),          True),
    (f(a, b),       True),
    (f(x_),         True),
    (f(x__),        False),
    (f_a(a),        False),
    (f_a(a, b),     False),
    (f_a(x_),       False),
    (f_a(x__),      False),
    (f_c(a),        False),
    (f_c(a, b),     False),
    (f_c(x_),       False),
    (f_c(x__),      False),
    (f_ac(a),       False),
    (f_ac(a, b),    False),
    (f_ac(x_),      False),
    (f_ac(x__),     False),
]

for i in test_syntactic:
    assert i[0].is_syntactic == i[1]

test_symbols = [
    (a,                 ['a']),
    (x_,                []),
    (_,                 []),
    (f(a),              ['a', 'f']),
    (f(a, b),           ['a', 'b', 'f']),
    (f(x_),             ['f']),
    (f(a, a),           ['a', 'a', 'f']),
    (f(f(a), f(b, c)),  ['a', 'b', 'c', 'f', 'f', 'f']),
]

for i in test_symbols:
    assert i[0].symbols == Multiset(i[1])


test_variables = [
    (a,                         []),
    (x_,                        ['x']),
    (_,                         []),
    (f(a),                      []),
    (f(x_),                     ['x']),
    (f(x_, x_),                 ['x', 'x']),
    (f(x_, a),                  ['x']),
    (f(x_, a, y_),              ['x', 'y']),
    (f(f(x_), f(b, x_)),        ['x', 'x']),
    (f(a, variable_name='x'),        ['x']),
    (f(f(y_), variable_name='x'),    ['x', 'y']),
]

for i in test_variables:
    assert(i[0].variables == Multiset(i[1]))
