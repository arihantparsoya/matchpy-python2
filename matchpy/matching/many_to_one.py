# -*- coding: utf-8 -*-
u"""Contains the :class:`ManyToOneMatcher` which can be used for fast many-to-one matching.

You can initialize the matcher with a list of the patterns that you wish to match:

>>> pattern1 = Pattern(f(a, x_))
>>> pattern2 = Pattern(f(y_, b))
>>> matcher = ManyToOneMatcher(pattern1, pattern2)

You can also add patterns later:

>>> pattern3 = Pattern(f(a, b))
>>> matcher.add(pattern3)

A pattern can be added with a label which is yielded instead of the pattern during matching:

>>> pattern4 = Pattern(f(x_, y_))
>>> matcher.add(pattern4, "some label")

Then you can match a subject against all the patterns at once:

>>> subject = f(a, b)
>>> matches = matcher.match(subject)
>>> for matched_pattern, substitution in sorted(map(lambda m: (str(m[0]), str(m[1])), matches)):
...     print('{} matched with {}'.format(matched_pattern, substitution))
f(a, b) matched with {}
f(a, x_) matched with {x ↦ b}
f(y_, b) matched with {y ↦ a}
some label matched with {x ↦ a, y ↦ b}

Also contains the :class:`ManyToOneReplacer` which can replace a set :class:`ReplacementRule` at one using a
:class:`ManyToOneMatcher` for finding the matches.
"""
from __future__ import absolute_import
import math
import html
import itertools
from collections import deque
from operator import itemgetter
from typing import Container, Dict, Iterable, Iterator, List, NamedTuple, Optional, Sequence, Set, Tuple, Type, Union
from itertools import imap

try:
    from graphviz import Digraph
except ImportError:
    Digraph = None
from multiset import Multiset

from ..expressions.expressions import (
    Expression, Operation, Symbol, SymbolWildcard, Wildcard, Pattern, AssociativeOperation, CommutativeOperation
)
from ..expressions.substitution import Substitution
from ..expressions.functions import is_anonymous, contains_variables_from_set, create_operation_expression, preorder_iter_with_position
from ..utils import (VariableWithCount, commutative_sequence_variable_partition_iter)
#from ..functions import replace
from .bipartite import BipartiteGraph, enum_maximum_matchings_iter
from .syntactic import OPERATION_END, is_operation

__all__ = [u'ManyToOneMatcher', u'ManyToOneReplacer']

LabelType = Union[Expression, Type[Operation]]
HeadType = Optional[Union[Expression, Type[Operation], Type[Symbol]]]
MultisetOfInt = Multiset
MultisetOfExpression = Multiset

_State = NamedTuple(u'_State', [
    (u'number', int),
    (u'transitions', Dict[LabelType, u'_Transition']),
    (u'matcher', Optional[u'CommutativeMatcher'])
])  # yapf: disable

_Transition = NamedTuple(u'_Transition', [
    (u'label', LabelType),
    (u'target', _State),
    (u'variable_name', Optional[unicode]),
    (u'patterns', Set[int]),
    (u'check_constraints', Optional[Set[int]]),
])  # yapf: disable

def f_replace(expression, position, replacement):
    ur"""Replaces the subexpression of `expression` at the given `position` with the given `replacement`.

    The original `expression` itself is not modified, but a modified copy is returned. If the replacement
    is a list of expressions, it will be expanded into the list of operands of the respective operation:

    >>> print(replace(f(a), (0, ), [b, c]))
    f(b, c)

    Parameters:
        expression:
            An :class:`Expression` where a (sub)expression is to be replaced.
        position:
            A tuple of indices, e.g. the empty tuple refers to the `expression` itself,
            `(0, )` refers to the first child (operand) of the `expression`, `(0, 0)` to the first
            child of the first child etc.
        replacement:
            Either an :class:`Expression` or a list of :class:`Expression`\s to be
            inserted into the `expression` instead of the original expression at that `position`.

    Returns:
        The resulting expression from the replacement.

    Raises:
        IndexError: If the position is invalid or out of range.
    """
    if len(position) == 0:
        return replacement
    if not isinstance(expression, Operation):
        raise IndexError(u"Invalid position {!r} for expression {!s}".format(position, expression))
    if position[0] >= len(expression):
        raise IndexError(u"Position {!r} out of range for expression {!s}".format(position, expression))
    pos = position[0]
    operands = list(expression)
    subexpr = replace(operands[pos], position[1:], replacement)
    if isinstance(subexpr, Sequence):
        new_operands = tuple(operands[:pos]) + tuple(subexpr) + tuple(operands[pos + 1:])
        return create_operation_expression(expression, new_operands)
    operands[pos] = subexpr
    return create_operation_expression(expression, operands)


class _MatchIter(object):
    def __init__(self, matcher, subject, intial_associative=None):
        self.matcher = matcher
        self.subjects = deque([subject])
        self.patterns = set(xrange(len(matcher.patterns)))
        self.substitution = Substitution()
        self.constraints = set(xrange(len(matcher.constraints)))
        self.associative = [intial_associative]

    def __iter__(self):
        for _ in self._match(self.matcher.root):
            for i in self._internal_iter():
                yield i

    def grouped(self):
        u"""
        Yield the matches grouped by their final state in the automaton, i.e. structurally identical patterns
        only differing in constraints will be yielded together. Each group is yielded as a list of tuples consisting of
        a pattern and a match substitution.

        Yields:
            The grouped matches.
        """
        for _ in self._match(self.matcher.root):
            yield list(self._internal_iter())

    def any(self):
        u"""
        Returns:
            True, if any match is found.
        """
        try:
            self.next()
        except StopIteration:
            return False
        return True

    def _internal_iter(self):
        for pattern_index in self.patterns:
            renaming = self.matcher.pattern_vars[pattern_index]
            new_substitution = self.substitution.rename(dict((renamed, original) for original, renamed in renaming.items()))
            pattern, label, _ = self.matcher.patterns[pattern_index]
            valid = True
            for constraint in pattern.global_constraints:
                if not constraint(new_substitution):
                    valid = False
                    break
            if valid:
                yield label, new_substitution

    def _match(self, state):
        if len(self.subjects) == 0:
            if state.number in self.matcher.finals or OPERATION_END in state.transitions:
                yield state
            heads = [None]
        else:
            heads = list(self._get_heads(self.subjects[0]))
        for head in heads:
            for transition in state.transitions.get(head, []):
                for i in self._match_transition(transition):
                    yield i

    def _match_transition(self, transition):
        if self.patterns.isdisjoint(transition.patterns):
            return
        label = transition.label
        if is_operation(label):
            if transition.target.matcher:
                for i in self._match_commutative_operation(transition.target):
                    yield i
            else:
                for i in self._match_regular_operation(transition):
                    yield i
            return
        if isinstance(label, Wildcard) and not isinstance(label, SymbolWildcard):
            min_count = label.min_count
            if label.fixed_size and not self.associative[-1]:
                assert min_count == 1, u"Fixed wildcards with length != 1 are not supported."
                if not self.subjects:
                    return
            else:
                for i in self._match_sequence_variable(label, transition):
                    yield i
                return
        subject = self.subjects.popleft() if self.subjects else None
        for i in self._check_transition(transition, subject):
            yield i

    def _check_transition(self, transition, subject, restore_subject=True):
        if self.patterns.isdisjoint(transition.patterns):
            return
        restore_constraints = set()
        restore_patterns = self.patterns - transition.patterns
        self.patterns &= transition.patterns
        old_value = None
        try:
            if transition.variable_name is not None:
                try:
                    old_value = self.substitution.get(transition.variable_name, None)
                    self.substitution.try_add_variable(transition.variable_name, subject)
                except ValueError:
                    return
                self._check_constraints(transition.check_constraints, restore_constraints, restore_patterns)
                if not self.patterns:
                    return

            for i in self._match(transition.target):
                yield i

        finally:
            if restore_subject and subject is not None:
                self.subjects.appendleft(subject)
            self.constraints |= restore_constraints
            self.patterns |= restore_patterns
            if transition.variable_name is not None:
                if old_value is None:
                    del self.substitution[transition.variable_name]
                else:
                    self.substitution[transition.variable_name] = old_value

    def _check_constraints(self, variable, restore_constraints, restore_patterns):
        if isinstance(variable, unicode):
            check_constraints = self.matcher.constraint_vars.get(variable, [])
        else:
            check_constraints = variable
        variables = set(self.substitution.keys())
        for constraint_index in check_constraints:
            if constraint_index not in self.constraints:
                continue
            constraint, patterns = self.matcher.constraints[constraint_index]
            if constraint.variables <= variables and not self.patterns.isdisjoint(patterns):
                self.constraints.remove(constraint_index)
                restore_constraints.add(constraint_index)
                if not constraint(self.substitution):
                    restore_patterns |= self.patterns & patterns
                    self.patterns -= patterns
                    if not self.patterns:
                        break

    @staticmethod
    def _get_heads(expression):
        for base in type(expression).__mro__:
            if base is not object:
                yield base
        if not isinstance(expression, Operation):
            yield expression
        yield None

    def _match_sequence_variable(self, wildcard, transition):
        min_count = wildcard.min_count
        if len(self.subjects) < min_count:
            return
        matched_subject = []
        for _ in xrange(min_count):
            matched_subject.append(self.subjects.popleft())
        while True:
            if self.associative[-1] and wildcard.fixed_size:
                assert min_count == 1, u"Fixed wildcards with length != 1 are not supported."
                if len(matched_subject) > 1:
                    wrapped = self.associative[-1](*matched_subject)
                else:
                    wrapped = matched_subject[0]
            else:
                wrapped = tuple(matched_subject)
            for i in self._check_transition(transition, wrapped, False):
                yield i
            if not self.subjects:
                break
            matched_subject.append(self.subjects.popleft())
        self.subjects.extendleft(reversed(matched_subject))

    def _match_commutative_operation(self, state):
        subject = self.subjects.popleft()
        matcher = state.matcher
        substitution = self.substitution
        for operand in subject:
            matcher.add_subject(operand)
        for matched_pattern, new_substitution in matcher.match(subject, substitution):
            restore_constraints = set()
            diff = set(new_substitution.keys()) - set(substitution.keys())
            self.substitution = new_substitution
            transition_set = state.transitions[matched_pattern]
            t_iter = iter(t.patterns for t in transition_set)
            potential_patterns = t_iter.next().union(*t_iter)
            restore_patterns = self.patterns - potential_patterns
            self.patterns &= potential_patterns
            for variable in diff:
                self._check_constraints(variable, restore_constraints, restore_patterns)
                if not self.patterns:
                    break
            if self.patterns:
                transition_set = state.transitions[matched_pattern]
                for next_transition in transition_set:
                    for i in self._check_transition(next_transition, subject, False):
                        yield i
            self.constraints |= restore_constraints
            self.patterns |= restore_patterns
        self.substitution = substitution
        self.subjects.append(subject)

    def _match_regular_operation(self, transition):
        subject = self.subjects.popleft()
        after_subjects = self.subjects
        operand_subjects = self.subjects = deque(subject)
        new_associative = transition.label if issubclass(transition.label, AssociativeOperation) else None
        self.associative.append(new_associative)
        for new_state in self._check_transition(transition, subject, False):
            self.subjects = after_subjects
            self.associative.pop()
            for end_transition in new_state.transitions[OPERATION_END]:
                for i in self._check_transition(end_transition, None, False):
                    yield i
            self.subjects = operand_subjects
            self.associative.append(new_associative)
        self.subjects = after_subjects
        self.subjects.appendleft(subject)
        self.associative.pop()


class ManyToOneMatcher(object):
    __slots__ = (u'patterns', u'states', u'root', u'pattern_vars', u'constraints', u'constraint_vars', u'finals')

    def __init__(self, *patterns):
        u"""
        Args:
            *patterns: The patterns which the matcher should match.
        """
        self.patterns = []
        self.states = []
        self.root = self._create_state()
        self.pattern_vars = []
        self.constraints = []
        self.constraint_vars = {}
        self.finals = set()

        for pattern in patterns:
            self.add(pattern)

    def add(self, pattern, label=None):
        u"""Add a new pattern to the matcher.

        The optional label defaults to the pattern itself and is yielded during matching. The same pattern can be
        added with different labels which means that every match for the pattern will result in every associated label
        being yielded with that match individually.

        Equivalent patterns with the same label are not added again. However, patterns that are structurally equivalent,
        but have different constraints or different variable names are distinguished by the matcher.

        Args:
            pattern:
                The pattern to add.
            label:
                An optional label for the pattern. Defaults to the pattern itself.
        """
        if label is None:
            label = pattern
        for i, (p, l, _) in enumerate(self.patterns):
            if pattern == p and label == l:
                return i
        # TODO: Avoid renaming in the pattern, use variable indices instead
        renaming = self._collect_variable_renaming(pattern.expression)
        self._internal_add(pattern, label, renaming)

    def _internal_add(self, pattern, label, renaming):
        u"""Add a new pattern to the matcher.

        Equivalent patterns are not added again. However, patterns that are structurally equivalent,
        but have different constraints or different variable names are distinguished by the matcher.

        Args:
            pattern: The pattern to add.

        Returns:
            The internal id for the pattern. This is mainly used by the :class:`CommutativeMatcher`.
        """
        pattern_index = len(self.patterns)
        index = 0
        renamed_constraints = [c.with_renamed_vars(renaming) for c in pattern.local_constraints]
        constraint_indices = [self._add_constraint(c, pattern_index) for c in renamed_constraints]
        self.patterns.append((pattern, label, constraint_indices))
        self.pattern_vars.append(renaming)
        pattern = self.rename_variables(pattern.expression, renaming)
        state = self.root
        patterns_stack = [deque([pattern])]

        while patterns_stack:
            if patterns_stack[-1]:
                subpattern = patterns_stack[-1].popleft()
                if isinstance(subpattern, Operation) and not isinstance(subpattern, CommutativeOperation):
                    patterns_stack.append(deque(subpattern))
                variable_name = getattr(subpattern, u'variable_name', None)
                state = self._create_expression_transition(state, subpattern, variable_name, pattern_index)
                if isinstance(subpattern, CommutativeOperation):
                    subpattern_id = state.matcher.add_pattern(subpattern, renamed_constraints)
                    state = self._create_simple_transition(state, subpattern_id, pattern_index)
                index += 1
            else:
                patterns_stack.pop()
                if len(patterns_stack) > 0:
                    state = self._create_simple_transition(state, OPERATION_END, pattern_index)

        self.finals.add(state.number)

        return pattern_index

    @classmethod
    def rename_variables(cls, expression, renaming):
        if isinstance(expression, Operation):
            if hasattr(expression, u'variable_name'):
                variable_name = renaming.get(expression.variable_name, expression.variable_name)
                return create_operation_expression(
                    expression, [cls.rename_variables(o, renaming) for o in expression], variable_name=variable_name
                )
            operands = [cls.rename_variables(o, renaming) for o in expression]
            return create_operation_expression(expression, operands)
        elif isinstance(expression, Expression):
            expression = expression.__copy__()
            expression.variable_name = renaming.get(expression.variable_name, expression.variable_name)
        return expression

    def _add_constraint(self, constraint, pattern):
        index = None
        for i, (c, patterns) in enumerate(self.constraints):
            if c == constraint:
                patterns.add(pattern)
                index = i
                break
        else:
            index = len(self.constraints)
            self.constraints.append((constraint, set([pattern])))
        for var in constraint.variables:
            self.constraint_vars.setdefault(var, set()).add(index)
        return index

    def match(self, subject):
        u"""Match the subject against all the matcher's patterns.

        Args:
            subject: The subject to match.

        Yields:
            For every match, a tuple of the matching pattern and the match substitution.
        """
        return _MatchIter(self, subject)

    def is_match(self, subject):
        u"""Check if the subject matches any of the matcher's patterns.

        Args:
            subject: The subject to match.

        Return:
            True, if the subject is matched by any of the matcher's patterns.
            False, otherwise.
        """
        return _MatchIter(self, subject).any()

    def _create_expression_transition(
            self, state, expression, variable_name, index
    ):
        label, head = self._get_label_and_head(expression)
        transitions = state.transitions.setdefault(head, [])
        commutative = isinstance(expression, CommutativeOperation)
        matcher = None
        for transition in transitions:
            if transition.variable_name == variable_name and transition.label == label:
                transition.patterns.add(index)
                if variable_name is not None:
                    constraints = set(
                        self.constraint_vars[variable_name] if variable_name in self.constraint_vars else []
                    )
                    for c in list(constraints):
                        patterns = self.constraints[c][1]
                        if patterns.isdisjoint(transition.patterns):
                            constraints.discard(c)
                    transition.check_constraints.update(constraints)
                state = transition.target
                break
        else:
            if commutative:
                matcher = CommutativeMatcher(type(expression) if isinstance(expression, AssociativeOperation) else None)
            state = self._create_state(matcher)
            if variable_name is not None:
                constraints = set(self.constraint_vars[variable_name] if variable_name in self.constraint_vars else [])
                for c in list(constraints):
                    patterns = self.constraints[c][1]
                    if index not in patterns:
                        constraints.discard(c)
            else:
                constraints = None
            transition = _Transition(label, state, variable_name, set([index]), constraints)
            transitions.append(transition)
        return state

    def _create_simple_transition(self, state, label, index, variable_name=None):
        if label in state.transitions:
            transition = state.transitions[label][0]
            transition.patterns.add(index)
            return transition.target
        new_state = self._create_state()
        transition = _Transition(label, new_state, variable_name, set([index]), None)
        state.transitions[label] = [transition]
        return new_state

    @staticmethod
    def _get_label_and_head(expression):
        if isinstance(expression, Operation):
            head = label = type(expression)
        else:
            label = expression
            if isinstance(label, SymbolWildcard):
                head = label.symbol_type
                label = SymbolWildcard(symbol_type=label.symbol_type)
            elif isinstance(label, Wildcard):
                head = None
                label = Wildcard(label.min_count, label.fixed_size)
            elif isinstance(label, Symbol):
                head = type(label)(label.name)
            else:
                head = expression

        return label, head

    def _create_state(self, matcher=None):
        state = _State(len(self.states), dict(), matcher)
        self.states.append(state)
        return state

    @classmethod
    def _collect_variable_renaming(
            cls, expression, position=None, variables=None
    ):
        u"""Return renaming for the variables in the expression.

        The variable names are generated according to the position of the variable in the expression. The goal is to
        rename variables in structurally identical patterns so that the automaton contains less redundant states.
        """
        if position is None:
            position = [0]
        if variables is None:
            variables = {}
        if getattr(expression, u'variable_name', False):
            if expression.variable_name not in variables:
                variables[expression.variable_name] = cls._get_name_for_position(position, variables.values())
        position[-1] += 1
        if isinstance(expression, Operation):
            if isinstance(expression, CommutativeOperation):
                for operand in expression:
                    position.append(0)
                    cls._collect_variable_renaming(operand, position, variables)
                    position.pop()
            else:
                for operand in expression:
                    cls._collect_variable_renaming(operand, position, variables)

        return variables

    @staticmethod
    def _get_name_for_position(position, variables):
        new_name = u'i{}'.format(u'.'.join(imap(unicode, position)))
        if new_name in variables:
            counter = 1
            while u'{}_{}'.format(new_name, counter) in variables:
                counter += 1
            new_name = u'{}_{}'.format(new_name, counter)
        return new_name

    def as_graph(self):  # pragma: no cover
        return self._as_graph(None)

    _PATTERN_COLORS = [
        u'#2E4272',
        u'#7887AB',
        u'#4F628E',
        u'#162955',
        u'#061539',
        u'#403075',
        u'#887CAF',
        u'#615192',
        u'#261758',
        u'#13073A',
        u'#226666',
        u'#669999',
        u'#407F7F',
        u'#0D4D4D',
        u'#003333',
    ]

    _CONSTRAINT_COLORS = [
        u'#AA3939',
        u'#D46A6A',
        u'#801515',
        u'#550000',
        u'#AA6C39',
        u'#D49A6A',
        u'#804515',
        u'#552600',
        u'#882D61',
        u'#AA5585',
        u'#661141',
        u'#440027',
    ]

    _VARIABLE_COLORS = [
        u'#8EA336',
        u'#B9CC66',
        u'#677B14',
        u'#425200',
        u'#5C9632',
        u'#B5E196',
        u'#85BC5E',
        u'#3A7113',
        u'#1F4B00',
        u'#AAA139',
        u'#807715',
        u'#554E00',
    ]

    @classmethod
    def _colored_pattern(cls, pid):  # pragma: no cover
        color = cls._PATTERN_COLORS[pid % len(cls._PATTERN_COLORS)]
        return u'<font color="{}"><b>p{}</b></font>'.format(color, pid)

    @classmethod
    def _colored_constraint(cls, cid):  # pragma: no cover
        color = cls._CONSTRAINT_COLORS[cid % len(cls._CONSTRAINT_COLORS)]
        return u'<font color="{}"><b>c{}</b></font>'.format(color, cid)

    @classmethod
    def _colored_variable(cls, var):  # pragma: no cover
        color = cls._VARIABLE_COLORS[hash(var) % len(cls._VARIABLE_COLORS)]
        return u'<font color="{}"><b>{}</b></font>'.format(color, var)

    @classmethod
    def _format_pattern_set(cls, patterns):  # pragma: no cover
        return u'{{{}}}'.format(u', '.join(imap(cls._colored_pattern, patterns)))

    @classmethod
    def _format_constraint_set(cls, constraints):  # pragma: no cover
        return u'{{{}}}'.format(u', '.join(imap(cls._colored_constraint, constraints)))

    def _as_graph(self, finals):  # pragma: no cover
        if Digraph is None:
            raise ImportError(u'The graphviz package is required to draw the graph.')
        graph = Digraph()
        if finals is None:
            patterns = [
                u'{}: {} with {}'.format(
                    self._colored_pattern(i), html.escape(unicode(p.expression)), self._format_constraint_set(c)
                ) for i, (p, l, c) in enumerate(self.patterns)
            ]
            graph.node(u'patterns', u'<<b>Patterns:</b><br/>\n{}>'.format(u'<br/>\n'.join(patterns)), {u'shape': u'box'})

        self._make_graph_nodes(graph, finals)
        if finals is None:
            constraints = [
                u'{}: {} for {}'.format(self._colored_constraint(i), html.escape(unicode(c)), self._format_pattern_set(p))
                for i, (c, p) in enumerate(self.constraints)
            ]
            graph.node(
                u'constraints', u'<<b>Constraints:</b><br/>\n{}>'.format(u'<br/>\n'.join(constraints)), {u'shape': u'box'}
            )
        self._make_graph_edges(graph)
        return graph

    def _make_graph_nodes(self, graph, finals):  # pragma: no cover
        state_patterns = [set() for i in xrange(len(self.states))]
        for state in self.states:
            for transition in itertools.chain.from_iterable(state.transitions.values()):
                state_patterns[transition.target.number] |= transition.patterns
        for state in self.states:
            name = u'n{!s}'.format(state.number)
            if state.matcher:
                graph.node(name, u'Sub Matcher', {u'shape': u'box'})
                subfinals = []
                graph.subgraph(state.matcher.automaton._as_graph(subfinals))
                submatch_label = u'<<b>Sub Matcher End</b>'
                for pattern_index, subpatterns, variables in state.matcher.patterns.values():
                    var_formatted = u', '.join(
                        u'{}[{}]x{}{}'.format(self._colored_variable(n), m, c, u'W' if w else u'')
                        for (n, c, m), w in variables
                    )
                    submatch_label += u'<br/>\n{}: {} {}'.format(
                        self._colored_pattern(pattern_index), subpatterns, var_formatted
                    )
                submatch_label += u'>'
                graph.node(name + u'-end', submatch_label, {u'shape': u'box'})
                for f in subfinals:
                    graph.edge(f, name + u'-end')
                graph.edge(name, u'n{}'.format(state.matcher.automaton.root.number))
            else:
                attrs = {u'shape': (u'doublecircle' if state.number in self.finals else u'circle')}
                graph.node(name, unicode(state.number), attrs)
                if state.number in self.finals:
                    sp = state_patterns[state.number]
                    if finals is not None:
                        finals.append(name + u'-out')
                    variables = [
                        u'{}: {}'.format(
                            self._colored_pattern(i),
                            u', '.join(u'{} -&gt; {}'.format(self._colored_variable(o), n) for n, o in r.items())
                        ) for i, r in enumerate(self.pattern_vars) if i in sp
                    ]
                    graph.node(
                        name + u'-out', u'<<b>Pattern Variables:</b><br/>\n{}>'.format(u'<br/>\n'.join(variables)),
                        {u'shape': u'box'}
                    )
                    graph.edge(name, name + u'-out')

    def _make_graph_edges(self, graph):  # pragma: no cover
        for state in self.states:
            for _, transitions in state.transitions.items():
                for transition in transitions:
                    t_label = u'<'
                    if transition.variable_name:
                        t_label += u'{}: '.format(self._colored_variable(transition.variable_name))
                    t_label += html.escape(unicode(transition.label))
                    if is_operation(transition.label):
                        t_label += u'('
                    t_label += u'<br/>{}'.format(self._format_pattern_set(transition.patterns))
                    if transition.check_constraints is not None:
                        t_label += u'<br/>{}'.format(self._format_constraint_set(transition.check_constraints))
                    t_label += u'>'

                    start = u'n{!s}'.format(state.number)
                    if state.matcher:
                        start += u'-end'
                    end = u'n{!s}'.format(transition.target.number)
                    graph.edge(start, end, t_label)


class ManyToOneReplacer(object):
    u"""Class that contains a set of replacement rules and can apply them efficiently to an expression."""

    def __init__(self, *rules):
        u"""
        A replacement rule consists of a *pattern*, that is matched against any subexpression
        of the expression. If a match is found, the *replacement* callback of the rule is called with
        the variables from the match substitution. Whatever the callback returns is used as a replacement for the
        matched subexpression. This can either be a single expression or a sequence of expressions, which is then
        integrated into the surrounding operation in place of the subexpression.

        Note that the pattern can therefore not be a single sequence variable/wildcard, because only single expressions
        will be matched.

        Args:
            *rules:
                The replacement rules.
        """
        self.matcher = ManyToOneMatcher()
        for rule in rules:
            self.add(rule)


    def add(self, rule):
        u"""Add a new rule to the replacer.

        Args:
            rule:
                The rule to add.
        """
        self.matcher.add(rule.pattern, rule.replacement)


    def replace(self, expression, max_count=float('inf')):
        u"""Replace all occurrences of the patterns according to the replacement rules.

        Args:
            expression:
                The expression to which the replacement rules are applied.
            max_count:
                If given, at most *max_count* applications of the rules are performed. Otherwise, the rules
                are applied until there is no more match. If the set of replacement rules is not confluent,
                the replacement might not terminate without a *max_count* set.

        Returns:
            The resulting expression after the application of the replacement rules. This can also be a sequence of
            expressions, if the root expression is replaced with a sequence of expressions by a rule.
        """
        #print(dir(functions))
        replaced = True
        replace_count = 0
        while replaced and replace_count < max_count:
            replaced = False
            for subexpr, pos in preorder_iter_with_position(expression):
                try:
                    replacement, subst = iter(self.matcher.match(subexpr)).next()
                    result = replacement(**subst)
                    expression = f_replace(expression, pos, result)
                    replaced = True
                    break
                except StopIteration:
                    pass
            replace_count += 1
        return expression


Subgraph = BipartiteGraph[Tuple[int, int], Tuple[int, int], Substitution]
Matching = Dict[Tuple[int, int], Tuple[int, int]]


class CommutativeMatcher(object):
    __slots__ = (u'patterns', u'subjects', u'automaton', u'bipartite', u'associative')

    def __init__(self, associative):
        self.patterns = {}
        self.subjects = {}
        self.automaton = ManyToOneMatcher()
        self.bipartite = BipartiteGraph()
        self.associative = associative

    def add_pattern(self, operands, constraints):
        pattern_set, pattern_vars = self._extract_sequence_wildcards(operands, constraints)
        sorted_vars = tuple(sorted(pattern_vars.values(), key=lambda v: (v[0][0] or u'', v[0][1], v[0][2], v[1])))
        sorted_subpatterns = tuple(sorted(pattern_set))
        pattern_key = sorted_subpatterns + sorted_vars
        if pattern_key not in self.patterns:
            inserted_id = len(self.patterns)
            self.patterns[pattern_key] = (inserted_id, pattern_set, sorted_vars)
        else:
            inserted_id = self.patterns[pattern_key][0]
        return inserted_id

    def add_subject(self, subject):
        if subject not in self.subjects:
            subject_id, pattern_set = self.subjects[subject] = (len(self.subjects), set())
            self.subjects[subject_id] = subject
            match_iter = _MatchIter(self.automaton, subject, self.associative)
            for _ in match_iter._match(self.automaton.root):
                for pattern_index in match_iter.patterns:
                    variables = self.automaton.pattern_vars[pattern_index]
                    substitution = Substitution(match_iter.substitution)
                    self.bipartite[subject_id, pattern_index] = substitution
                    pattern_set.add(pattern_index)
        else:
            subject_id, _ = self.subjects[subject]
        return subject_id

    def match(self, subjects, substitution):
        subject_ids = Multiset()
        pattern_ids = Multiset()
        for subject in subjects:
            subject_id, subject_pattern_ids = self.subjects[subject]
            subject_ids.add(subject_id)
            pattern_ids.update(subject_pattern_ids)
        for pattern_index, pattern_set, pattern_vars in self.patterns.values():
            if pattern_set:
                if not pattern_set <= pattern_ids:
                    continue
                bipartite_match_iter = self._match_with_bipartite(subject_ids, pattern_set, substitution)
                for bipartite_substitution, matched_subjects in bipartite_match_iter:
                    if pattern_vars:
                        ids = subject_ids - matched_subjects
                        remaining = Multiset(self.subjects[id] for id in ids)  # pylint: disable=not-an-iterable
                        sequence_var_iter = self._match_sequence_variables(
                            remaining, pattern_vars, bipartite_substitution
                        )
                        for result_substitution in sequence_var_iter:
                            yield pattern_index, result_substitution
                    elif len(subjects) == len(pattern_set):
                        yield pattern_index, bipartite_substitution
            elif pattern_vars:
                sequence_var_iter = self._match_sequence_variables(Multiset(subjects), pattern_vars, substitution)
                for variable_substitution in sequence_var_iter:
                    yield pattern_index, variable_substitution
            elif len(subjects) == 0:
                yield pattern_index, substitution

    def _extract_sequence_wildcards(self, operands,
                                    constraints):
        pattern_set = Multiset()
        pattern_vars = dict()
        for operand in operands:
            if not self._is_sequence_wildcard(operand):
                actual_constraints = [c for c in constraints if contains_variables_from_set(operand, c.variables)]
                pattern = Pattern(operand, *actual_constraints)
                index = None
                for i, (p, _, _) in enumerate(self.automaton.patterns):
                    if pattern == p:
                        index = i
                        break
                else:
                    index = self.automaton._internal_add(pattern, None, {})
                pattern_set.add(index)
            else:
                varname = getattr(operand, u'variable_name', None)
                if varname is None:
                    if varname in pattern_vars:
                        (_, _, min_count), _ = pattern_vars[varname]
                    else:
                        min_count = 0
                    pattern_vars[varname] = (VariableWithCount(varname, 1, operand.min_count + min_count), False)
                else:
                    if varname in pattern_vars:
                        (_, count, _), wrap = pattern_vars[varname]
                    else:
                        count = 0
                        wrap = operand.fixed_size and self.associative
                    pattern_vars[varname] = (VariableWithCount(varname, count + 1, operand.min_count), wrap)
        return pattern_set, pattern_vars

    def _is_sequence_wildcard(self, expression):
        if isinstance(expression, SymbolWildcard):
            return False
        if isinstance(expression, Wildcard):
            return not expression.fixed_size or self.associative
        return False

    def _match_with_bipartite(
            self,
            subject_ids,
            pattern_set,
            substitution,
    ):
        bipartite = self._build_bipartite(subject_ids, pattern_set)
        anonymous = set(i for i, (p, _, _) in enumerate(self.automaton.patterns) if is_anonymous(p.expression))
        for matching in enum_maximum_matchings_iter(bipartite):
            if len(matching) < len(pattern_set):
                break
            if not self._is_canonical_matching(matching, anonymous):
                continue
            try:
                bipartite_substitution = substitution.union(*(bipartite[edge] for edge in matching.items()))
            except ValueError:
                continue
            matched_subjects = Multiset(subexpression for subexpression, _ in matching)
            yield bipartite_substitution, matched_subjects

    def _match_sequence_variables(
            self,
            subjects,
            pattern_vars,
            substitution,
    ):
        only_counts = [info for info, _ in pattern_vars]
        wrapped_vars = [name for (name, _, _), wrap in pattern_vars if wrap and name]
        for variable_substitution in commutative_sequence_variable_partition_iter(subjects, only_counts):
            for var in wrapped_vars:
                operands = variable_substitution[var]
                if len(operands) > 1:
                    variable_substitution[var] = self.associative(*operands)
                else:
                    variable_substitution[var] = iter(operands).next()
            try:
                result_substitution = substitution.union(variable_substitution)
            except ValueError:
                continue
            yield result_substitution

    def _build_bipartite(self, subjects, patterns):
        bipartite = BipartiteGraph()
        n = 0
        m = 0
        s_states = {}
        p_states = {}
        for (subject, pattern), substitution in self.bipartite.edges_with_labels():
            if subject not in s_states:
                states = []
                for _ in xrange(subjects[subject]):
                    states.append((subject, n))
                    n += 1
                s_states[subject] = states
            if pattern not in p_states:
                states = []
                for _ in xrange(patterns[pattern]):
                    states.append((pattern, m))
                    m += 1
                p_states[pattern] = states

            for s_state in s_states[subject]:
                for p_state in p_states[pattern]:
                    bipartite[s_state, p_state] = substitution

        return bipartite

    @staticmethod
    def _is_canonical_matching(matching, anonymous_patterns):
        for (s1, n1), (p1, m1) in matching.items():
            for (s2, n2), (p2, m2) in matching.items():
                if p1 in anonymous_patterns and p2 in anonymous_patterns:
                    if n1 < n2 and m1 > m2:
                        return False
                elif s1 == s2 and n1 < n2 and m1 > m2:
                    return False
        return True


class SecondaryAutomaton(object):  # pragma: no cover
    # TODO: Decide whether to integrate this
    def __init__(self, k):
        self.k = k
        self.states = self._build(k)

    def match(self, edges):
        raise NotImplementedError

    @staticmethod
    def _build(k):
        states = dict()
        queue = [frozenset([0])]

        while queue:
            state_id = queue.pop(0)
            state = states[state_id] = dict()
            for i in xrange(1, 2**k):
                new_state = set()
                for t in [2**j for j in xrange(k) if i & 2**j]:
                    for v in state_id:
                        new_state.add(t | v)
                new_state = frozenset(new_state - state_id)
                if new_state:
                    if new_state != state_id:
                        state[i] = new_state
                    if new_state not in states and new_state not in queue:
                        queue.append(new_state)

        keys = sorted(states.keys())
        new_states = []

        for state in keys:
            new_states.append(states[state])

        for i, state in enumerate(new_states):
            new_state = dict()
            for key, value in state.items():
                new_state[key] = keys.index(value)
            new_states[i] = new_state

        return new_states

    def as_graph(self):
        if Digraph is None:
            raise ImportError(u'The graphviz package is required to draw the graph.')
        graph = Digraph()
        for i in xrange(len(self.states)):
            graph.node(unicode(i), unicode(i))

        for state, edges in enumerate(self.states):
            for target, labels in itertools.groupby(sorted(edges.items()), key=itemgetter(1)):
                label = u'\n'.join(bin(l)[2:].zfill(self.k) for l, _ in labels)
                graph.edge(unicode(state), unicode(target), label)

        return graph
