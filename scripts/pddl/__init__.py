from .errors import AmbigiousStatement, NullStatement
import re
import random
import itertools
import timeit

def evaluate(world, query, as_conjunction = True, debugging = False):
    return recursive_evaluate(world, query, as_conjunction, 0)

def recursive_evaluate(world, query, as_conjunction, layer):
    if is_atom(query):
        return query

    if is_conditional(query):
        return evaluate_condition(world, query)

    for term in logical_split(query)[1:]:
        result = recursive_evaluate(world, term, as_conjunction, layer + 1)
        query = query.replace(term, result, 1)

    if is_query(query):
        return evaluate_query(world, query)

    if is_intersection(query):
        return evaluate_intersection(world, query)

    if is_union(query):
        return evaluate_intersection(world, query)

    if is_disjunction(query):
        return evaluate_disjunction(world, query)

    if is_conjunction(query):
        return evaluate_conjunction(world, query)

    if is_limit(query):
        return evaluate_limit(world, query)

    if not is_iterable(query) and contains_iterable(query):
        return build_conjunction(query)

    return query

def evaluate_query(world, condition, layer = 0):
    if not is_query(condition):
        return condition

    atoms = logical_split(condition)

    if len(atoms) == 3 and (is_iterable(atoms[1]) or is_iterable(atoms[2])):
        for idx, component in enumerate(atoms[1:]):
            if is_iterable(component):
                atoms[idx + 1] = logical_split(component)[1:]

        retval = set()
        for x in list(itertools.product(atoms[1], atoms[2])):
            retval.add(evaluate_query(world, '(' + atoms[0] + ' ' + x[0] + ' ' + x[1] + ')', layer))

        if len(retval) > 1:
            return '(set ' + ' '.join(list(retval)) + ')'

        return retval.pop()

    result = world.ask(condition)

    if not result:
        raise NullStatement(condition)

    if len(set(result)) > 1:
        return '(set ' + ' '.join(set(result)) + ')'

    return result[0]

def evaluate_condition(world, condition):
    if not is_conditional(condition):
        return condition

    terms = logical_split(condition)[1:]

    if world.is_satisfied(terms[0]):
        return evaluate(world, terms[1])

    if len(terms) > 2:
        return evaluate(world, terms[2])

    return str()

def evaluate_late(world, condition):
    if not is_late(condition):
        return condition

    return logical_split(condition)[1]

def evaluate_intersection(world, condition):
    if not is_intersection(condition):
        return condition

    atoms = [logical_split(term)[(1 if is_iterable(term) else 0):] for term in logical_split(condition)[1:]]
    atoms = list(set.intersection(*[set(atom) for atom in atoms]))

    if not atoms:
        raise NullStatement(condition)

    return ('(set ' + ' '.join(atoms) + ')' if len(atoms) > 1 else atoms[0])

def evaluate_union(world, condition):
    if not is_union(condition):
        return condition

    atoms = [logical_split(term)[(1 if is_iterable(term) else 0):] for term in logical_split(condition)[1:]]
    atoms = list(set.union(*[set(atom) for atom in atoms]))

    if len(atoms) > 1:
        return '(set ' + ' '.join(atoms) + ')'

    return atoms[0]

def evaluate_conjunction(world, condition):
    if not is_conjunction(condition):
        return condition

    atoms = [logical_split(term)[(1 if is_iterable(term) else 0):] for term in logical_split(condition)[1:]]
    atoms = list(set.union(*[set(atom) for atom in atoms]))

    if len(atoms) > 1:
        return '(set ' + ' '.join(atoms) + ')'

    return atoms[0]

def evaluate_disjunction(world, condition):
    if not is_disjunction(condition):
        return condition

    return logical_split(condition)[1]#random.choice(logical_split(condition)[1:])


def evaluate_limit(world, condition):
    if not is_limit(condition):
        return condition

    terms = logical_split(condition)

    if is_iterable(terms[1]):
        atoms = logical_split(terms[1])[1:]
    else:
        atoms = [terms[1]]

    if terms[0] == 'only':
        if len(atoms) != int(terms[2]):
            raise AmbigiousStatement(condition)

        return terms[1]

    if len(atoms) < int(terms[2]):
        raise AmbigiousStatement(condition)

    result = []

    for _ in range(int(terms[2])):
        idx = 0
        result.append(atoms.pop(idx))

    if len(result) == 1:
        return result[0]

    return '(set ' + ' '.join(result) + ')'

def logical_split(logical):
    tokens =  logical.replace('(', ' ( ').replace(')', ' ) ').split()
    return recursive_logical_split(tokens)

def recursive_logical_split(tokens, layer = 0):
    token = tokens.pop(0)
    if '(' == token:
        L = []
        while tokens[0] != ')':
            L.append(recursive_logical_split(tokens, layer + 1))
        tokens.pop(0)

        if layer:
            return '(' + ' '.join(L) + ')'
        else:
            return L

    if layer > 0:
        return token

    return [token]

def is_atom(term):
    return not term.startswith('(')

def is_negative(term):
    return term.startswith('(not ')

def is_query(term):
    return '?' in term

def is_conditional(term):
    return term.startswith('(if ')

def is_intersection(term):
    return term.startswith('(intersect ')

def is_union(term):
    return term.startswith('(union ')

def is_conjunction(term):
    return term.startswith('(and ')

def is_disjunction(term):
    return term.startswith('(or ')

def is_iterable(term):
    return term.startswith('(set ')

def is_limit(term):
    return term.startswith('(only ') or term.startswith('(any ')

def is_late(term):
    return term.startswith('(late ')

def is_complement(term):
    return term.startswith('(!')

def contains_iterable(term):
    return '(set ' in term

def is_tautology(world, term):
    if is_atom(term):
        return False

    constituents = logical_split(term)

    predicate_name = constituents[0]
    inverse_name = world.kb.inverse(predicate_name)

    for idx, constituent in enumerate(constituents[1:]):
        if is_atom(constituent):
            continue

        child_consituents = logical_split(constituent)

        if child_consituents[0] == predicate_name:
            if child_consituents[1 + idx] == '?' and child_consituents[2 - idx] == constituents[2 - idx]:
                return True

        if child_consituents[0] == inverse_name:
            if child_consituents[2 - idx] == '?' and child_consituents[1 + idx] == constituents[2 - idx]:
                return True

    return False

def negate(term):
    if term.startswith('(not '):
        return logical_split(term)[1]
    return '(not ' + term + ')'

def build_conjunction(term):
    if is_iterable(term) or not contains_iterable(term):
        return term

    atoms = logical_split(term)
    pieces = []

    for atom in atoms:
        atom = build_conjunction(atom)

        if is_iterable(atom):
            pieces.append(logical_split(atom)[1:])
        else:
            pieces.append([atom])

    pieces = itertools.product(*pieces)

    return '(and ' + ' '.join(['(' + ' '.join(piece) + ')' for piece in pieces]) + ')'
