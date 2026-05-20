from util.sygus import parse_literal


def inline_let(t, vars):
    def compute(t, vars, subst):
        match t:
            case ['let', bindings, body]:
                new_subst = dict(subst) | { v: compute(e, vars, subst) for v, e in bindings }
                new_vars = vars | set(v for v, _ in bindings)
                return compute(body, new_vars, new_subst)
            case [op, *args] if len(args) > 0:
                return (op,) + tuple(compute(a, vars, subst) for a in args)
            case _:
                return subst.get(t, t)
    return compute(t, vars, {})

def cse(term, vars):
    vn = {}
    prefix = 'v'
    count = 0
    def fresh():
        nonlocal count
        count += 1
        return f'v{count - 1}'

    def compute(term):
        nonlocal prefix, vn, vars
        if term in vars:
            return term
        elif term in vn:
            return vn[term]
        elif isinstance(term, str):
            res = f'{prefix}{len(vn)}'
            vn[term] = res
            return res
        else:
            op, *children = term
            children = tuple(compute(t) for t in children)
            res = fresh()
            vn[(op, *children)] = res
            return res
    res = compute(term)
    for t, v in reversed(vn.items()):
        res = ('let', ((v, t),), res)
    return res

def term_size(expr, vars, const_cost):
    match expr:
        case ['let', bindings, body]:
            new_vars = vars | set(v for v, _ in bindings)
            return sum(term_size(e, vars, const_cost) for _, e in bindings) \
                + term_size(body, new_vars, const_cost)
        case ['!', *args]:
            return sum(term_size(e, vars, const_cost) for e in args)
        case [op, *args]:
            assert len(args) > 0
            return 1 + sum(term_size(e, vars, const_cost) for e in args)
        case t:
            return 0 if t in vars else const_cost
    assert False, f'unknown expression: {expr}'

def find_vars(expr):
    match expr:
        case ['let', bindings, body]:
            return find_vars(body) \
                .difference(*(v for v, _ in bindings)) \
                .union(*(find_vars(e) for _, e in bindings))
        case [op, *args]:
            assert len(args) > 0
            return set().union(*(find_vars(e) for e in args))
        case t:
            try:
                parse_literal(t)
                return set()
            except:
                return set(t)
    assert False, f'unknown expression: {expr}'

def solution_sizes(sexpr, const_cost):
    def get_term_size(s, vars):
        phi = inline_let(s, vars)
        phi = cse(phi, vars)
        return term_size(phi, vars, const_cost)
    def get_term_size_define_fun(s):
        _, name, bindings, _, phi = s
        vars = set(v for v, _ in bindings)
        yield (name, get_term_size(phi, vars))
    if all(s[0] == 'define-fun' for s in sexpr):
        for s in sexpr:
            yield from get_term_size_define_fun(s)
    elif sexpr[0] == 'define-fun':
        yield from get_term_size_define_fun(sexpr)
    else:
        vars = find_vars(sexpr)
        yield ('?', get_term_size(sexpr, vars))