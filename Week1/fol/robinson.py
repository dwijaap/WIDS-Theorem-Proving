"""
First-Order Logic - Robinson's Resolution Algorithm
Implement the Robinson resolution algorithm for FOL theorem proving.
"""

from typing import List, Tuple

# whether a variable or not
def is_var(x:str):
    return x and x[0].islower() and (x.find("(")==-1)

def is_func(x:str):
    if (is_var(x)):
        return False, "", []
    
    if x and x[0].islower() and x.find("(") != -1:
        _ , func , args = get_literal(x)
        return True, func, args
    
    return False, "", []



# gives whether negation, predicate name and its arguments
def get_literal(t:str):
    neg = t.startswith("~")
    if neg:
        t = t[1:]
    predicate = t[0:t.find("(")]
    arguments = t[t.find("(")+1:-1].split(",")
    return neg, predicate, arguments


# applies substitution on a term
def apply_sub_term(t, sub):
    fu, name, arg = is_func(t)
    if fu:
        new_args = [apply_sub_term(a,sub) for a in arg]
        s = f"{name}({','.join(new_args)})"
        return s

    while t in sub:
        t = sub[t]
    return t

# apply substitution on a literal -> i.e. a predicate
def apply_sub_literal(t, sub):
    neg, pred, args = get_literal(t)
    new_args = [apply_sub_term(a, sub) for a in args]
    s = f"{pred}({','.join(new_args)})"
    return "~" + s if neg else s


def uni_terms(t1,t2,sub):
    t1 = apply_sub_term(t1,sub)
    t2 = apply_sub_term(t2,sub)

    if t1==t2:
        return sub
    
    elif is_var(t1):
        sub[t1] = t2
        return sub
    
    elif is_var(t2):
        sub[t2] = t1
        return sub
    
    f1, n1, a1 = is_func(t1)
    f2, n2, a2 = is_func(t2)

    if f1 and f2 and n1==n2 and len(a1)==len(a2):
        for x1,x2 in zip(a1,a2):
            sub = uni_terms(x1,x2,sub)
        return sub
    
    return None


def unify(t1, t2) -> dict:
    """
    Unification algorithm - find most general unifier (MGU).
    
    Returns:
        Substitution dictionary if unifiable, None otherwise
    """
    # TODO: Implement unification algorithm
    n1, p1, a1 = get_literal(t1)
    n2, p2, a2 = get_literal(t2)

    if p1!=p2 or n1==n2 or len(a1)!=len(a2):
        return None
    
    sub = {}

    for x1,x2 in zip(a1,a2):
        sub = uni_terms(x1,x2,sub)
        if sub is None:
            return None
        
    return sub

def build_proof(clause, parents):
    proof = []
    def dfs(c):
        info = parents[c]
        if info is None:
            return

        c1, c2, l1, l2, subst = info
        dfs(c1)
        dfs(c2)
        proof.append((
            list(c1),
            list(c2),
            l1,
            l2,
            subst,
            list(c)
        ))

    dfs(clause)
    return proof


def robinson_resolution(clauses: List[List[str]], max_iterations: int = 1000) -> Tuple[str, List]:
    """
    Robinson's resolution algorithm for FOL.
    
    Args:
        clauses: List of clauses in CNF (each clause is list of literals)
        max_iterations: Maximum resolution steps before timeout
        
    Returns:
        ("UNSAT", proof) if empty clause derived (contradiction found)
        ("TIMEOUT", []) if max_iterations reached or no new clauses
    """
    # TODO: Implement Robinson's resolution algorithm

    # rename all vars in diff clauses:
    

    clause_set = set()
    parents = {}
    new = set()

    for c in clauses:
        fc = frozenset(c)
        clause_set.add(fc)
        parents[fc] = None

    for _ in range(max_iterations):
        clause_list = list(clause_set)

        for i in range(len(clause_list)):
            for j in range(i + 1, len(clause_list)):
                c1, c2 = clause_list[i], clause_list[j]

                for l1 in c1:
                    for l2 in c2:
                        sub = unify(l1, l2)
                        if sub is None:
                            continue

                        # complementary check is implicit in unify
                        resolvent = set()

                        for x in c1:
                            if x != l1:
                                resolvent.add(apply_sub_literal(x, sub))

                        for x in c2:
                            if x != l2:
                                resolvent.add(apply_sub_literal(x, sub))

                        # empty clause => contradiction
                        if not resolvent:
                            empty = frozenset()
                            parents[empty] = (c1, c2, l1, l2, sub)
                            # print ( build_proof(empty,parents))
                            return "UNSAT", build_proof(empty,parents)
                        
                        r2 = resolvent.copy()
                        for x in r2:
                            if "~"+x in r2:
                                resolvent.remove(x)
                                resolvent.remove("~"+x)

                        new_clause = frozenset(resolvent)
                        if new_clause and new_clause not in clause_set:
                            new.add(new_clause)
                            parents[new_clause] = (c1,c2,l1,l2,sub)


        if not new:
            return "TIMEOUT", []
        
        clause_set |= new
        new.clear()

    return "TIMEOUT", []

