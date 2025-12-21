def dpll(clauses, assignment=None):
    """
    clauses: list of sets (e.g. {{'P', '~Q'}, {'Q'}})
    assignment: dict mapping variable -> bool
    Returns: (sat: bool, assignment)
    """
    if assignment is None:
        assignment = {}

    if not clauses:
        return True, assignment
    
    for c in clauses:
        if not c or len(c)==0:
            return False, None
        
    def get_var(s):
        if s.startswith("~"):
            return s[1:]
        return s

    def get_val(s):
        return not s.startswith("~")
    
    def get_new_clauses(clas, var, ass):
        new_clauses = []
        for c in clas:
            if ( ass and (var in c) ) or ((not ass) and ("~"+var in c) ):
                continue

            if ((not ass) and var in c):
                new_c = c
                new_c.remove(var)
                new_clauses.append(new_c)
            elif (ass and ("~"+var in c) ):
                new_c = c
                new_c.remove("~"+ var)
                new_clauses.append(new_c)
            else:
                new_clauses.append(c)

        return new_clauses
    
    for c in clauses:
        if len(c)==1:
            s = next(iter(c))
            if get_var(s) in assignment and get_val(s)!=assignment[get_var(s)]:
                return False, None
            
            assignment[get_var(s)] = get_val(s)
            return dpll(get_new_clauses(clauses,get_var(s),get_val(s)),assignment)
        
    all_vars = set.union(*clauses)
    for v in all_vars:
        v1 = get_var(v)
        if (v1 not in all_vars) and (v1 not in assignment):
            assignment[v1] = get_val(v)
            return dpll(get_new_clauses(clauses,v1,get_val(v)),assignment)
        elif ("~"+v1 not in all_vars) and (v1 not in assignment):
            assignment[v1] = get_val(v)
            return dpll(get_new_clauses(clauses,v1,get_val(v)),assignment)

    dp_lit = next(iter(clauses[0]))
    dp_var = get_var(dp_lit)
    assignment[dp_var] = True
    ass2 = assignment
    sat, ass = dpll(get_new_clauses(clauses,dp_var,True),ass2)

    if sat:
        return True, ass
    
    assignment[dp_var] = False
    return dpll(get_new_clauses(clauses,dp_var,False),assignment)


    raise NotImplementedError