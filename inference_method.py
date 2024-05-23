from utils import expr, remove_all, extend
from collections import defaultdict
from kb_parser import conjuncts, disjuncts, is_prop_symbol, prop_symbols, associate, to_cnf


class TruthTable:
    def __init__(self):
        # Initialize the counter for tracking the number of models where 'alpha' is true under 'kb'.
        self.correct_models = 0

    def tt_entails(self, kb, alpha):
        # Create a list of unique propositional symbols used in both the knowledge base (kb) and assertion (alpha).
        symbols = list(prop_symbols(kb & alpha))
        # Start the recursive check of all possible truth assignments to the symbols.
        return self.tt_check_all(kb, alpha, symbols, {})

    ## Main Algorithm for Truth Table Enumeration
    def tt_check_all(self, kb, alpha, symbols, model):
        """ Check all possible models recursively and determine if 'kb' entails 'alpha'. """
        if not symbols:
            # If no symbols left, evaluate the expressions with the current model.
            if pl_true(kb, model):
                result = pl_true(alpha, model)
                assert result in (True, False)
                self.correct_models += 1
                return result
            else:
                return True
        else:
            # Split the symbols into the first and the rest, and check all combinations of truth values.
            P, rest = symbols[0], symbols[1:]
            return (self.tt_check_all(kb, alpha, rest, extend(model, P, True)) and
                    self.tt_check_all(kb, alpha, rest, extend(model, P, False)))
    

class ForwardChaining:
    def __init__(self):
        self.KB_entailed_symbols = []

    ## Main Algorithm for Forward Chaining
    def pl_fc_entails(self, kb, q):
        """ Using known facts in the KB, further infer a chain of known facts until the queried symbol can be inferred. """
        count = {c: len(conjuncts(c.args[0])) for c in kb.clauses if c.op == '==>'} # Tracks the number of literals/symbols present in each clause's premise
        inferred = defaultdict(bool) # Keeps track of which symbol has been inferred
        agenda = [s for s in kb.clauses if is_prop_symbol(s.op)] # List of known facts/unit literals in the KB

        # While there are still unit literals/known facts to be used to infer other propositional symbols
        while agenda:
            p = agenda.pop(0)
            
            if p == q:
                self.KB_entailed_symbols.append(p)
                return True
            
            if not inferred[p]:
                inferred[p] = True
                self.KB_entailed_symbols.append(p)
                
                for c in kb.clauses_with_premise(p):
                    count[c] -= 1
                    if count[c] == 0: # When all the symbols of a clause's premise have been inferred to True, then the implied symbol is also True
                        agenda.append(c.args[1])

        return False

class BackwardsChaining:
    def __init__(self):
        self.KB_entailed_symbols = []

    ## Main Algorithm for Backwards Chaining
    def pl_bc_entails(self, kb, q, goals=set()):
        """
        Performs backwards chaining recursively to determine if a query can be entailed from the given knowledge base
        
        Parameters:
        - kb: Knowledge base containing the rules and facts represented as a list of strings.
        - q: The query symbol to be checked for entailment.
        - goals: Set containing the symbols that are currently being evaluated (used to prevent infinite loops).
        
        Returns: Boolean indicating whether the query can be entailed from the knowledge base.
        """
        goal_stack = goals
        facts = [s for s in kb.clauses if is_prop_symbol(s.op)] # List of known facts/unit literals in the KB

        if q in self.KB_entailed_symbols:
            return True

        if q in facts:
            self.KB_entailed_symbols.append(q)
            return True
        
        goal_stack.add(q) # Add the query symbol to the goal stack to track its evaluation
        q_clauses = kb.clauses_with_goal(q) # Get clauses with the query as the goal
        evaluated_clauses = defaultdict(bool) # Dictionary to track evaluated clauses

        # Check if the query is non-inferrable
        if not q_clauses and q not in self.KB_entailed_symbols and q not in facts:
            return False

        for c in q_clauses:
            clause_inferrable = True
            for p in conjuncts(c.args[0]):
                # If any premise symbol is part of the goal stack and not yet entailed, assume it is False
                if (p in goal_stack and p not in self.KB_entailed_symbols) or not self.pl_bc_entails(kb, p, goal_stack):
                    clause_inferrable = False            
                    break

            evaluated_clauses[c] = clause_inferrable

        # If no clauses evaluated to True, then the symbol is non-inferrable
        if evaluated_clauses and not any(evaluated_clauses.values()):
            return False

        self.KB_entailed_symbols.append(q)
        return True

class DPLL:

    ## Main Algorithm for DPLL
    def dpll(self, clauses, symbols, model):
        """See if the clauses are true in a partial model."""
        unknown_clauses = []  # clauses whose values are unknown

        for clause in clauses:
            val = pl_true(clause, model)
            
            if val is False:
                return False
            if val is not True:
                # For clauses that are still unknown, attempt to simplify them
                # If there contains literals whose values are known in the model but their values equate to false in the clause
                # Either their value is False in the model or they are negated in the clause
                literals = disjuncts(clause)

                for literal in literals:
                    # Only remove literals whose values are defined in the model
                    op, args = literal.op, literal.args
                    
                    if is_prop_symbol(op) and literal in model:
                        clause = associate('|', remove_all(literal, literals))
                    elif op == "~" and len(args) < 2 and args[0] in model:
                        clause = associate('|', remove_all(literal, literals))
  
                unknown_clauses.append(clause)

        if not unknown_clauses:
            return model
        
        # Find and remove all occurences of unit clauses from the propositional sentence
        P, value = self.find_unit_clause(unknown_clauses)
        if P:
            return self.dpll(unknown_clauses, remove_all(P, symbols), extend(model, P, value))
        
        # Find and remove all occurences of pure symbols from the propositional sentence
        P, value = self.find_pure_symbol(symbols, unknown_clauses)
        if P:
            return self.dpll(unknown_clauses, remove_all(P, symbols), extend(model, P, value))
        
        if not symbols:
            raise TypeError("Argument should be of the type Expr.")
        
        # Propogration when no unit or pure literals are found, no more simplifications can be made
        P, symbols = symbols[0], symbols[1:]
        return (self.dpll(clauses, symbols, extend(model, P, True)) or
                self.dpll(clauses, symbols, extend(model, P, False)))


    # Search for clauses that only have a single literal, a.k.a, unit clauses
    def find_unit_clause(self, clauses):
        """Find a unit clause in the given clauses and return the symbol and its value."""
        
        for clause in clauses:
            if len(clause.args) < 2:
                if is_prop_symbol(clause.op) and len(clause.args) == 0:
                    return clause, True
                else:
                    return clause.args[0], False 

        return None, None


    # Search for literals that only exist in one type of polarity (either True/False, not both) in the propositional sentence
    # If found, set them to their respective boolean values (if C then True, otherwise if ~C then False)
    def find_pure_symbol(self, symbols, clauses):
        """Find a pure symbol in the given clauses and return the symbol and its value."""
        counts = {}

        for symbol in symbols:
            counts[symbol] = [0, 0]  # [positive_count, negative_count]

        # Iterate through all the clauses and their literals to count the number of positive/negative polarities for each unique literal
        for clause in clauses:
            for literal in clause.args:
                if str(literal).startswith('~'):
                    counts[literal.args[0]][1] += 1
                else:
                    counts[literal][0] += 1

        for symbol in symbols:
            positive_count, negative_count = counts[symbol]
            if positive_count > 0 and negative_count == 0:
                return symbol, True
            elif negative_count > 0 and positive_count == 0:
                return symbol, False

        return None, None


    def dpll_satisfiable(self, kb_expr, query_expr):
        """Check the satisfiability of a propositional sentence. Returns the model when the sentence is True."""
        negated_query_expr = expr(f"~({query_expr})")
        p_sentence = associate("&", [kb_expr, negated_query_expr])

        # Converts the combined (KB & ~q) propositional sentence to CNF as a requisite for DPLL algorithm
        clauses = conjuncts(to_cnf(p_sentence))

        symbols = list(prop_symbols(p_sentence))
        return self.dpll(clauses, symbols, {})
    

def pl_true(exp, model={}):
    """Return True if the propositional logic expression is true in the model,
    and False if it is false. If the model does not specify the value for
    every proposition, this may return None to indicate 'not obvious';
    this may happen even when the expression is tautological.
    >>> pl_true(P, {}) is None
    True
    """
    # If the exp value is a boolean value, return it directly
    if exp in (True, False):
        return exp
    
    op, args = exp.op, exp.args

    #If the operator is found to be a propositional symbol, search the model to get its boolean value
    if is_prop_symbol(op):
        return model.get(exp)
    
    # When the expression is actually a negated literal
    elif op == '~':
        p = pl_true(args[0], model)
        if p is None:
            return None
        else:
            return not p
    
    # For disjunctive expressions, if any premise/literal in the expression is found to be True, then the expression is True
    # Otherwise False or None depending if the value of any premise/literal could not be inferred from the model
    elif op == '|':
        result = False
        for arg in args:
            p = pl_true(arg, model)
            if p is True:
                return True
            if p is None:
                result = None
        return result
    
    # For conjunctive expressions, if any premise/literal in the expression is found to be False, then the expression is False
    # Otherwise True or None depending if the value of any premise/literal could not be inferred from the model
    elif op == '&':
        result = True
        for arg in args:
            p = pl_true(arg, model)
            if p is False:
                return False
            if p is None:
                result = None
        return result
    
    p, q = args

    # Convert implications into its CNF equivalent expression
    if op == '==>':
        return pl_true(~p | q, model)
    elif op == '<==':
        return pl_true(p | ~q, model)
    
    # For further evaluations when the logical connective used in the expression is neither ~, &, |, ==>
    pt = pl_true(p, model)

    if pt is None:
        return None
    
    qt = pl_true(q, model)

    if qt is None:
        return None
    
    if op == '<=>':
        return pt == qt
    else:
        raise ValueError('Illegal operator in logic expression' + str(exp))