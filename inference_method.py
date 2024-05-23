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

    #KB = knowledge base
    #alpha = alphabetical literal to evaluate
    def tt_check_all(self, kb, alpha, symbols, model):
        # Check all possible models recursively and determine if 'kb' entails 'alpha'.
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

    ## Algorithm for Forward Chaining Inference Method
    def pl_fc_entails(self, kb, q):
        """
        [Figure 7.15]
        Use forward chaining to see if a PropDefiniteKB entails symbol q.
        >>> pl_fc_entails(horn_clauses_KB, expr('Q'))
        True
        """
        count = {c: len(conjuncts(c.args[0])) for c in kb.clauses if c.op == '==>'}
        inferred = defaultdict(bool)
        agenda = [s for s in kb.clauses if is_prop_symbol(s.op)]

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
                    if count[c] == 0:
                        agenda.append(c.args[1])

        return False

class BackwardsChaining:
    def __init__(self):
        self.KB_entailed_symbols = []

    
    # BC follows Depth-First Search principles
    # Local Variables:
    # - facts: Known facts in the KB
    # - goal_stack: Set containing the symbols that are currently being evaluated (used to prevent infinite loops).
    # - q_clauses: Clauses with the q as the goal
    # - evaluated_clauses: Dictionary to track whether each q_clause is inferrable
    # Pseudocode:
    # If the query symbol is a known fact or it already exists in the kb inferred symbols list:
    #    Add the symbol to the inferred symbols list if not already present
    #    Return True
    # Add the query symbol to the goal stack
    # Get all the clauses in which the query is a goal
    # For each symbol in each clause:
        # The clause is non-inferrable if the evaluated symbol is found in the goal stack & not in the inferred symbols list
    # If any clause of a symbol is True, then the symbol is inferrable

    ## Algorithm for Backwards Chaining Inference Method
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
        facts = [s for s in kb.clauses if is_prop_symbol(s.op)]

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

        # If no clauses evaluated to True, then symbol is non-inferrable
        if evaluated_clauses and not any(evaluated_clauses.values()):
            return False

        self.KB_entailed_symbols.append(q)
        return True

class DPLL:
    ## David Puttnam Algo

    # Use MOM's heuristic to further attempt to simplify the number of clauses
    # The aim is to create as many unit clauses as possible through each iteration of DPLL
    # How: Find the most occurences of a literal in the clauses of minimum length
    # I.E.: (a | b | c) & (a | b) & (b | c) & (a | d | c)
    # The shortest clause is 2 literals, so find the literal that appears the most in those clauses and expand them first
    def dpll(self, clauses, symbols, model):
        """See if the clauses are true in a partial model."""
        unknown_clauses = []  # clauses with an unknown truth value
        #print(f"Model: {model}")
        for clause in clauses:
            val = pl_true(clause, model)
            #print(f"Clause {clause} propositional value: {val}")
            
            if val is False:
                return False
            if val is not True:
                #For clauses that are still unknown, attempt to simplify them
                #If there contains literals whose values are known in the model but their values equate to false in the clause
                #Either their value is False in the model or they are negated in the clause
                literals = disjuncts(clause)
                #print(f"Literals of clause: {literals}")
                for literal in literals:
                    #print(f"Literal Op: {literal.op} Args: {literal.args}")

                    ## Only remove literals whose values are defined in the model
                    op, args = literal.op, literal.args
                    
                    if is_prop_symbol(op) and literal in model:
                        #print(f"Found literal to simplify from clauses: {literal}")
                        #print(f"Literals with literal {literal} removed: {remove_all(literal, literals)}")
                        clause = associate('|', remove_all(literal, literals))

                    elif op == "~" and len(args) < 2 and args[0] in model:
                        #print(f"Found literal to simplify from clauses: {literal}")
                        #print(f"Literals with literal {literal} removed: {remove_all(literal, literals)}")
                        clause = associate('|', remove_all(literal, literals))
                    # if literal in model:
                    #     print(f"Found literal to simplify from clauses: {literal}")
                    #     print(f"Literals with literal {literal} removed: {remove_all(literal, literals)}")
                    #     clause = associate('|', remove_all(literal, literals))

                #print(f"Clause to append: {clause}\n")
                unknown_clauses.append(clause)

        if not unknown_clauses:
            return model
        
        # Remove all occurences of unit clauses
        P, value = self.find_unit_clause(unknown_clauses)
        #print(f"Discovered Unit Clause: {P} - {value}\n")
        if P:
            return self.dpll(unknown_clauses, remove_all(P, symbols), extend(model, P, value))
        
        # Remove all occurences of the discovered pure symbol from the list of symbols
        P, value = self.find_pure_symbol(symbols, unknown_clauses)
        #print(f"Discovered Pure Symbol: {P} - {value}\n")
        if P:
            return self.dpll(unknown_clauses, remove_all(P, symbols), extend(model, P, value))
        
        if not symbols:
            raise TypeError("Argument should be of the type Expr.")
        
        # Propogration when no unit or pure literals are found, no more simplifications can be made
        P, symbols = symbols[0], symbols[1:]
        return (self.dpll(clauses, symbols, extend(model, P, True)) or
                self.dpll(clauses, symbols, extend(model, P, False)))


    #find unit clause
    #That is finding clauses with only a single literal
    def find_unit_clause(self, clauses):
        """Find a unit clause in the given clauses and return the symbol and its value."""
        #print(f"Unknown Clauses in UC: {clauses}")
        
        for clause in clauses:
            # print(f"Clause {clause} args: {clause.args}")
            # print(f"{clause.op} is Prop Symbol?: {is_prop_symbol(clause.op)}")

            if len(clause.args) < 2:
                if is_prop_symbol(clause.op) and len(clause.args) == 0:
                    return clause, True
                else:
                    return clause.args[0], False 

        return None, None


    #find pure symbol means to search for propositional symbols that occur in either truthy or negated state
    # E.g. (A || ~B || C) & (B || C) & (~A || C)
    # from the above CNF clause, there are a total of 3 unique symbols (A,B,C)
    # though only C is considered a pure symbol because throughout hte whole clause
    # it is found as a positive literal
    # A & B are not because found A, ~A, B, ~B
    # once we find all the pure symbols, we need to set them to their rspecive pure values (if C then True, if ~C then False)
    def find_pure_symbol(self, symbols, clauses):
        """Find a pure symbol in the given clauses and return the symbol and its value."""
        counts = {}
        #print(f"Unknown Clauses in PS: {clauses}")
        #Initialise each symbol's entry in the dictionary
        for symbol in symbols:
            counts[symbol] = [0, 0]  # [positive_count, negative_count]

        #Step through all the clauses and their literals to count the number of positive/negative polarities for each unique literal
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
        """Check satisfiability of a propositional sentence.
        This differs from the book code in two ways: (1) it returns a model
        rather than True when it succeeds; this is more useful. (2) The
        function find_pure_symbol is passed a list of unknown clauses, rather
        than a list of all clauses and the model; this is more efficient."""
        negated_query_expr = expr(f"~({query_expr})")
        p_sentence = associate("&", [kb_expr, negated_query_expr])

        clauses = conjuncts(to_cnf(p_sentence))

        #print(f"Propositional Sentence RAW: {p_sentence}")
        #print(f"DPLL Propositional Sentence CNF Form: {to_cnf(p_sentence)}")
        #print(f"DPLL Propositional Sentence CNF Form Clauses: {clauses}\n")

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
        # Evaluate a logical expression 'exp' using the given truth assignment 'model'.
        #print(f"Expression: {exp}")

        # If the exp value is a boolean value, return it directly
        if exp in (True, False):
            return exp
        
        op, args = exp.op, exp.args

        #print(f"Operator: {exp.op}\nExpression: Arguments: {exp.args}")

        #If the operator is found to be a propositional symbol, search the model to get its boolean value
        if is_prop_symbol(op):
            return model.get(exp)
        
        elif op == '~':
            p = pl_true(args[0], model)
            if p is None:
                return None
            else:
                return not p
            
        elif op == '|':
            result = False
            for arg in args:
                p = pl_true(arg, model)
                if p is True:
                    return True
                if p is None:
                    result = None
            return result
        
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

        # Convert implications into its logically equivalent expression
        if op == '==>':
            return pl_true(~p | q, model)
        elif op == '<==':
            return pl_true(p | ~q, model)
        
        pt = pl_true(p, model)

        #print(f"PT: {pt}")

        if pt is None:
            return None
        
        qt = pl_true(q, model)

        #print(f"PT: {qt}")

        if qt is None:
            return None
        
        if op == '<=>':
            return pt == qt
        elif op == '^':
            return pt != qt
        else:
            raise ValueError('Illegal operator in logic expression' + str(exp))