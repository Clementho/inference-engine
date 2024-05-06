from utils import Expr
from kb import expr

class TruthTable:
    def __init__(self):
        # Initialize the counter for tracking the number of models where 'alpha' is true under 'kb'.
        self.correct_models = 0

    def tt_entails(self, kb, alpha):
        # Create a list of unique propositional symbols used in both the knowledge base (kb) and assertion (alpha).
        symbols = list(self.prop_symbols(kb & alpha))
        # Start the recursive check of all possible truth assignments to the symbols.
        return self.tt_check_all(kb, alpha, symbols, {})

    def tt_check_all(self, kb, alpha, symbols, model):
        # Check all possible models recursively and determine if 'kb' entails 'alpha'.
        if not symbols:
            # If no symbols left, evaluate the expressions with the current model.
            if self.pl_true(kb, model):
                result = self.pl_true(alpha, model)
                assert result in (True, False)
                self.correct_models += 1
                return result
            else:
                return True
        else:
            # Split the symbols into the first and the rest, and check all combinations of truth values.
            P, rest = symbols[0], symbols[1:]
            return (self.tt_check_all(kb, alpha, rest, self.extend(model, P, True)) and
                    self.tt_check_all(kb, alpha, rest, self.extend(model, P, False)))

    def prop_symbols(self, x):
        # Recursively collect all propositional symbols from an expression.
        if not isinstance(x, Expr):
            return set()
        elif self.is_prop_symbol(x.op):
            return {x}
        else:
            return {symbol for arg in x.args for symbol in self.prop_symbols(arg)}

    def constant_symbols(self, x):
        # Recursively collect all constant symbols from an expression.
        if not isinstance(x, Expr):
            return set()
        elif self.is_prop_symbol(x.op) and not x.args:
            return {x}
        else:
            return {symbol for arg in x.args for symbol in self.constant_symbols(arg)}

    def predicate_symbols(self, x):
        # Recursively collect all predicate symbols and their arities from an expression.
        if not isinstance(x, Expr) or not x.args:
            return set()
        pred_set = {(x.op, len(x.args))} if self.is_prop_symbol(x.op) else set()
        pred_set.update({symbol for arg in x.args for symbol in self.predicate_symbols(arg)})
        return pred_set

    def tt_true(self, s):
        # Convenience method for checking the truth of a simple expression against a tautological knowledge base.
        s = expr(s)
        return self.tt_entails(True, s)

    def pl_true(self, exp, model={}):
        # Evaluate a logical expression 'exp' using the given truth assignment 'model'.
        if exp in (True, False):
            return exp
        op, args = exp.op, exp.args
        if self.is_prop_symbol(op):
            return model.get(exp)
        elif op == '~':
            p = self.pl_true(args[0], model)
            if p is None:
                return None
            else:
                return not p
        elif op == '|':
            result = False
            for arg in args:
                p = self.pl_true(arg, model)
                if p is True:
                    return True
                if p is None:
                    result = None
            return result
        elif op == '&':
            result = True
            for arg in args:
                p = self.pl_true(arg, model)
                if p is False:
                    return False
                if p is None:
                    result = None
            return result
        p, q = args
        if op == '==>':
            return self.pl_true(~p | q, model)
        elif op == '<==':
            return self.pl_true(p | ~q, model)
        pt = self.pl_true(p, model)
        if pt is None:
            return None
        qt = self.pl_true(q, model)
        if qt is None:
            return None
        if op == '<=>':
            return pt == qt
        elif op == '^':  
            return pt != qt
        else:
            raise ValueError('Illegal operator in logic expression' + str(exp))

    @staticmethod
    def extend(model, var, val):
        # Create a new model extending the current one by setting 'var' to 'val'.
        model = model.copy()
        model[var] = val
        return model

    @staticmethod
    def is_prop_symbol(s):
        # Check if a string 's' represents a propositional symbol.
        return isinstance(s, str) and s[0].isalpha()
