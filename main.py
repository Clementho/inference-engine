import sys

from utils import expr

from textfile_reader import ProblemFileReader

from kb import PropDefiniteKB

from inference_method import TruthTable, DPLL, ForwardChaining, BackwardsChaining

from kb_parser import is_horn_form, parse_sentences, expr_parse_infix_ops


VALID_INFERENCE_METHODS = ["TT", "DPLL", "FC", "BC"]
HORNKB_ONLY_METHODS = ["FC", "BC"]

def main():
    # Check the number of arguments passed to the script
    if len(sys.argv) < 3:
        print("Usage: python main.py <filename> <method>")
        sys.exit(1)

    # Access the arguments
    filename = sys.argv[1]
    method = sys.argv[2]

    # Instantiate the problem file reader and read the contents of the problem text file
    file_reader = ProblemFileReader(filename) # Create a file reader
    problem_details = file_reader.get_content_from_file()
    is_KB_horn_form = is_horn_form(problem_details['knowledge_base'], problem_details['query'])

    # Check if the requested inference method is valid
    if method not in VALID_INFERENCE_METHODS:
        print(f"Invalid inference method supplied. Please only select from the following: {VALID_INFERENCE_METHODS}")
        sys.exit(0)

    # TT & DPLL accepts both generic & horn form KBs
    if method == "TT":
        tt = TruthTable()
        kb_expr = parse_sentences(problem_details['knowledge_base'])
        query_expr = parse_sentences([problem_details['query']])

        if tt.tt_entails(kb_expr, query_expr):
            print(f"YES; {tt.correct_models}")
        else:
            print("NO")

    elif method == "DPLL":
        dpll = DPLL()
        kb_expr = parse_sentences(problem_details['knowledge_base'])
        query_expr = parse_sentences([problem_details['query']])
        contradiction_satisfiable = dpll.dpll_satisfiable(kb_expr, query_expr)

        # If the attempt to prove the contradicting statement (KB & ~q) returns FALSE
        # Then the contradiction is not satisfiable, as such only then can we determine that the KB entails q
        if contradiction_satisfiable == False:
            print("YES")
        # If the contradiction is satisfiable, print the model(set of literal truth values) that led to the contradiction being TRUE
        else:
            print(f"NO; {contradiction_satisfiable}")

    # Only allow chaining algorithms if the KB is in valid Horn Form
    # And the query is a single propositional symbol
    if is_KB_horn_form:
        definite_clauses_KB = PropDefiniteKB()
        # Convert each clause's implication symbol from '=>' to '==>'
        # Then create an expression string using expr() utility function
        for clause in problem_details['knowledge_base']:
            clause = expr_parse_infix_ops(clause)
            definite_clauses_KB.tell(expr(clause))

        if method=="FC":
            fc = ForwardChaining()
            result = fc.pl_fc_entails(definite_clauses_KB, expr(problem_details['query']))  # Check if query can be derived
            result_string = ", ".join(str(symbol) for symbol in fc.KB_entailed_symbols)
            print(f"YES; {result_string}" if result else "NO")

        elif method=="BC":
            bc = BackwardsChaining()
            result = bc.pl_bc_entails(definite_clauses_KB, expr(problem_details['query']))
            result_string = ", ".join(str(symbol) for symbol in bc.KB_entailed_symbols)
            print(f"YES; {result_string}" if result else "NO")

    elif not is_KB_horn_form and method in HORNKB_ONLY_METHODS:
        print(f"Provided KB is not valid Horn Form KB. Unable to use {HORNKB_ONLY_METHODS} methods")

if __name__ == "__main__":
    main()