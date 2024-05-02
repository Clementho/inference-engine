import sys

from textfile_reader import ProblemFileReader

from kb import PropDefiniteKB,expr_handle_infix_imp,expr



def main():
    # Check the number of arguments passed to the script
    if len(sys.argv) < 3:
        print("Usage: python iengine.py <filename> <method>")
        sys.exit(1)

    # Access the arguments
    script_name = sys.argv[0]
    filename = sys.argv[1]
    method = sys.argv[2]

    # print(f"Script Name: {script_name}")
    # print(f"Filename: {filename}")
    # print(filename,method)

    file_reader = ProblemFileReader(filename) # Create a file reader
    problem_details = file_reader.get_content_from_file()
    # print("Knowledge Base:", problem_details['knowledge_base'])
    # print("Query:", problem_details['query'])

    definite_clauses_KB = PropDefiniteKB()

    for clause in problem_details['knowledge_base']:
        clause = expr_handle_infix_imp(clause)
        definite_clauses_KB.tell(expr(clause))

    
    if method == "TT":
        print("TT method is being used")
        

    elif method=="FC":
        result = definite_clauses_KB.get_FC_solution(expr(problem_details['query']))  # Check if query can be derived
        result_string = ", ".join(str(symbol) for symbol in definite_clauses_KB.propositional_symbols_entailed_from_KB)
        print(f"YES; {result_string}" if result else "NO")
        
    
    elif method=="BC":
        
        print("BC method is being used")

   

   

   
  

            


    

if __name__ == "__main__":
    main()