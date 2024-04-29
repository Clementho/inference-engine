import sys

from textfile_reader import ProblemFileReader

from logic import PropKB,kb2expr





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
    print("Knowledge Base:", problem_details['knowledge_base'])
    print("Query:", problem_details['query'])

    # kb = PropKB()
    # for sentence in problem_details['knowledge_base']:

    #     kb.tell(kb2expr(sentence))
    # print(kb.clauses)

    # grid_size, initial_state, goal_states, walls = file_reader.get_content_from_file()
    # problem = RobotNavigationProblem(initial=initial_state, goal=goal_states, grid_size=grid_size, walls=walls) # get problem

    # print("Initial State:", problem.initial)
    # print("Goal States:", problem.goal)
    # print("Grid Size:", problem.grid_size)
    # print("Walls:", problem.walls)

    if method == "TT":
        print("TT method is being used")
       
    
 
    

    elif method=="FC":
        
        print("FC method is being used")
    
    elif method=="BC":
        
        print("FC method is being used")

   

   

   
  

            


    # Your script logic here

if __name__ == "__main__":
    main()