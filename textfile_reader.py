class ProblemFileReader:
    """
    A class to read and parse knowledge base from a text file.
    """
    
    def __init__(self, file_path):
        """
        Initializes the reader with the path to the problem definition file.
        """
        self.file_path = file_path
    
    def read_problem_file(self):
        """
        Reads the problem definition file and returns its content as a list of lines.
        """
        try:
            with open(self.file_path, 'r') as file:
                content = file.readlines()
            return content
        except IOError as e:
            print(f"An error occurred while reading the file: {e}")
            return None
    
    def parse_problem_content(self, content):
        """
        Parses the content of the problem definition file to separate the knowledge base and the query.
        
        Parameters:
        - content: List of strings representing the lines of the problem file.
        
        Returns:
        - A dictionary containing the 'knowledge_base' as a list of clauses and 'query' as a string.
        """
        if content is None:
            return None
        
        # Convert list of lines back into a single string
        content_string = ''.join(content)

        sections = content_string.split('ASK')
        tell_section = sections[0].strip().split('TELL')[1].strip()
        ask_section = sections[1].strip()
        
        knowledge_base = [clause.strip() for clause in tell_section.split(';') if clause.strip()]
        query = ask_section.strip()
        
        return {'knowledge_base': knowledge_base, 'query': query}
    
    def get_content_from_file(self):
        content = self.read_problem_file()
        problem_details = self.parse_problem_content(content)
        return problem_details
