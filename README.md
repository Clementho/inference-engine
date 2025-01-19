# Propositional Logic Inference Engine
A Propositional Logic Inference Engine is a computational model designed to simulate rational reasoning by deriving logical conclusions from a set of given propositions. By manipulating formal logic, these engines evaluate the truth values of propositions based on a predefined knowledge base (KB). They are essential tools in fields such as artificial intelligence, automated reasoning, expert systems, and logical programming.

## Inference Methods
This engine utilizes 4 core inference methods:

1. **Truth Table**: A method that exhaustively lists all possible truth values for a set of propositions and determines their validity.
2. **Forward Chaining**: A data-driven approach that begins with known facts and applies inference rules to deduce new facts until a conclusion is reached.
3. **Backward Chaining**: A goal-driven approach that starts with a desired conclusion and works backward to find the supporting facts in the knowledge base.
4. **DPLL (Davis-Putnam-Logeman-Loveland) Algorithm**: An efficient algorithm used for determining the satisfiability of propositional logic formulas, often used in solving SAT problems.

## Minimum Requirements
* Python 3.7.16

Install the required dependencies from the `requirements.txt` file:
  ```bash
  $ pip install -r requirements.txt
  ```

## Program Instructions

### Running the Program with a Single Test Case and Inference Method
To execute the program, use the following command format:
  ```bash
  $ python main.py <filename> <method>
  ```

  * `<filename>` is the path to the test case txt files (e.g., `test-cases/test-1.txt`).
  * `<method>` is the inference method to execute (e.g., `TT`, `FC`, `BC`. `DPLL`).

### Batch Testing
To execute a batch test of all test cases with all inference methods:
  ```bash
  $ python batch_test.py
  ```

