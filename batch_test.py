import os
import subprocess

TEST_CASES_DIR = "test-cases"
TEST_OUTPUT_DIR = "test-results"
INFERENCE_METHODS = ["TT", "FC", "BC"]

# Output results to "test-results" directory, file format: results-<inference-method-abbreviation>.txt
def run_test_cases(inference_method):
    # Check if the results output directory exists, if not, create it
    if not os.path.exists(TEST_OUTPUT_DIR):
        os.makedirs(TEST_OUTPUT_DIR)

    output_file = (f"{TEST_OUTPUT_DIR}/results-{inference_method}.txt")
    files = os.listdir(TEST_CASES_DIR)
    files.sort(key=lambda x: int(x.split("-")[-1].split(".")[0])) # Sort the list of files based on the numeric suffix of the filename

    print(f"Running Batch Testing for <{inference_method}>....")

    with open(output_file, "w") as output: #Override file contents on write
        for file_name in files:
            if file_name.endswith(".txt"):
                test_case_path = os.path.join(TEST_CASES_DIR, file_name)
                command = ["python", "iengine.py", test_case_path, inference_method]

                try:
                    result = subprocess.run(command, capture_output=True, text=True, check=True)
                    output.write(f"Test Case: {file_name}\n")
                    output.write("Program Output:\n")
                    output.write(result.stdout)
                    output.write("\n\n")

                except subprocess.CalledProcessError as error:  # Capture and record the error stack trace to the output results text file
                    print(f"Error executing test case: <{file_name}>")
                    output.write(f"Error executing test case {file_name}: {error}\n\n")
                    output.write("Error output:\n")
                    output.write(error.stderr) # Access the error message from the CalledProcessError instance
                    output.write("\n\n")

    print(f"Finished Batch Testing for <{inference_method}>\n")

if __name__ == "__main__":
    for method in INFERENCE_METHODS:
        run_test_cases(method)
