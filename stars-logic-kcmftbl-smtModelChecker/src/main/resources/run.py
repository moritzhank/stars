import sys
import subprocess

if __name__ == "__main__":
    solverName = sys.argv[1]
    fileName = sys.argv[2]
    if solverName == "cvc5":
        result = subprocess.run(
            ["./cvc5", "-m", f"exchange/{fileName}"],
            capture_output = True,
            text = True
        )
        if result.returncode != 0:
            raise Exception(f"Error: {result.stderr}!")
        print(result.stdout)
    elif solverName == "z3":
        result = subprocess.run(
            ["z3", f"exchange/{fileName}"],
            capture_output = True,
            text = True
        )
        if result.returncode != 0:
            raise Exception(f"Error: {result.stderr}!")
        print(result.stdout)
    else:
        raise Exception(f"Unsupported solver: {solverName}!")