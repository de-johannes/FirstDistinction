import subprocess
import os

def check_compilation():
    print("Step 1: Agda compilation...")
    try:
        # Run agda to generate latex
        # Assuming agda is in path. 
        # We need to be in the root dir for imports to work if there are any, 
        # but the file is in the root.
        result = subprocess.run(
            ["agda", "--latex", "--safe", "--without-K", "FirstDistinction.lagda.tex"],
            capture_output=True,
            text=True
        )
        if result.returncode != 0:
            print("Agda compilation failed:")
            print(result.stderr)
            print(result.stdout)
            return False
        print("Agda compilation successful.")
    except FileNotFoundError:
        print("Agda executable not found. Skipping Agda step (assuming .tex is updated or just checking latex syntax if possible).")
        # If we can't run Agda, we can't fully verify, but we can try to compile the existing tex if it was updated? 
        # Actually, if we edit .lagda.tex, we MUST run agda to update .tex.
        return False

    print("Step 2: LaTeX compilation...")
    try:
        os.chdir("latex")
        result = subprocess.run(
            ["xelatex", "-interaction=batchmode", "FirstDistinction.tex"],
            capture_output=True,
            text=True
        )
        if result.returncode != 0:
            print("LaTeX compilation failed.")
            # Check log file for errors?
            # print(result.stdout) # xelatex output is verbose
            # Grep for errors
            print("Errors found in output:")
            for line in result.stdout.splitlines():
                if line.startswith("!"):
                    print(line)
            return False
        print("LaTeX compilation successful.")
        return True
    except Exception as e:
        print(f"LaTeX step failed: {e}")
        return False
    finally:
        os.chdir("..")

if __name__ == "__main__":
    if check_compilation():
        print("SUCCESS: Build verified.")
    else:
        print("FAILURE: Build failed.")
        exit(1)
