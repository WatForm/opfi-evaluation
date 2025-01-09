#!/usr/bin/python3
import argparse
from pathlib import Path
import subprocess
import shutil
import shlex
from typing import IO
from collections import deque
from tempfile import NamedTemporaryFile

from negate_smt import negate_asserts, negated_file_name
from definitions_to_asserts import transform_defs


def is_valid_solution(problem_path: Path, solution_constraints: str, timeout: int = 3600) -> bool | None:
    temp_file = NamedTemporaryFile(mode='w', prefix='tmp_', suffix='.smttc',  dir='.', delete_on_close=False)
    test_path = temp_file.path
    temp_file.close()
    
    # Negate the original file
    negate_asserts(problem_path, test_path)
    # Now append the solution constraints
    with open(test_path, 'a') as test_file:
        test_file.write(';; supposed solution\n')
        test_file.write(solution_constraints)
        test_file.write('\n(check-sat)\n')
    
    # Now run z3
    command = f'z3 {test_path} -model'
    command = shlex.split(command)
    
    result = subprocess.run(command, capture_output=True, text=True, timeout=timeout)
    
    # Delete the temporary file
    del temp_file
    
    # We need a non-error result
    if result.returncode != 0:
        return None
    
    lowercase_output = result.stdout.lower()
    
    # Unsat is valid!
    if 'unsat' in lowercase_output:
        return True
    elif 'sat' in lowercase_output:
        return False
    else:
        # Not sure what the result is here
        return None
