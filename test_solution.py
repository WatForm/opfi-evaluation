#!/usr/bin/python3
import argparse
from pathlib import Path
import subprocess
import shutil
import shlex
from typing import IO
from collections import deque

from negate_smt import negate_asserts, negated_file_name
from definitions_to_asserts import transform_defs


parser = argparse.ArgumentParser()

parser.add_argument('-p', '--problem', type=Path, help="The smtlib problem file", required=True)
parser.add_argument('-s', '--solution', type=Path, required=True)

args = parser.parse_args()

problem_path: Path = args.problem
# Null replacement
solution_path: Path = args.solution

negated_path = negated_file_name(problem_path)

# TODO make chain better?
negate_asserts(problem_path, negated_path)

combined_path = problem_path.with_stem(problem_path.stem + '_combined')

# Combine negation and solution asserts
shutil.copyfile(negated_path, combined_path)

asserts: str = ""
with open(args.solution, 'r') as solution_file:
    asserts = transform_defs(solution_file.read())

with open(combined_path, 'a') as combined_file:
    combined_file.write(';; supposed solution\n')
    combined_file.write(asserts)

# Now run z3
command = f'z3 {combined_path} -model'
command = shlex.split(command)

# Should be unsat (no model)
# Just print model text for now
subprocess.run(command)
