#!venv/bin/python3

"""Runs satisfiability tests. 
Then, if the method is sat, attempts to validate the result.
"""

import subprocess
import os
import logging
import shutil

from pathlib import Path
from testrunner import testrunner as tr
from testrunner import util 
import argparse
from typing import *

from validity_check import is_valid_solution
from testrunner.util import satisfiability_of_output


# Columns to store results
# unbound_valid is if the solution is valid for unbounded integers
result_fields = ['return_code', 'time_elapsed', 'sat', 'unbound_valid']
# Options to ignore in output
ignore_fields = []

# Result values needs some run-time info to save solutions to a file
def make_result_values(save_dir: Path) -> Callable[[tr.OptionDict, subprocess.CompletedProcess[str], float], tr.OptionDict]:
    """Result values needs to save the solution generated.
    This function creates result_values when given a directory to save solutions in."""
    # Ensure save dir exists and is empty
    os.makedirs(save_dir)
    
    def save_solution(solution: str, target_file: str) -> None:
        """Saves """
        save_file_name = target_file
        save_file_name.replace('/', '_')
        save_file_name.replace('\\', '_')
        
        save_path = save_dir / save_file_name
        with open(save_path, 'w') as f:
            f.write(solution)
        logging.debug('Wrote solution.')
    
    def result_values(opts: tr.OptionDict, result: subprocess.CompletedProcess[str],
                  time_elapsed: float) -> tr.OptionDict:
        if result.returncode != 0:
            logging.error('------OUTPUT------\n' + result.stdout + '------STDERR-----\n' + result.stderr +"------------")
            satisfiability = 'UNSURE'
            unbound_valid = 'NA'
        else:   
            satisfiability: str = 'UNSURE'
            
            result_str: str = result.stdout
            
            satisfiability = util.satisfiability_of_output(result_str)
            
            if satisfiability == util.Satisfiablity.SAT:
                
                # Trim to get constraints 
                constraints_text = result_str.split('====Constraints====')[1].split('==End Constraints==')[0]
                
                save_solution(constraints_text, opts['target_file'])
                
                validity = is_valid_solution(opts['target_file'], constraints_text)
                
                if validity is None:
                    unbound_valid = 'UNSURE'
                elif validity == True:
                    unbound_valid = 'VALID'
                else:
                    unbound_valid = 'INVALID'
            else:
                unbound_valid = 'NA'
                
                if satisfiability == util.Satisfiablity.UNSURE:
                    logging.error('------OUTPUT------\n' + result.stdout + '------STDERR-----\n' + result.stderr +"------------")
        
        results = {
            'sat': satisfiability,
            'return_code': result.returncode,
            'time_elapsed': time_elapsed,
            'unbound_valid': unbound_valid,
        }
        logging.debug(f'Result: {satisfiability}')
        return results
    
    return result_values


def timeout_values(opts: tr.OptionDict, result: subprocess.TimeoutExpired) -> tr.OptionDict:
    results = {
        'sat': util.Satisfiablity.UNSURE,
        'return_code': 999,
        'time_elapsed': -1,
        'unbound_valid': 'NA',
    }
    return results

# Have the testrunner handle timeout
# Added  -C for constraints
command = 'fortress -C --timeout 999999 -c {compiler} --scope {scope} {target_file}'


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    
    parser.add_argument(
        '--compilers',
        nargs='+',
        type=str,
        required=False,
        default=['Standard', 'UncheckedBV', 'NOBV'],
        help='List of Fortress compilers to use.'
    )
    
    parser.add_argument(
        '--scopes',
        nargs='+',
        type=int,
        required=False,
        default=[8],
        help='What scopes to run the tests at. Bitvectors will be the smallest size to hold at least this many values.'
    )
    
    parser.add_argument(
        '--timeout',
        '-t',
        type=int,
        default=20*60,
        help='Timeout in seconds'
    )
    
    parser.add_argument(
        '--files',
        type=str,
        default='sample-benchmark.txt',
        help='The path to a textfile containing the path to one model per line'
    )
    
    parser.add_argument(
        '--output', '-o',
        type=argparse.FileType('w'),
        default=f'test-{util.now_string()}.csv',
        help='Path to write output csv file to.'
    )
    
    parser.add_argument(
        '--solutions-dir', '-s',
        type=Path,
        default=f'./solutions/{util.now_string()}/',
        help='Path to store solutions in.'
    )
    
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Add verbose loging data',
    )
    
    parser.add_argument(
        '--iterations', '-i',
        type=int,
        default=1,
        help='Number of iterations to run each combination of options'
    )
    
    parser.add_argument(
        '--skip',
        type=int,
        default=0,
        help='Number of iterations to skip when resuming. NOTE: include iterations skipped due to timeout.'
    )
    
    
    
    args = parser.parse_args()
    
    compiler = tr.Option(
        'compiler',
        args.compilers,
    )
    
    scope = tr.Option(
        'scope',
        args.scopes,
    )
    
    target_file = tr.FromFileOption(
        'target_file',
        args.files,
    )
    
    if args.verbose:
        util.setup_logging_debug()
    else:
        util.setup_logging_default()
        
    # Make directory to store results
    
    result_values = make_result_values(args.solutions_dir)
    
    runner = tr.CSVTestRunner(
        command,
        compiler,
        scope,
        target_file,
        timeout=args.timeout,
        result_fields=result_fields,
        fields_from_result=result_values,
        fields_from_timeout=timeout_values,
        ignore_fields=ignore_fields,
    )
    
    runner.run(
        iterations=args.iterations,
        skip=args.skip,
        )
    
    

