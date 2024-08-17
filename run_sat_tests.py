#!venv/bin/python3

import subprocess
import os
import logging
import shutil


from testrunner import testrunner as tr
from testrunner import util 
import argparse
from typing import *


# Columns to store results
result_fields = ['return_code', 'time_elapsed', 'satisfiability']
# Options to ignore in output
ignore_fields = []

def result_values(opts: tr.OptionDict, result: subprocess.CompletedProcess,
                  time_elapsed: float) -> tr.OptionDict:
    if result.returncode != 0:
        logging.error('------OUTPUT------\n' + result.stdout + '------STDERR-----\n' + result.stderr +"------------")
    satisfiability: str = 'UNSURE'
    
    satisfiability = util.satisfiability_of_output(result.stdout)
    
    results = {
        'sat': satisfiability,
        'return_code': result.returncode,
        'time_elapsed': time_elapsed
    }
    logging.debug(f'Result: {satisfiability}')
    return results

def timeout_values(opts: tr.OptionDict, result: subprocess.TimeoutExpired) -> tr.OptionDict:
    results = {
        'sat': util.Satisfiablity.UNSURE,
        'return_code': 999,
        'time_elapsed': -1
    }
    return results

# Have the testrunner handle timeout
command = 'fortress --timeout 999999 -c {compiler} --scope {scope} {target_file}'


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    
    parser.add_argument(
        '--compilers',
        nargs='+',
        type=str,
        required=False,
        default=['UncheckedBV', 'NOBV'],
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
    
    

