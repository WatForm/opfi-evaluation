import sys
import argparse
import random

from random import sample
from typing import *

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description='A script for selecting a random subset of lines from a file.'
    )
    
    parser.add_argument(
        '--input_file',
        type = argparse.FileType('r'),
        help='A text file containing one test file per line.',
        default='all-ufnia-files.txt',
    )
    
    parser.add_argument(
        '--seed',
        type=int,
        help="Optional seed for random generation"
    )
    
    parser.add_argument(
        '-n', '--num_choices',
        type=int,
        help='Number of entries to be chosen',
    )
    
    parser.add_argument(
        '-i', '--ignore',
        type=argparse.FileType('r'),
        required=False,
        help="File containing entries to ignore."
    )
    
    parser.add_argument(
        '-o', '--output_file',
        type=argparse.FileType('w'),
        default='sample-benchmark.txt',
        help='Text file to write chosen entries to'
    )
    
    args = parser.parse_args()
    
    if args.seed is not None:
        random.seed(args.seed)
    
    entries: List[str] = args.input_file.readlines()
    
    if args.ignore is not None:
        for entry in args.ignore.readlines():
            entries.remove(entry)
    
    num_choices = args.num_choices if args.num_choices is not None else len(entries)
    chosen_entries = sample(entries, num_choices)
    
    args.output_file.writelines(chosen_entries)
    
    exit(0)
