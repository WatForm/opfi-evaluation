import os
import argparse

parser = argparse.ArgumentParser(
    description='Collects a list of all posible tests, ignoring the directories mentioned in README.md'
)

parser.add_argument('--directory', help='The path to the non-incremental directory', default='..')

parser.add_argument('--output', '-o', help='The output file', default='all-ufnia-files.txt')
parser.add_argument('--ignored-dirs', nargs='*',
                    default=['vcc-havoc', 'full', 'partial', 'qf'],
                    help='Subdirectories to ignore')

args = parser.parse_args()

with open(args.output, 'w') as f:
    # Walk though all the possible files, use absolute path
    for root, dirs, files in os.walk(os.path.abspath(args.directory)):
        for file in files:
            if str(file).endswith('.smt2') or str(file).endswith('.smttc'):
                f.write(os.path.join(root,file) + '\n')
        
        # Ignore skipped directories
        for ignored in args.ignored_dirs:
            if ignored in dirs:
                dirs.remove(ignored)
    