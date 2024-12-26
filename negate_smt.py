import argparse
from pathlib import Path
from io import StringIO
from enum import Enum

class Closure(Enum):
    PAREN = 1
    ASSERT = 2
    DECL = 3 # Const or function declaration

def negated_file_name(original: Path) -> Path:
    return original.with_stem(original.stem + '_negated')

def negate_asserts(input_path: Path, output_path: Path,
                   verbose: bool=False,
                   remove_commands: bool = True,
                   keep_decls: bool = True,
                   ) -> None:
    original_text = None
    with open(input_path, 'r') as in_file:
        original_text = in_file.read()
    
    if verbose:
        print(original_text)
        
    if remove_commands:
        original_text = original_text.replace('(get-model)', '')
        original_text = original_text.replace('(check-sat)', '')
        original_text = original_text.replace('(exit)', '')
    # Used to track when we need to add a new closing paren due to an assert being negated
    
    # bodies of assert statements
    assert_bodies = []
    
    current = StringIO()
    
    # What the opening content is for when we close the parenthesis
    # PAREN means just write the closing paren
    # ASSERT means the paren closes an assert statement
    close_stack: list[Closure] = []
    with open(output_path, 'w') as out_file:
        while original_text:
            if verbose:
                print('>', repr(current.getvalue()))
            # No mode, check for vertical bar identifier
            if original_text.startswith('|'):
                # Write the bar
                original_text = original_text[1:]
                current.write('|')
                # Find the next | and split
                identifier, original_text = original_text.split('|', 1)
                
                if not identifier:
                    raise ValueError("Missing closing |")
                    
                # Copy the entire identifier
                current.write(identifier)
                current.write('|')
            
                
                can_start_assert = False
                
                if verbose:
                    print(f'|{identifier}|')
            elif original_text.startswith('('):
                original_text = original_text[1:]
                # If a top level function, write out the current buffer
                if not close_stack:
                    out_file.write(current.getvalue())
                    current.truncate(0)
                    current.seek(0)
                    
                    # Now check for the starting command
                    original_text = original_text.lstrip()
                    if original_text.startswith(('assert ', 'assert(')):
                        # We found an assert body, do not include the paren, put a 0 on the stack
                        close_stack.append(Closure.ASSERT)
                        original_text = original_text[len('assert'):]
                    elif original_text.startswith(('declare-fun ', 'declare-fun(')):
                        close_stack.append(Closure.DECL)
                        original_text = original_text[len('declare-fun'):]
                        current.write('(declare-fun')
                    elif original_text.startswith(('declare-const ', 'declare-const(')):
                        close_stack.append(Closure.DECL)
                        original_text = original_text[len('declare-const'):]
                        current.write('(declare-const')
                    else:
                        close_stack.append(Closure.PAREN)
                        current.write('(')
                else:
                    # If not top level, just close the paren
                    close_stack.append(Closure.PAREN)
                    current.write('(')
                
                if verbose:
                    print('(', close_stack)
                
            elif original_text[0].isspace():
                byte = original_text[0]
                current.write(byte)
                original_text = original_text[1:]
                
                if verbose:
                    print(byte)
                # Keeps same can assert
            elif original_text[0] == ')':
                original_text = original_text[1:]
                # Write out the correct number of closing parens
                if not close_stack:
                    raise ValueError('Unmatched )')
                close_mode: Closure = close_stack.pop()
                if close_mode == Closure.PAREN:
                    current.write(')')
                    if verbose:
                        print(')', close_stack)
                
                # If a top level function, write out the current buffer
                if not close_stack:
                    # If this is an assert, store its body instead
                    if close_mode == Closure.ASSERT:
                        assert_bodies.append(current.getvalue())
                    elif close_mode == Closure.DECL:
                        # Maybe write out the decl
                        if keep_decls:
                            current.write(')')
                            out_file.write(current.getvalue())
                        # Reset current
                        current.truncate(0)
                        current.seek(0)
                            
                    else:
                        out_file.write(current.getvalue())
                    current.truncate(0)
                    current.seek(0)
                    
                    if verbose:
                        print('', close_stack)

                
            else:
                byte = original_text[0]
                current.write(byte)
                original_text = original_text[1:]
                
                if verbose:
                    print(byte)
        
        
        if verbose:
            print(assert_bodies)
        # Now write out asserts
        out_file.write('\n(assert (or\n')
        
        for assert_body in assert_bodies:
            out_file.writelines(['  (not ', assert_body, ')\n'])
        
        out_file.write('))\n')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(
        description="Negates every the problem statement in an smtlib file"
    )
    

    parser.add_argument('filename',
                        type=Path,
                        help="The input file to negate asserts"
                        )

    parser.add_argument('-o', '--output',
                        type=Path,
                        help="File to output to. Defaults to <original_name>_negagated.<extension>"
                        )

    parser.add_argument('-v', '--verbose',
                        action='store_true',
                        )
    
    parser.add_argument('-c', '--keep-commands',
                        help='keep (check-sat), (get-model), and (exit) commands',
                        action='store_true'
                        )
    
    parser.add_argument('-d', '--remove-decls',
                        help="Keep function and constant declarations",
                        action='store_false'
                        )

    args = parser.parse_args()
    
    # Translate output
    input_path: Path = args.filename
    output_path = args.output
    if output_path is None:
        # Add _negated to the stem of the file name (keeps suffixes)
        output_path = input_path.with_stem(input_path.stem + '_negated')
    
    print(input_path, output_path)
    negate_asserts(
        input_path,
        output_path,
        verbose=args.verbose,
        remove_commands=not args.keep_commands,
        keep_decls=not args.remove_decls,
        )
