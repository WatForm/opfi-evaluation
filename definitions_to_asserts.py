#!/usr/bin/python
import argparse
import sys
from typing import IO
from collections import deque


def skip_space(text: deque[str]):
    while text[0].isspace():
        text.popleft()
    return text

def parse_identifier(text: deque[str]) -> str:
    identifier_chars: list[str] = []
    
    current = text.popleft()
    # Is this |identifier| form
    bar_quoted = current == '|'
    
    identifier_chars.append(current)
    
    if bar_quoted:
        # Read until |
        while True:
            current = text.popleft()
            identifier_chars.append(current)
            if current == '|':
                return ''.join(identifier_chars)
    else:
        while True:
            current = text.popleft()
            if current.isspace() or current in '()':
                # Put the ending char back
                if current in '()':
                    text.appendleft(current)
                return ''.join(identifier_chars)
            identifier_chars.append(current)
        

def transform_func_defn(defn: deque[str]) -> str:
    """Transforms a function definition into an assert statement"""
    # Ensure this starts with func defn
    for char in '(define-fun ':
        assert(defn.popleft() == char)
    
    skip_space(defn)
    
    # Parse the function identifier
    fname: str = parse_identifier(defn)
    
    skip_space(defn)
    
    # Now we parse the parameters
    # name, type list
    parameters: list[(str, str)] = []
    
    # We should see an open (
    assert(defn.popleft() == '(')
    
    while True:
        # Parse next parameter
        skip_space(defn)
        current = defn.popleft()
        if current == ')':
            break
        assert(current == '(')
        ident = parse_identifier(defn)
        skip_space(defn)
        type = parse_identifier(defn)
        assert(defn.popleft() == ')') # Close )
        parameters.append((ident, type))
    
    # Now read the next ident
    skip_space(defn)
    return_type: str = parse_identifier(defn)
    
    skip_space(defn)
    # Parse the body to the end
    body_chars: list[str] = []
    
    unclosed_parens: int = 1
    in_bar: bool = False
    
    while defn and unclosed_parens > 0:
        current = defn.popleft()
        
        if current == '|':
            in_bar = not in_bar
        # If in bar, we parens are just part of the id
        elif not in_bar:
            if current == '(':
                unclosed_parens += 1
            elif current == ')':
                unclosed_parens -= 1
        body_chars.append(current)
    assert(unclosed_parens == 0)
    assert(body_chars[-1] == ')')
    
    body: str = ''.join(body_chars[:-1])
    
    
    
    # Now make the output
    if parameters:
        avars = [
            f'({var_name} {type_name})' 
            for (var_name, type_name) in parameters
        ]
        
        fargs = [var_name for (var_name, _) in parameters]
        
        
        return f'(assert (forall ({" ".join(avars)}) (= ({fname} {" ".join(fargs)})\n {body})))'
    else:
        return f'(assert (= {fname} {body}))'


def transform_defs(in_str: str) -> str:
    in_text: deque[str] = deque(in_str)
    current_statement:deque[str] = deque()
    # While there is text in the queue
    asserts = []
    while in_text:
        # Top level
        # Read to next open paren
        current: str = in_text.popleft()
        if current != '(':
            continue
        
        # Now we parse the statement
        unclosed_parens = 1
        current_statement.append('(')
        while unclosed_parens > 0:
            current = in_text.popleft()
            current_statement.append(current)
            if current == '(':
                unclosed_parens += 1
            elif current == ')':
                unclosed_parens -= 1
        # Need to parse
        new_assert = transform_func_defn(current_statement)
        asserts.append(new_assert)
    return '\n'.join(asserts)
    

if __name__ == '__main__':
    parser = argparse.ArgumentParser()

    parser.add_argument( '-i', '--input',
                        type=argparse.FileType('r'),
                        default=sys.stdin
                        )

    parser.add_argument( '-o',  '--output',
                        type=argparse.FileType('w'),
                        default=sys.stdout
                        )

    args = parser.parse_args()

    in_file: IO  = args.input
    out_file: IO = args.output


    # Just read everything in
    in_str = in_file.read
    result: str = transform_defs(in_str)
    
    out_file.write(result)




        
    
