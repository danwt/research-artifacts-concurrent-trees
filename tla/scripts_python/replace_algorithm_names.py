from get_all_tla_file_paths import get_all_tla_file_paths

"""
This program replaces all occurrences of the line

(* --algorithm <string> {

with 

(* --algorithm algo {

in the models/ directory
"""

def get_lines(path):
    with open(path,'r') as f:
        return f.read().split("\n")

def write_string(path, string):
    with open(path,'w') as f:
        f.write(string)

def replace(lines):

    PREFIX = "(* --algorithm "
    REPLACEMENT = "(* --algorithm algo {"

    for i, line in enumerate(lines):
        if line.startswith(PREFIX):
            lines[i] = REPLACEMENT

    return lines

if __name__ == "__main__":
    paths = get_all_tla_file_paths()
    for p in paths:
        lines = get_lines(p)
        replacement_lines = replace(lines)
        to_write = "\n".join(replacement_lines)
        write_string(p, to_write)
