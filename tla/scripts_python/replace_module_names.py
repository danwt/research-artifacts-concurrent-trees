import ntpath

from get_all_tla_file_paths import get_all_tla_file_paths

"""
Replaces all occurrences of the line

------------------- MODULE <module name> -------------------

with 

------------------- MODULE <filename> -------------------

in the models/ directory, where filename is the name of the file.

Note that exact number of '-' characters may differ.
"""

def get_lines(path):
    with open(path,'r') as f:
        return f.read().split("\n")

def write_string(path, string):
    with open(path,'w') as f:
        f.write(string)

def replace(lines, filename):


    SUBSTR = " MODULE "
    REPLACEMENT = f"------------------- MODULE {filename} -------------------"

    first_line = lines[0]

    if SUBSTR not in first_line:
        err_str = f"First line '{first_line}' of {filename} does not contain {SUBSTR}"
        print(err_str)
        return lines

    lines[0] = REPLACEMENT

    return lines

if __name__ == "__main__":
    paths = get_all_tla_file_paths()
    for p in paths:
        lines = get_lines(p)
        filename = ntpath.basename(p)
        filename_without_extension = filename[:-4]
        replacement_lines = replace(lines, filename_without_extension)
        to_write = "\n".join(replacement_lines)
        write_string(p, to_write)
