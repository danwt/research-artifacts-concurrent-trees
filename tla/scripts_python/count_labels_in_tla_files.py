from get_all_tla_file_paths import get_all_tla_file_paths

"""
This program reads all non-toolbox .tla files in models/ and prints information
about the Pluscal labels inside them.

Note: this isn't a general solution. This program only works
for the style of label used in this project, meaning labels which:
1. Are on their own line
2. Have no indentation
3. The last characters are ':' or ':+'
"""

# Strings to search for in path
INTERESTING_SET = {"bronson"}
PRINT_LABELS = True

def get_contents(path):
    with open(path,'r') as inf:
        return inf.read()

def label_info(lines_of_tla_file):

    def inside_pluscal(lines):
        START_PREFIX = "(* --algorithm"
        END_PREFIX = "\* BEGIN TRANSLATION"
        start_ix = None
        end_ix = None
        for i, line in enumerate(lines):
            if line.startswith(START_PREFIX):
                start_ix = i
            if line.startswith(END_PREFIX):
                end_ix = i

        # Be optimistic
        lines = lines[start_ix: end_ix]
        return lines

    def is_label(line):

        if not ":" in line:
            return False
            
        if line[0].isspace():
            return False

        stripped = line.strip()

        if not (stripped.endswith(":+") or stripped.endswith(":")):
            return False
            
        if len([c for c in stripped if c.isspace()]) != 0:
            return False

        return True

    def is_special_case(s):
        compare = {"DROPIN:", "NOTE:", "TODO:"}
        return s in compare
        
            
    pluscal_lines = inside_pluscal(lines_of_tla_file)
    label_lines = [l for l in pluscal_lines if is_label(l)]
    excluding_special_cases = [l for l in label_lines if not is_special_case(l)]
    ret = excluding_special_cases
    return ret

if __name__=="__main__":
    paths = get_all_tla_file_paths()

    paths = [p for p in paths if any([w in p for w in INTERESTING_SET])]

    paths.sort()

    for p in paths:
        contents = get_contents(p)
        lines = contents.split("\n")
        labels = label_info(lines)
        print(f"File: {p}: {len(labels)}")

