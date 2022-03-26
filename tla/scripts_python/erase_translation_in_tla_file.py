import sys

"""
This program takes a .tla file with a Pluscal translation and overwrites it with the same contents
except for that the translation is erased.

Usage:
command line arg is filename of pluscal spec to erase translation of
"""

HEAD = "\* BEGIN TRANSLATION"
TAIL = "\* END TRANSLATION"

to_write = None

def erase(filename):
    with open(filename, "r") as inf:
        lines = inf.read().split("\n")
        try:
            head_ix = [ix for ix, line in enumerate(lines) if line.startswith(HEAD)][0]
        except:
            # No translation found (HACK: not sure if this really works in all cases)
            return
        tail_ix = [ix for ix, line in enumerate(lines) if line.startswith(TAIL)][0]
        lines = lines[: head_ix + 1] + lines[tail_ix:]
        to_write = "\n".join(lines)

    with open(filename, "w") as ouf:
        ouf.write(to_write)


if __name__ == "__main__":
    filename = sys.argv[1]
    erase(filename)
