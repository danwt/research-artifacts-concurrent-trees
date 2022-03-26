import os

"""
This program contains
1. A function returning all file paths of non-toolbox .tla files in models/
"""
    
def get_all_tla_file_paths():
    DIR = "models/"

    def is_part_of_toolbox(dirpath):
        return ".toolbox" in dirpath

    ret = []
    for (dirpath, dirnames, filenames) in os.walk(DIR):
        if not is_part_of_toolbox(dirpath):
            tla_files = [f for f in filenames if f.endswith(".tla")]
            for f in tla_files:
                p = dirpath + "/" + f
                ret.append(p)
    return ret
