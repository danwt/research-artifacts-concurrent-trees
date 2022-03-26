
from erase_translation_in_tla_file import erase
from get_all_tla_file_paths import get_all_tla_file_paths

"""
This program erases the translation for every .tla file in the models/ directory
"""

if __name__ == "__main__":
    paths = get_all_tla_file_paths()
    for p in paths:
        erase(p)