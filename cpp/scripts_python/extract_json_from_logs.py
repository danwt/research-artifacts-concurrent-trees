import os

"""
A script to parse JSON debugging graphs from logs/ files.
The script automatically pushes the json to the visualizer.
"""

log_directory = "logs/"
temp_directory = "temp/"
log_extension = ".txt"
PREFIX = "[graph]"

def change_extension(filename):
    new = ".json"
    base = filename[:-len(log_extension)]
    return base + new

def get_filenames():
    ret = []
    for filename in os.listdir(log_directory):
        if filename.endswith(log_extension): 
            ret.append(filename)
    return ret

def get_blob(dir, filename):
    path = os.path.join(log_directory, filename)
    with open(path,'r') as inf:
        return inf.read()

def get_jsons(blob):
    ret = []
    lines = blob.split("\n")
    for line in lines:
        if PREFIX in line:
            ix = line.index(PREFIX) + len(PREFIX)
            j =  line[ix:]
            ret.append(j)
    return ret

def get_out_string(jsons):
    content = ','.join(jsons)
    out_str = f"[{content}]"
    return out_str


def write_to_dir(directory, filename, out_str):
    path = os.path.join(directory, filename)
    with open(path,'w') as outf:
        outf.write(out_str)
    

def main():

    filenames = get_filenames()
    blobs = [get_blob(log_directory,fn) for fn in filenames]
    jsons = [get_jsons(b) for b in blobs]
    json_filenames = [change_extension(fn) for fn in filenames]
    out_strings = [get_out_string(js) for js in jsons]
    for fn,out_str in zip(json_filenames,out_strings):
        write_to_dir("temp/", fn, out_str)
        write_to_dir("../visualize/src/hot_reload_json/", fn,  out_str)


if __name__=="__main__":
    print("Extracting json from logs")
    main()
    print("Done")
