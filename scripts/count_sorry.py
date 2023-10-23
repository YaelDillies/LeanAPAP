from glob import glob
import os
import re

def ident_to_word(ident: str):
    ident = ident.replace("_", " ")
    return ident[0].upper() + ident[1:]

def pretty_file(file: str):
    segments = file[4:].replace(".lean", "").split("/")
    name = ": ".join(ident_to_word(s) for s in segments)
    url = f"https://github.com/YaelDillies/LeanAPAP/blob/master/{file}"
    return f"[{name}]({url})"

files = [file for tree in os.walk("LeanAPAP") for file in glob(os.path.join(tree[0], '*.lean'))]
sorries = {}

for file in files:
    with open(file, "r") as f:
        contents = f.read()
    matches = [m.start() for m in re.finditer("sorry", contents)]
    if len(matches) != 0:
        sorries[pretty_file(file)] = len(matches)

result = """
| File | Sorries |
| ---- | ------- |
"""
for file in sorted(sorries.keys()):
    result += f"| {file} | {sorries[file]} |\n"

print(result)
if not os.path.exists("docs/_includes"):
    os.makedirs("docs/_includes")
with open("docs/_includes/sorries.md", "w") as f:
    f.write(result)
