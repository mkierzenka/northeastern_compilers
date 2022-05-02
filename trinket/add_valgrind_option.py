from glob import glob
from pathlib import Path

for dest in glob("./input/**/*.trinket"):
    path = Path(dest).with_suffix(".options")
    if path.exists():
        continue
    path.touch()
    with open(path, "w") as path_f:
        path_f.write("valgrind")
    print(f"Added valgrind to {path}")
