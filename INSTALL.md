# Installation

1. Install Agda v2.6.2 ([installation instructions](https://agda.readthedocs.io/en/v2.6.2/getting-started/installation.html)).

2. Install `agda-stdlib` v1.7 ([installation instructions](https://github.com/agda/agda-stdlib/blob/v1.7/notes/installation-guide.md)).

3. It remains to install **calf** itself.
Find the absolute path of the `calf` folder (e.g., `$HOME/Downloads`), which we refer to as `CALF_PATH`.
Add the following line to `$HOME/.agda/libraries`:
```
CALF_PATH/calf/calf.agda-lib
```

**calf** should now be installed.

---

To test your installation, run:
```
agda src/Examples.agda
```
or using Emacs mode, open `src/Examples.agda` and load the file by via `C-c C-l` (pressing Ctrl-`C` immediately followed by Ctrl-`L`).
