# Installation

Either:
1. Install Agda v2.6.2 ([instructions](https://agda.readthedocs.io/en/v2.6.2/getting-started/installation.html))
   and `agda-stdlib` v1.7 ([instructions](https://github.com/agda/agda-stdlib/blob/v1.7/notes/installation-guide.md)).
   (This method is preferred.)
2. Install Agda v2.6.1.3 ([instructions](https://agda.readthedocs.io/en/v2.6.1.3/getting-started/installation.html))
   and `agda-stdlib` v1.6 ([instructions](https://github.com/agda/agda-stdlib/blob/v1.6/notes/installation-guide.md)).
  Then, replace `standard-library-1.7` with `standard-library-1.6` in [`calf.agda-lib`](./calf.agda-lib).

This is all that is required to play with **calf**.

## (Optional) Installing the `calf` Agda library

Find the absolute path of the `calf` folder (e.g., `$HOME/Downloads`), which we refer to as `CALF_PATH`.
Add the following line to `$HOME/.agda/libraries`:
```
CALF_PATH/calf/calf.agda-lib
```

**calf** should now be installed.


# Testing the Installation

To test your installation, run:
```
agda src/index.agda
```
or using Emacs mode, open `src/index.agda` and load the file by via `C-c C-l` (pressing Ctrl-`C` immediately followed by Ctrl-`L`).
