# Installation

1. Install Agda v2.6.3 ([instructions](https://agda.readthedocs.io/en/v2.6.3/getting-started/installation.html)).
2. Install `agda-stdlib` v2.0 ([instructions](https://github.com/agda/agda-stdlib/blob/fc473ec/notes/installation-guide.md)).
   We have tested on commit [fc473ec](https://github.com/agda/agda-stdlib/tree/fc473ec905ab1a11a16718a7e8b628f1ab7eb435).

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
