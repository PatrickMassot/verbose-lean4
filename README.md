# Verbose Lean 4

This is very much work in progress port of Verbose Lean from Lean 3 to Lean 4.

## Notes about internationalisation:

* For error messages, the idea is to have for each language a hash map from names to functions
  consuming a number of arguments and returning the messages.
* For the tactic themselves, we should have a folder with a subfolder for each language containing the elaborators.
