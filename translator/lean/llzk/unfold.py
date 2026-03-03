from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import smtlibscript_from_formula

import sys

input_file = sys.argv[1] if len(sys.argv) > 1 else "input.smt2"

parser = SmtLibParser()

# Parses the script and inlines the macros
script = parser.get_script_fname(input_file)
formula = script.get_last_formula()

# Dump it back to a file
with open("output.smt2", "w") as f:
	# This will write out the pure assertions without define-fun
	smtlibscript_from_formula(formula).serialize(f)
