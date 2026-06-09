import z3;
ctx = z3.Context()
s = z3.Solver(ctx=ctx)
assertions = z3.parse_smt2_file("mux2_1_concrete.smt2")

# We use a set to keep track of unique functions found
functions = set()

def collect_funcs(expr):
    if z3.is_app(expr):
        f = expr.decl()
        if f.arity() > 0: # It's a function, not a constant
            functions.add(f)
        # Recursively check arguments
        for child in expr.children():
            collect_funcs(child)

# Scan every assertion in the file
for ast in assertions:
    collect_funcs(ast)

# Print the names of the functions found
for f in functions:
    print(f"Found Function: {f.name()} | Arity: {f.arity()}")