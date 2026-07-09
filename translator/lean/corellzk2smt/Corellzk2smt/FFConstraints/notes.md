# Functional formula

`<f,InVs,OutVs,AuxVs>` is functional if

- InVars and OutVars are two sets of FF variables
- InVars and OutVars are not necessarily disjoint
- AuxVs is a set of FF and boolean variables. The FF variables
  do not appear in InVs \cup

- **For any values of InVs, the formula f is satisfiable**

The functional property can also be stated as:

  Given an assignment **rho**, we can be modify the mapping
  of any variable that is not in InVs, and get a satisfying
  assignment for f

# Composition

Given functional formulas `<f1,InVs1,OutVs1,AuxVs1>` and `<f2,InVs2,OutVs2,AuxVs2>` such that

- InVs2 is a subset of FFVs1

then `<f1/\f2,InVs1,FFVs1 \cup FFVs2,BVs1 \cup BVs2>` is functional

# Disjunction

Given functional formulas `<f1,InVs,FFVs1,BVs1>` and `<f2,InVs,FFVs2,BVs2>` and a formula
g such that

- ffvars(g) is a subset of InVs
- bvars(g) is empty

then

`<phi/\f1 \/ ~phi/\f2, InVs,FFVs1 \cup FFVs2,BVs1 \cup BVs2>` is functional

# Semantic equivalence

A concrete execution has a corresponding abstract one and vice versa

Given a context, which is a formula

If we start from env and senv,
