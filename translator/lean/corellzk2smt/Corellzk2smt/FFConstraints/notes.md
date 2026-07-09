# Functional formula

`<f,InVs,FFVs,BVs>` is functional if

- InVs is a subset of FFVs
- bvars(f) is a subset of BVs
- ffvars(f) is a subset of FFVs
- **For any values of InVs, the formula f is satisfiable**

The functional property can also be stated as:

  Given an assignment **rho**, we can be modify the mapping
  of any variable that is not in InVs, and get a satisfying
  assignment for f

# Composition

Given functional formulas `<f1,InVs1,FFVs1,BVs1>` and `<f2,InVs2,FFVs2,BVs2>` such that

- InVs2 is a subset of FFVs1

then `<f1/\f2,InVs1,FFVs1 \cup FFVs2,BVs1 \cup BVs2>` is functional

# Disjunction

Given functional formulas `<f1,InVs,FFVs1,BVs1>` and `<f2,InVs,FFVs2,BVs2>` and a formula
g such that

- ffvars(g) is a subset of InVs
- bvars(g) is empty

then

`<g/\f1 \/ ~g/\f2, InVs,FFVs1 \cup FFVs2,BVs1 \cup BVs2>` is functional
