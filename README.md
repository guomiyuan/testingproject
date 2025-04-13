# testingproject overview
Combinatorial and Z3 testing techniques for testing quadratic equations and handling date conversions in Java.

# Functional Introduction

- `DateHelper`: Provides tools and methods for date processing.
- `Quadratic`: Implements the root-finding algorithm for quadratic equations, supporting complex and real number results.
- ‘DateCombinatorialTest.java’ // Use combinatorial's ACTS tool to generate test cases and then write to this code to test the date conversion case
- 'QuadraticCombinatorialTest.java' // Use combinatorial's ACTS tool to generate test cases and then write to this code to test the quadratic equation case
- 'DateZ3Test.java' //Use Z-solver's tool Z3 to generate test cases and then write this code to test the date conversion case
- 'QuadraticZ3Test.java' //Use Z-solver's tool Z3 to generate test cases and then write this code to test the quadratic equation case
- The test class covers tests of different dimensions and scenarios (combination tests, Z3 tests, etc.).
- z3/generate_quadratic_tests.smt2 //Use the Z3 tool to write SMT-LIB scripts for Quadratic Equation cases (to generate test cases)
- z3/quadratic_test_cases.txt //Use the Z3 tool to write SMT-LIB scripts for Quadratic Equation cases and then execute commands to generate test cases
- z3/generate_date_tests.smt2 //Use the Z3 tool to write SMT-LIB scripts for date conversion cases (to generate test cases)
- z3/date_tate_cases.txt //Use the Z3 tool to write an SMT-LIB script for the date conversion case and then execute the command to generate the test case
- pom.xml // Maven dependencies

  #Test Case Generation
- Combinatorial testing technology uses the ACTS tool to automatically generate test cases
- Z-Solver testing technology uses the Z3 tool to write SMT-LIB and then run commands to automatically generate test cases

# Mutation Testing
- Use the pitest tool. Modify the pom.xml file and add pitest dependencies 

# Code Coverage
- Use the JaCoCo tool. Modify the pom.xml file and add the JaCoCo dependency

# Notes
- Combinatorial testing tool ACTS download and usage instructions can be found at https://csrc.nist.gov/projects/automated-combinatorial-testing-for-software#
- The mutation test needs to modify the pom.xml file according to the location of targetClasses and targetTests generated in different cases. The default is Z3 date conversion
