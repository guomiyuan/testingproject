# testingproject overview
Combinatorial and Z3 testing techniques for testing quadratic equations and handling date conversions in Java.

# Functional Introduction

- `DateHelper`: Provides tools and methods for date processing.
- `Quadratic`: Implements the root-finding algorithm for quadratic equations, supporting complex and real number results.
- `DateCombinatorialTest.java` // Use combinatorial's ACTS tool to generate test cases and then write to this code to test the date conversion case
- `QuadraticCombinatorialTest.java` // Use combinatorial's ACTS tool to generate test cases and then write to this code to test the quadratic equation case
- `DateZ3Test.java` //Use Z-solver's tool Z3 to generate test cases and then write to this code to test the date conversion case
- `QuadraticZ3Test.java` //Use Z-solver's tool Z3 to generate test cases and then write to this code to test the quadratic equation case
- `generate_quadratic_tests.smt2` //Use the Z3 tool to write SMT-LIB scripts for Quadratic Equation cases
- `quadratic_test_cases.txt` // Test cases generated for Quadratic Equation cases
- `generate_date_tests.smt2` //Use the Z3 tool to write SMT-LIB scripts for Date Conversion cases
- `date_tate_cases.txt` // Test cases generated for Date Conversion cases
- `pom.xml` // Maven dependencies

# Test Case Generation
- Combinatorial testing technology uses the ACTS tool to automatically generate test cases
- Z-Solver testing technology uses the Z3 tool to write SMT-LIB script and then run commands to automatically generate test cases

# Mutation Testing
- Use the pitest tool. Modify the pom.xml file and add pitest dependencies 

# Code Coverage
- Use the JaCoCo tool. Modify the pom.xml file and add the JaCoCo dependency

# Notes
- Combinatorial testing tool ACTS download and usage instructions can be found at https://csrc.nist.gov/projects/automated-combinatorial-testing-for-software#
- The mutation test needs to modify the pom.xml file according to the location of targetClasses and targetTests generated in different cases. The default is Z3 date conversion
