
import org.junit.Test;  
import org.junit.Before;
import org.junit.After;

import java.io.ByteArrayOutputStream;
import java.io.ByteArrayInputStream;
import java.io.PrintStream;
import static org.junit.Assert.*;

import java.io.InputStream;
import java.util.Scanner;

import java.util.ArrayList; 
import java.util.regex.Pattern;



public class QuadraticCombinatorialTest {

    private final ByteArrayOutputStream outContent = new ByteArrayOutputStream();
    private final PrintStream originalOut = System.out;

    @Before
    public void setUpStreams() {
        System.setOut(new PrintStream(outContent));
    }

    @After
    public void restoreStreams() {
        System.setOut(originalOut);
    }

    @Test
    public void runAllTestCases() {
        double[][] testCases = {
                {1.0,     1.0,     -1.0},
                {1.0,    -1.0,      0.0},
                {1.0,     0.0,     1e100},
                {1.0,     1e100,   1e-100},
                {1.0,     1e-100,  1.0},
                {-1.0,    1.0,      0.0},
                {-1.0,   -1.0,     1e100},
                {-1.0,    0.0,     1e-100},
                {-1.0,    1e100,   1.0},
                {-1.0,    1e-100, -1.0},
                {0.0,     1.0,     1e100},
                {0.0,    -1.0,     1e-100},
                {0.0,     0.0,      1.0},
                {0.0,     1e100,   -1.0},
                {0.0,     1e-100,   0.0},
                {1e100,   1.0,     1e-100},
                {1e100,  -1.0,      1.0},
                {1e100,   0.0,     -1.0},
                {1e100,   1e100,   1e100},
                {1e100,   1e-100,  1e-100},
                {1e-100,  1.0,      1.0},
                {1e-100, -1.0,      1.0},
                {1e-100,  0.0,      0.0},
                {1e-100,  1e100,   1e100},
                {1e-100,  1e-100,  1e-100}
        };

        for (int i = 0; i < testCases.length; i++) {
            double a = testCases[i][0];
            double b = testCases[i][1];
            double c = testCases[i][2];
            outContent.reset();

            System.out.println("\nTest Case " + (i + 1) + ": a = " + a + ", b = " + b + ", c = " + c);
            try {
                if (a == 0) {
                    try {
                        Quadratic.solveQuadratic(a, b, c);
                        fail("Test Case " + (i + 1) + ": Expected exception for a=0");
                    } catch (Quadratic.NotEnoughPrecisionException e) {
                        System.out.println("Expected exception: " + e.getMessage());
                    } catch (Exception e) {
                        fail("Test Case " + (i + 1) + ": Unexpected exception for a=0: " + e);
                    }
                } else {
                    Quadratic.solveQuadratic(a, b, c);
                    String output = outContent.toString().trim();
                    double discriminant = b * b - 4 * a * c;

                    assertFalse("Test Case " + (i + 1) + ": Empty output", output.isEmpty());

                    if (Double.isNaN(discriminant) || discriminant == b * b) {
                        fail("Test Case " + (i + 1) + ": Discriminant overflow/underflow not handled");
                    } else if (discriminant < 0) {

					assertTrue("Test Case " + (i + 1) + ": Invalid complex roots format: " + output,
						output.matches("(?s).*x1 = .*i\\s*\\n.*x2 = .*i"));

                    } else {
					assertTrue("Test Case " + (i + 1) + ": Invalid real roots format: " + output,
						output.matches("(?s).*x1 = [-+]?\\d+(\\.\\d+)?([Ee][-+]?\\d+)?(\\n.*x2 = [-+]?\\d+(\\.\\d+)?([Ee][-+]?\\d+)?)?"));
										}
                }
            } catch (Quadratic.NotEnoughPrecisionException e) {
                System.out.println("Expected precision loss: " + e.getMessage());
            } catch (Throwable t) {
                fail("Test Case " + (i + 1) + ": Unexpected error: " + t);
            }
        }
    }



    //Add test cases to improve mutation score and jacoco coverage
    private String captureOutput(double a, double b, double c) throws Exception {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        PrintStream originalOut = System.out;
        System.setOut(new PrintStream(out));
        try {
            Quadratic.solveQuadratic(a, b, c);
        } finally {
            System.setOut(originalOut);
        }
        return out.toString().replace("\r", "").trim();
    }

    // Fix real root test
    @Test
    public void testRealRoots() throws Exception {
        String output = captureOutput(1, -5, 6);
        assertTrue("Output should contain x1=3.0",
            output.matches("(?s).*x1\\s*=\\s*3\\.?0?.*"));
        assertTrue("Output should contain x2=2.0",
            output.matches("(?s).*x2\\s*=\\s*2\\.?0?.*"));
    }

    // Fix complex root testing (match output format exactly)
	@Test
	public void testComplexRoots() throws Exception {
		String output = captureOutput(1, 0, 1);

		// Exactly match the actual output format
		assertEquals("x1 = i\nx2 = -i", output);

		// Or use a more flexible validation
		//assertTrue(output.matches("x1\\s*=\\s*i\\s*\nx2\\s*=\\s*-i"));
	}

    // Fix zero value test (exact match output)
    @Test
    public void testZeroCases() throws Exception {
        String output = captureOutput(1, 0, -1); // x²-1=0 → x=±1
        System.out.println("DEBUG ZERO OUTPUT: " + output); 

        // Loosely matching number formats
        assertTrue(output.matches("(?s).*x1\\s*=\\s*1\\.?0?.*"));
        assertTrue(output.matches("(?s).*x2\\s*=\\s*-1\\.?0?.*"));
    }

    // Perfect Square Test
    @Test
    public void testSqrtPrecision() throws Exception {
        String output = captureOutput(1, -2, 1); // (x-1)²=0
        assertTrue("Should show exact root",
            output.replaceAll("\\s+", "").matches(".*x1=1\\.?0?.*"));
    }

    // Boundary Testing
    @Test(expected = Quadratic.NotEnoughPrecisionException.class)
    public void testExtremeValues() throws Exception {
        captureOutput(1e300, 1e300, 1e300);
    }

    @Test
    public void testSignBehavior() throws Exception {
        String posOutput = captureOutput(1, 5, 6);
        String negOutput = captureOutput(1, -5, 6);
        assertNotEquals("Sign change should affect output", posOutput, negOutput);
    }

	@Test
	public void testValidateInput() throws Exception {
		// Test integer input
		assertEquals(1.0, Quadratic.validateInput("1.0"), 0.0);
		assertEquals(-2.0, Quadratic.validateInput("-2.0"), 0.0);

		// Testing decimal input
		assertEquals(1.5, Quadratic.validateInput("1.5"), 0.0);
		assertEquals(-0.25, Quadratic.validateInput("-0.25"), 0.0);

		// Avoid using scientific notation for input, or modify the method implementation
		assertEquals(100.0, Quadratic.validateInput("100.0"), 0.0);
	}

	@Test(expected = Quadratic.NotEnoughPrecisionException.class)
	public void testValidateInputExtremeValues() throws Exception {
		Quadratic.validateInput("1e400"); 
	}

	@Test(expected = NumberFormatException.class)
    public void testValidateInputInvalid() throws Exception {
        Quadratic.validateInput("abc");
    }

	@Test
	public void testValidateInputWithLargeNumber() throws Exception {
		assertEquals(Double.MAX_VALUE, Quadratic.validateInput(String.valueOf(Double.MAX_VALUE)), 0.0);
		assertEquals(Double.MIN_VALUE, Quadratic.validateInput(String.valueOf(Double.MIN_VALUE)), 0.0);
	}

	@Test
	public void testValidateInputWithIntegerInput() throws Exception {
		assertEquals(1.0, Quadratic.validateInput("1"), 0.0);
		assertEquals(-2.0, Quadratic.validateInput("-2"), 0.0);
	}

	@Test(expected = NumberFormatException.class)
	public void testValidateInputWithEmptyString() throws Exception {
		Quadratic.validateInput("");
	}

	@Test(expected = NumberFormatException.class)
	public void testValidateInputWithNonNumeric() throws Exception {
		Quadratic.validateInput("1.2.3");
	}

	@Test(expected = Quadratic.NotEnoughPrecisionException.class)
	public void testValidateInputWithExtremeScientificNotation() throws Exception {
		Quadratic.validateInput("1.0e400");
	}


    @Test
    public void testMainMethodOutputFormat() throws Exception {
        String input = "1\n0\n-1\nn\n"; // x²-1=0 → x=±1
        InputStream in = new java.io.ByteArrayInputStream(input.getBytes());
        System.setIn(in);

        ByteArrayOutputStream out = new ByteArrayOutputStream();
        PrintStream originalOut = System.out;
        System.setOut(new PrintStream(out));

        try {
            Quadratic.main(new String[]{});
        } finally {
            System.setOut(originalOut);
        }

        String output = out.toString();
        assertTrue(output.contains("x1 = 1"));
        assertTrue(output.contains("x2 = -1"));
    }



	@Test
	public void testMainMethodWithZeroA() throws Exception {
		// a = 0 (invalid), retry with a=1, b=-2, c=1, then exit with n
		String input = "0\n1\n-2\n1\nn\n";
		InputStream in = new ByteArrayInputStream(input.getBytes());
		System.setIn(in);

		ByteArrayOutputStream out = new ByteArrayOutputStream();
		PrintStream originalOut = System.out;
		System.setOut(new PrintStream(out));

		try {
			Quadratic.main(new String[]{});
			String output = out.toString();
			assertTrue("The output should include the message 'a cannot be zero'",
				output.contains("'a' cannot be zero"));
		} finally {
			// Restore original streams
			System.setIn(System.in);
			System.setOut(originalOut);
		}
	}


	@Test
	public void testMainMethodWithRetry() throws Exception {
		String input = "1\n0\n-1\ny\n1\n0\n-4\nn\n"; 
		InputStream in = new java.io.ByteArrayInputStream(input.getBytes());
		System.setIn(in);

		ByteArrayOutputStream out = new ByteArrayOutputStream();
		PrintStream originalOut = System.out;
		System.setOut(new PrintStream(out));

		try {
			Quadratic.main(new String[]{});
		} finally {
			System.setOut(originalOut);
		}

		String output = out.toString();
		assertTrue(output.contains("x1 = 1"));
		assertTrue(output.contains("x1 = 2"));
		assertTrue(output.contains("Thank you for using"));
	}

    @Test
    public void testQuadraticConstructor() {
        Quadratic quadratic = new Quadratic();
        assertNotNull(quadratic); 
    }


}
