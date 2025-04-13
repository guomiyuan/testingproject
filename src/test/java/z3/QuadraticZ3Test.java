import org.junit.Test;  

import static org.junit.Assert.*;

public class QuadraticZ3Test {

    private void assertQuadratic(double a, double b, double c) {
        System.out.println("[OK] Running test: a=" + a + ", b=" + b + ", c=" + c);
        try {
            if (a == 0) {
                try {
                    Quadratic.solveQuadratic(a, b, c);
                    fail("Expected exception for a=0");
                } catch (Quadratic.NotEnoughPrecisionException e) {
                    System.out.println("Expected exception: " + e.getMessage());
                } catch (Exception e) {
                    fail("Unexpected exception for a=0: " + e);
                }
            } else {
                Quadratic.solveQuadratic(a, b, c);
                double discriminant = b * b - 4 * a * c;

                if (Double.isNaN(discriminant) || discriminant == b * b) {
                    fail("Discriminant overflow/underflow not handled");
                }
            }
        } catch (Quadratic.NotEnoughPrecisionException e) {
            System.out.println("Expected precision loss: " + e.getMessage());
        } catch (Throwable t) {
            fail("Unexpected error: " + t);
        }
    }

    @Test public void testTwoRealRoots() { assertQuadratic(1.0, 2.0, 1.0 / 2.0); }
    @Test public void testRepeatedRealRoot() { assertQuadratic(1.0, 1.0, 1.0 / 4.0); }
    @Test public void testComplexRoots() { assertQuadratic(-1.0, 1.0, -2.0); }
    @Test public void testSmallAValuePositive() { assertQuadratic(11.0 / 20000000000.0, 2.0, 0.0); }
    @Test public void testSmallAValueNegative() { assertQuadratic(-11.0 / 20000000000.0, 2.0, 0.0); }
    @Test public void testLargeACoefficient() { assertQuadratic(100000000000000000001.0, 0.0, 0.0); }
    @Test public void testLargeBCoefficient() { assertQuadratic(0.0, 100000000000000000001.0, 0.0); }
    @Test public void testLargeBDiscriminant() { assertQuadratic(1.0 / 10000.0, 100000000000001.0 / 10000.0, -1.0 / 10000.0); }
    @Test public void testSmallACDiscriminant() { assertQuadratic(-1.0 / 10000000000.0, 10000000001.0 / 10000000000.0, 1.0 / 10000000000.0); }
    @Test public void testFractionalCoefficients() { assertQuadratic(11.0 / 20.0, 9.0 / 20.0, 9.0 / 20.0); }
    @Test public void testNearZeroDiscriminant() { assertQuadratic(0.0, -999999.0 / 20000000000.0, 0.0); }
    @Test public void testFloatingPointPrecision() { assertQuadratic(1.0 / 1073741824.0, 1.0 / 1048576.0, 1.0 / 1048576.0); }
    @Test public void testSpecialComboA1B0() { assertQuadratic(1.0, 0.0, 2.0); }
    @Test public void testDenormalizedNumbers() { assertQuadratic(0.0, 1.00000000000000000001, 0.0); }
    @Test public void testApproximateInteger() { assertQuadratic(0.0, 1.0000000001, 0.0); }
    @Test public void testRandomCombo() { assertQuadratic(10000000001.0 / 10000000000.0, 262050000000001.0 / 10000000000.0, 248170000000001.0 / 10000000000.0); }
}