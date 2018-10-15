// from http://web.mit.edu/6.005/www/fa14/classes/09-af-ri-equality/
public class RatNum {
    private final int numer;
    private final int denom;

    // Rep invariant:
    //   denom > 0
    //   numer/denom is in reduced form
    // Check that the rep invariant is true
    // *** Warning: this does nothing unless you turn on assertion checking
    // by passing -enableassertions or -ea to Java
    private void checkRep() {
        assert denom > 0;
        assert gcd(numer, denom) == 1;
    }

    // Abstraction Function:
    //   represents the rational number numer / denom

    /** Make a new Ratnum == n. */
    public RatNum(int n) {
        numer = n;
        denom = 1;
        checkRep();
    }

    /**
     * Make a new RatNum == (n / d).
     * @param n numerator
     * @param d denominator
     * @throws ArithmeticException if d == 0
     */
    public RatNum(int n, int d) throws ArithmeticException {
        // reduce ratio to lowest terms
        int g = gcd(n, d);
        n = n / g;
        d = d / g;

        // make denominator positive
        if (d < 0) {
            numer = -n;
            denom = -d;
        } else {
            numer = n;
            denom = d;
        }
        checkRep();
    }

    public String toString() {
        checkRep();
        if (denom == 1)
            return Integer.toString(numer);
        else
            return Integer.toString(numer)+"/"+Integer.toString(denom);
    }

    private int gcd(int a, int b) { return b==0 ? a : gcd(b, a%b); }

    public static void main(String[] args) {
        RatNum r1 = new RatNum(6, 3);
        System.out.println("6/3 is "+r1);

        RatNum r2 = new RatNum(6, 4);
        System.out.println("6/4 is "+r2);
    }
}
