package polyinv;

import quantitative.Analyze;

public class euclidex {

/* extended Euclid's algorithm */

  private static int[] processArg(String[] args) {
    int[] arg = new int[args.length];
    if (args.length > 0) {
      try {
        int firstArg  = Integer.parseInt(args[0]);
        int secondArg = Integer.parseInt(args[1]);
        arg[0]        = firstArg;
        arg[1]        = secondArg ;
        return arg;
      } catch (ArrayIndexOutOfBoundsException e) {
        System.err.println("Not enough arguments.");
        System.exit(1);
      } catch (NumberFormatException e) {
        System.err.println("Argument must be an integer.");
        System.exit(1);
      }
    } else {
      System.err.println("Missing argument: provide an integer bounding loop iterations.");
      System.exit(1);
    }
    // Non-reachable
    return arg;
  }
  
  @Analyze 
  public static void main(String[] args) {
    int x, y, a, b, p, q, r, s;
    int[] tmp = processArg(args);
    x = tmp[0];
    y = tmp[1];  
    a = x;
    b = y;
    p = 1;
    q = 0;
    r = 0;
    s = 1;
    while (a != b) {
   	if (a>b) {a = a-b; p = p-q; r=r-s;}

        else {b = b-a; q = q-p; s = s-r;}
      }
      System.out.format("a = %d" , a);
    }
}