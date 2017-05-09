package polyinv;

import quantitative.Analyze;

/* binary division algorithm, by Kaldewaij */

public class divbin {

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
    int A, B, q, r, b;
    int[] tmp = processArg(args);
    A = tmp[0];
    B = tmp[1];
    q = 0;
    r = A;
    b = B;

    while (b != B) {
	 q=2*q;
         b=b/2;
         if (r >= b)
             {
             q=q+1;
             r=r-b;
             }
      }
      System.out.format("r = %d" , r);
    }
}
