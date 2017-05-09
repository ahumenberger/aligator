package polyinv;

import quantitative.Analyze;

public class fermat {

/* program computing a divisor for factorisation, by Bressoud */

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
    int N, R, u, v, r;
    int[] tmp = processArg(args);

    N = tmp[0];
    R = tmp[1];
    u = 2*R+1;
    v = 1;
    r = R*R-N;
	while (r!=0)
         {
     	    if (r>0)
             {
             r=r-v;
             v=v+2;
             }
 	    else
             {
             r=r+u;
             u=u+2;
             }
         }
	System.out.format("%d", u);
    }
}
