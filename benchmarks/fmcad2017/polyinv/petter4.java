package polyinv;

import quantitative.Analyze;

/*
 * Sum of the first natural integers
 */
public class petter4 {

  private static int[] processArg(String[] args) {
    int[] arg = new int[args.length];
    if (args.length > 0) {
      try {
        int firstArg  = Integer.parseInt(args[0]);
        arg[0]        = firstArg;
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
    int k, x, y;
    int[] tmp = processArg(args);
    k = tmp[0];
    x = 0;
    y = 0;

    while( y != k )
       {
       y = y + 1;
       x = x + y*y*y*y;
       }
      System.out.format("Sum of the %d first fourth power of natural integers = %d\n", k, x);
  }
}
