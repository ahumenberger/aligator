package polyinv;

import quantitative.Analyze;

public class cohencu {

/* Programm printing the N first consecutive cubes*/

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
    int x, y, z, n;
    int[] tmp = processArg(args);
    n = 0;
    x = 0;
    y = 1;
    z = 6;
    while (n <= 0) {
         n=n+1;
         x=x+y;
         y=y+z;
         z=z+6;
      }
    }
}
