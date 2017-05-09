package polyinv;

import quantitative.Analyze;


// algorithm for finding the closest integer to the square root, from  www.pedrofreire.com/crea2_en.htm?*/
 
public class freire1 {

  private static float[] processArg(String[] args) {
    float[] arg = new float[args.length];
    if (args.length > 0) {
      try {
        float firstArg  = Float.parseFloat(args[0]);
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
    float a, x;
    float r;
    float[] tmp = processArg(args);
    a = tmp[0];
    x = a/2;
    r = 0;
    while (x > r) {
	x = x-r;
	r = r+1;
      }
    System.out.format("r = %f \n", r);
    }
}



