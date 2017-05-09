package polyinv;

import quantitative.Analyze;


/* Wensley's algorithm for real division */
 
public class wensley {

  private static float[] processArg(String[] args) {
    float[] arg = new float[args.length];
    if (args.length > 0) {
      try {
        float firstArg  = Float.parseFloat(args[0]);
	float secondArg = Float.parseFloat(args[1]);
	float thirdArg = Float.parseFloat(args[2]);
        arg[0]        = firstArg;
	arg[1]	      = secondArg;
	arg[2]	      = thirdArg;
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
     float a,b,d,y,P,Q,E;
     float[] tmp = processArg(args);
     P=tmp[0];
     Q=tmp[1];
     E=tmp[2];
     a=0;
     b=Q/2;
     d=1;
     y=0;

     while( d>= E)
         {
         if (P< a+b)
             {
             b=b/2;
             d=d/2;
             }
         else
             {
             a=a+b;
             y=y+d/2;
             b=b/2;
             d=d/2;
             }
         }
    System.out.format("y = %f \n", y);
    }
}
