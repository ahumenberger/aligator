 package polyinv;

import quantitative.Analyze;

public class dijkstra {

/* program computing the floor of the square root, by Dijkstra */

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
    int n, p, q, r, h;
    int[] tmp = processArg(args);
    n = tmp[0];
    p = 0;
    q = 1;		
    r = n;
    //while (q<=n) {q=4*q;}
   while (q!=1)	
       {
       q=q/4;
       h=p+q;
       p=p/2;
       if (r>=h)
           {
           p=p+q;
           r=r-h;
           }	
       }
    System.out.format("p = %d" , p);
  }
}
