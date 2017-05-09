package polyinv;

import quantitative.Analyze;

/* algorithm for computing simultaneously the GCD and the LCM, by Sankaranarayanan */

public class lcm {

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
		int a, b, x,y,u,v;
		int[] tmp = processArg(args);
		a = tmp[0];
		b = tmp[1];
		x = a;
		y = b;
		u = b;
		v = 0;
		while (x != y) {

			// inv( GCD(x,y) == GCD(a,b) && x*u + y*v == a*b );
			while (x>y)
			{
				x=x-y;
				v=v+u;
			}

			//inv( GCD(x,y) == GCD(a,b) && x*u + y*v == a*b );
			while (x<y)
			{
				y=y-x;
				u=u+v;
			}
		}
	}
}
