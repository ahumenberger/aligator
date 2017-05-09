package polyinv;

import quantitative.Analyze;

/*
 * Example taken from Manna's "Mathematical Theory of Computation".
 */
public class mannadiv {

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
    int x1, x2, y1, y2, y3;
    int[] tmp = processArg(args);
    x1 = tmp[0];
    x2 = tmp[1];
    y1 = 0;
    y2 = 0;
    y3 = x1;
    while (y3 != 0) {
      if (x2 == y2 + 1) {
        y1++;
        y2 = 0;
        y3--;
      } else {
        y2++;
        y3--;
      }
      System.out.format("x1 = %d, x2 = %d\ny1 = %d, y2 = %d, y3 = %d\n", x1, x2, y1, y2, y3);
    }
  }
}

/*
        0: mayinit test.Mannadiv
        1: tmp := test.Mannadiv.processArg(args:O)
        2: notnull tmp:O
        3: checkbound tmp:O[0]
        4: x1 := tmp:O[0]:I
        5: notnull tmp:O
        6: checkbound tmp:O[1]
        7: x2 := tmp:O[1]:I
        8: y1 := 0
        9: y2 := 0
       10: y3 := x1:I
       11: if (y3:I == 0) goto 57
       12: if (x2:I != (y2:I+1)) goto 17
       13: y1 := y1:I+1
       14: y2 := 0
       15: y3 := y3:I+-1
       16: goto 19
       17: y2 := y2:I+1
       18: y3 := y3:I+-1
       19: mayinit java.lang.System
       20: $irvar0 := 'x1 = %d, x2 = %d\ny1 = %d, y2 = %d, y3 = %d'
       21: checknegsize 5
       22: $irvar1 := new java.lang.Object[5]
       23: $irvar3 := java.lang.System.out
       24: mayinit java.lang.Integer
       25: $irvar2 := java.lang.Integer.valueOf(x1:I)
       26: notnull $irvar1:[O
       27: checkbound $irvar1:[O[0]
       28: checkstore $irvar1:[O[] <- $irvar2:O
       29: $irvar1:[O[0] := $irvar2:O
       30: mayinit java.lang.Integer
       31: $irvar4 := java.lang.Integer.valueOf(x2:I)
       32: notnull $irvar1:[O
       33: checkbound $irvar1:[O[1]
       34: checkstore $irvar1:[O[] <- $irvar4:O
       35: $irvar1:[O[1] := $irvar4:O
       36: mayinit java.lang.Integer
       37: $irvar4 := java.lang.Integer.valueOf(y1:I)
       38: notnull $irvar1:[O
       39: checkbound $irvar1:[O[2]
       40: checkstore $irvar1:[O[] <- $irvar4:O
       41: $irvar1:[O[2] := $irvar4:O
       42: mayinit java.lang.Integer
       43: $irvar4 := java.lang.Integer.valueOf(y2:I)
       44: notnull $irvar1:[O
       45: checkbound $irvar1:[O[3]
       46: checkstore $irvar1:[O[] <- $irvar4:O
       47: $irvar1:[O[3] := $irvar4:O
       48: mayinit java.lang.Integer
       49: $irvar4 := java.lang.Integer.valueOf(y3:I)
       50: notnull $irvar1:[O
       51: checkbound $irvar1:[O[4]
       52: checkstore $irvar1:[O[] <- $irvar4:O
       53: $irvar1:[O[4] := $irvar4:O
       54: notnull $irvar3:O
       55: $irvar4 := $irvar3:O.format($irvar0:O,$irvar1:[O)
       56: goto 11
       57: return
*/

