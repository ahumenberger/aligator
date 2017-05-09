package polyinv;

import quantitative.Analyze;

/*
 * Example taken from Knuth's "The Art of Computer Programming, Volume 2".
 */
public class knuth {

  @Analyze
  public static void main(String[] args) {
    int n, d, r, rp, q, t, n1, n2;
    double s;
    n  = Integer.parseInt(args[0]);
    d  = Integer.parseInt(args[1]);
    n1 = n/d;       // Integer division
    n2 = n/(d-2);   // Integer division
    r  = n - n1 * d;
    rp = n - n2 * (d-2);
    q  = 4 * (n2 - n1);
    s  = Math.sqrt(n);

    while ((s >= d) && (r != 0)) {
      if (2*r-rp+q < 0) {
        t  = r;
        r  = 2*r-rp+q+d+2;
        rp = t;
        q  = q+4;
        d  = d+2;
      } else if ((2*r-rp+q >= 0) && (2*r-rp+q < d+2))  {
        t  = r;
        r  = 2*r-rp+q;
        rp = t;
        d  = d+2;
      } else if ((2*r-rp+q >= 0) && (2*r-rp+q >= d+2) && (2*r-rp+q < 2*d+4)) {
        t  = r;
        r  = 2*r-rp+q-d-2;
        rp = t;
        q  = q-4;
        d  = d+2;
      } else { /* ((2*r-rp+q >= 0) && (2*r-rp+q >= 2*d+4)) */
        t  = r;
        r  = 2*r-rp+q-2*d-4;
        rp = t;
        q  = q-8;
        d  = d+2;
      }
      System.out.format("n = %d, d = %d\nr = %d, rp = %d, q = %d, s = %f, t = %d, n1 = %d, n2 = %d\n", n, d, r, rp, q, s, t, n1, n2);
    }
    System.out.format("Result: d = %d\n", d);
  }
}

/*
        0: notnull args:O
        1: checkbound args:O[0]
        2: mayinit java.lang.Integer
        3: n := java.lang.Integer.parseInt(args:O[0]:O)
        4: notnull args:O
        5: checkbound args:O[1]
        6: mayinit java.lang.Integer
        7: d := java.lang.Integer.parseInt(args:O[1]:O)
        8: notzero d:I
        9: n1 := n:I/d:I
       10: notzero d:I-2
       11: n2 := n:I/(d:I-2)
       12: r := n:I-(n1:I*d:I)
       13: rp := n:I-(n2:I*(d:I-2))
       14: q := 4*(n2:I-n1:I)
       15: mayinit java.lang.Math
       16: s := java.lang.Math.sqrt(I2D(n:I))
       17: nop
       18: if (s:D < I2D(d:I)) goto 110
       19: if (r:I == 0) goto 110
       20: if ((((2*r:I)-rp:I)+q:I) >= 0) goto 27
       21: t := r:I
       22: r := ((((2*r:I)-rp:I)+q:I)+d:I)+2
       23: rp := t:I
       24: q := q:I+4
       25: d := d:I+2
       26: goto 48
       27: if ((((2*r:I)-rp:I)+q:I) < 0) goto 34
       28: if ((((2*r:I)-rp:I)+q:I) >= (d:I+2)) goto 34
       29: t := r:I
       30: r := ((2*r:I)-rp:I)+q:I
       31: rp := t:I
       32: d := d:I+2
       33: goto 48
       34: if ((((2*r:I)-rp:I)+q:I) < 0) goto 43
       35: if ((((2*r:I)-rp:I)+q:I) < (d:I+2)) goto 43
       36: if ((((2*r:I)-rp:I)+q:I) >= ((2*d:I)+4)) goto 43
       37: t := r:I
       38: r := ((((2*r:I)-rp:I)+q:I)-d:I)-2
       39: rp := t:I
       40: q := q:I-4
       41: d := d:I+2
       42: goto 48
       43: t := r:I
       44: r := ((((2*r:I)-rp:I)+q:I)-(2*d:I))-4
       45: rp := t:I
       46: q := q:I-8
       47: d := d:I+2
       48: mayinit java.lang.System
       49: $irvar0 := 'n = %d, d = %d\nr = %d, rp = %d, q = %d, s = %f, t = %d, n1 = %d, n2 = %d\n'
       50: checknegsize 9
       51: $irvar1 := new java.lang.Object[9]
       52: $irvar3 := java.lang.System.out
       53: mayinit java.lang.Integer
       54: $irvar2 := java.lang.Integer.valueOf(n:I)
       55: notnull $irvar1:[O
       56: checkbound $irvar1:[O[0]
       57: checkstore $irvar1:[O[] <- $irvar2:O
       58: $irvar1:[O[0] := $irvar2:O
       59: mayinit java.lang.Integer
       60: $irvar4 := java.lang.Integer.valueOf(d:I)
       61: notnull $irvar1:[O
       62: checkbound $irvar1:[O[1]
       63: checkstore $irvar1:[O[] <- $irvar4:O
       64: $irvar1:[O[1] := $irvar4:O
       65: mayinit java.lang.Integer
       66: $irvar4 := java.lang.Integer.valueOf(r:I)
       67: notnull $irvar1:[O
       68: checkbound $irvar1:[O[2]
       69: checkstore $irvar1:[O[] <- $irvar4:O
       70: $irvar1:[O[2] := $irvar4:O
       71: mayinit java.lang.Integer
       72: $irvar4 := java.lang.Integer.valueOf(rp:I)
       73: notnull $irvar1:[O
       74: checkbound $irvar1:[O[3]
       75: checkstore $irvar1:[O[] <- $irvar4:O
       76: $irvar1:[O[3] := $irvar4:O
       77: mayinit java.lang.Integer
       78: $irvar4 := java.lang.Integer.valueOf(q:I)
       79: notnull $irvar1:[O
       80: checkbound $irvar1:[O[4]
       81: checkstore $irvar1:[O[] <- $irvar4:O
       82: $irvar1:[O[4] := $irvar4:O
       83: mayinit java.lang.Double
       84: $irvar4 := java.lang.Double.valueOf(s:D)
       85: notnull $irvar1:[O
       86: checkbound $irvar1:[O[5]
       87: checkstore $irvar1:[O[] <- $irvar4:O
       88: $irvar1:[O[5] := $irvar4:O
       89: mayinit java.lang.Integer
       90: $irvar4 := java.lang.Integer.valueOf(t:I)
       91: notnull $irvar1:[O
       92: checkbound $irvar1:[O[6]
       93: checkstore $irvar1:[O[] <- $irvar4:O
       94: $irvar1:[O[6] := $irvar4:O
       95: mayinit java.lang.Integer
       96: $irvar4 := java.lang.Integer.valueOf(n1:I)
       97: notnull $irvar1:[O
       98: checkbound $irvar1:[O[7]
       99: checkstore $irvar1:[O[] <- $irvar4:O
      100: $irvar1:[O[7] := $irvar4:O
      101: mayinit java.lang.Integer
      102: $irvar4 := java.lang.Integer.valueOf(n2:I)
      103: notnull $irvar1:[O
      104: checkbound $irvar1:[O[8]
      105: checkstore $irvar1:[O[] <- $irvar4:O
      106: $irvar1:[O[8] := $irvar4:O
      107: notnull $irvar3:O
      108: $irvar4 := $irvar3:O.format($irvar0:O,$irvar1:[O)
      109: goto 18
      110: mayinit java.lang.System
      111: $irvar0 := 'Result: d = %d\n'
      112: checknegsize 1
      113: $irvar1 := new java.lang.Object[1]
      114: $irvar3 := java.lang.System.out
      115: mayinit java.lang.Integer
      116: $irvar2 := java.lang.Integer.valueOf(d:I)
      117: notnull $irvar1:[O
      118: checkbound $irvar1:[O[0]
      119: checkstore $irvar1:[O[] <- $irvar2:O
      120: $irvar1:[O[0] := $irvar2:O
      121: notnull $irvar3:O
      122: $irvar4 := $irvar3:O.format($irvar0:O,$irvar1:[O)
      123: return
*/
