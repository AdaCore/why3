/* This file has been extracted from module Print. */
import java.io.PrintStream;
import java.util.Arrays;

public class Print {

  public static void printArray(PrintStream o, String prefix, int [] values,
                                int iBegin, int iEnd) {
    
    o.print(prefix);
    o.print("[");
    
    int o1 = iEnd - 1;
    for (int i = iBegin; i <= o1; i++) {
      
      String fmt;
      if (!(i == iBegin)) {
        fmt = ", %d";
      } else {
        fmt = "%d";
      }
      o.print((String.format(fmt, values[i])));
      
    }
    o.print("]");
    
  }
  
  public static void main(String [] us) {
    int [] a = new int[5];
    for (int i = 0; i <= 5 - 1; i++) {
      a[i] = 0;
    }
    for (int i1 = 0; i1 <= (a.length) - 1; i1++) {
      a[i1] = (a.length) - i1;
    }
    Print.printArray(System.out, "a = ", a, 0, (a.length));
    System.out.println();
  }
  
  
}
