/* This file has been extracted from module IfThenElse. */
public class IfThenElse {

  public static int testIte(boolean b0, boolean b1) {
    int x;
    if (b0) {
      if (b1) {
        x = 2;
      } else {
        x = 0;
      }
    } else if (b1) {
      x = 3;
    } else {
      x = 1;
    }
    
    return 2 * x;
  }
  
  
}
