/* This file has been extracted from module Recursive. */
import java.util.List;
import java.util.ArrayList;
public class Recursive {

  
  
  public static int countTrueRec(List<Boolean> l, int i) {
    int eX = i + 1;
    try {
      if (i >= (l.size())) {
        return 0;
      } else if (l.get(i)) {
        return 1 + Recursive.countTrueRec(l, eX);
      } else {
        return Recursive.countTrueRec(l, eX);
      }
      
    } catch (IndexOutOfBoundsException eX1) {
      throw new RuntimeException("unreachable statement");
    }
  }
  
  public static int countTrue(List<Boolean> l) {
    
    return Recursive.countTrueRec(l, 0);
  }
  
  
}
