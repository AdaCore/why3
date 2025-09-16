/* This file has been extracted from module ForLoop. */
import java.util.Arrays;

public class ForLoop {

  public static boolean allEqualTo(int [] a, int x) {
    
    for (int i = 0; i <= (a.length) - 1; i++) {
      if (!(a[i] == x)) {
        return false;
      }
    }
    return true;
  }
  
  
}
