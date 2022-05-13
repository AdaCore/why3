/* This file has been extracted from module AllAreZeros. */
import java.util.Arrays;

public class AllAreZeros {

  public static boolean allZeros1(int [] t) {
    int i = 0;
    while (i < (t.length)) {
      if (!(t[i] == 0)) {
        return false;
      }
      i = i + 1;
    }
    return true;
  }
  
  public static boolean allZeros2(int [] t) {
    
    for (int i = 0; i <= (t.length) - 1; i++) {
      if (!(t[i] == 0)) {
        return false;
      }
    }
    return true;
  }
  
  public static boolean allZeros3(int [] t) {
    boolean res = true;
    int i = 0;
    while (i < (t.length)) {
      if (!(t[i] == 0)) {
        res = false;
      }
      i = i + 1;
    }
    if (!AllAreZeros.allZeros2(t)) {
      return !res;
    }
    return res;
  }
  
  public static boolean allZeros4(int [] t) {
    int nzi = -1;
    int i = 0;
    while (i < (t.length) && nzi == -1) {
      if (!(t[i] == 0)) {
        nzi = i;
      }
      i = i + 1;
    }
    return nzi == -1;
  }
  
  private static boolean allZeros5Rec(int [] t, int i) {
    
    if (i == (t.length)) {
      return true;
    }
    if (!(t[i] == 0)) {
      return false;
    }
    return AllAreZeros.allZeros5Rec(t, i + 1);
  }
  
  public static boolean allZeros5(int [] t) {
    
    return AllAreZeros.allZeros5Rec(t, 0);
  }
  
  
}
