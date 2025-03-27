/* This file has been extracted from module Return5. */
import java.util.Arrays;

public class Return5 {

  public static void f(int [] v) {
    
    for (int i = 0; i <= (v.length) - 1; i++) {
      v[i] = i;
    }
  }
  
  public static void h(int [] v) {
    
    for (int i = 0; i <= (v.length) - 1; i++) {
      v[i] = i + 1;
    }
  }
  
  public static void g(int [] v) {
    
    if ((v.length) > 5) {
      Return5.f(v);
      return;
    }
    Return5.h(v);
  }
  
  
}
