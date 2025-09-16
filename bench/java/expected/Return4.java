/* This file has been extracted from module Return4. */
public class Return4 {

  public int a;
  public int b;
  public final boolean equals(Object obj) {
    
    if (this == obj) {
      return true;
    }
    if (obj == null) {
      return false;
    }
    if (!(this.getClass() == obj.getClass())) {
      return false;
    }
    
    Return4 other = (Return4) obj;
    if (!(this.a == other.a)) {
      return false;
    }
    if (!(this.b == other.b)) {
      return false;
    }
    return true;
    
  }
  public final int hashCode() {
    int hashValue = 1;
    hashValue = 31 * hashValue + this.a;
    hashValue = 31 * hashValue + this.b;
    return hashValue;
  }
  
  public static void g(int us, int us1) {
    
    /* nop */
  }
  
  public void f(int i, int j) {
    boolean b = i < j;
    if (b) {
      return;
    }
    Return4.g(j, i);
  }
  
  
}
