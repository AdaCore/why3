/* This file has been extracted from module Return2. */
public class Return2 {

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
    
    Return2 other = (Return2) obj;
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
  
  public static void g(int us) {
    
    /* nop */
  }
  
  public void f(int i) {
    
    Return2.g(i);
  }
  
  
}
