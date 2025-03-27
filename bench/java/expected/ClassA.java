/* This file has been extracted from module ClassA. */
public class ClassA {

  public int a;
  public boolean b;
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
    
    ClassA other = (ClassA) obj;
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
    hashValue = 31 * hashValue + (this.b ? 1 : 0);
    return hashValue;
  }
  
  
}
