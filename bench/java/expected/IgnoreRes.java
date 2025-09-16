/* This file has been extracted from module IgnoreRes. */
public abstract class IgnoreRes {

  public boolean x;
  public boolean d;
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
    
    IgnoreRes other = (IgnoreRes) obj;
    if (!(this.x == other.x)) {
      return false;
    }
    if (!(this.d == other.d)) {
      return false;
    }
    return true;
    
  }
  public final int hashCode() {
    int hashValue = 1;
    hashValue = 31 * hashValue + (this.x ? 1 : 0);
    hashValue = 31 * hashValue + (this.d ? 1 : 0);
    return hashValue;
  }
  
  public abstract boolean f();
  
  public void g() {
    
    this.f();
  }
  
  
}
