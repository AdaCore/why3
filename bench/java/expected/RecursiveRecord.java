/* This file has been extracted from module RecursiveRecord. */
import java.util.NoSuchElementException;
import java.util.Optional;
public class RecursiveRecord {

  public final boolean a;
  public final Optional<RecursiveRecord> next;
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
    
    RecursiveRecord other = (RecursiveRecord) obj;
    if (!(this.a == other.a)) {
      return false;
    }
    if (!(this.next == null ? other.next == null : this.next.equals(other.next))) {
      return false;
    }
    return true;
    
  }
  public final int hashCode() {
    int hashValue = 1;
    hashValue = 31 * hashValue + (this.a ? 1 : 0);
    hashValue = 31 * hashValue + (this.next == null ? 0 : this.next.hashCode());
    return hashValue;
  }
  
  public RecursiveRecord getNext() throws NoSuchElementException {
    
    return this.next.get();
  }
  
  public RecursiveRecord() {
    
    this.a = false;
    this.next = Optional.ofNullable(null);
  }
  
  
}
