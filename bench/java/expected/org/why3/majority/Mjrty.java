/* This file has been extracted from module Mjrty. */
package org.why3.majority;

import java.util.Arrays;

import org.why3.majority.MjrtyNotFoundException;
import org.why3.majority.Candidate;

public class Mjrty {

  public static Candidate mjrty(Candidate [] a) throws MjrtyNotFoundException {
    int n = (a.length);
    Candidate cand = a[0];
    long k = 0;
    for (int i = 0; i <= n - 1; i++) {
      if (k == 0) {
        cand = a[i];
        k = 1;
      } else if ((cand).equals(a[i])) {
        k = k + 1;
      } else {
        k = k - 1;
      }
      
    }
    if (k == 0) {
      throw new MjrtyNotFoundException ();
    }
    if (2 * k > (Long.valueOf(n))) {
      return cand;
    }
    k = 0;
    for (int i1 = 0; i1 <= n - 1; i1++) {
      if (a[i1].equals(cand)) {
        k = k + 1;
        if (2 * k > (Long.valueOf(n))) {
          return cand;
        }
      }
    }
    throw new MjrtyNotFoundException ();
  }
  
  
}
