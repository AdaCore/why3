import org.why3.majority.Candidate;
import org.why3.majority.Mjrty;

public class MjrtyTest {

	public static class Candidate implements org.why3.majority.Candidate {		
		public boolean equals(org.why3.majority.Candidate other) {
			return this == other;
		}
	}

	static void majority(Candidate c, Candidate[] arr) {
		assert(c.equals(Mjrty.mjrty(arr)));
	}

	static void no_majority(Candidate[] arr) {
		try {
			Mjrty.mjrty(arr);
			assert(false);
		} catch(org.why3.majority.MjrtyNotFoundException e) {			
		}
	}

	public static void main(String[] args) {
		Candidate A = new Candidate();
		Candidate B = new Candidate();
		Candidate C = new Candidate();
		
		assert(A.equals(A));
		assert(!A.equals(B));				
		assert(!A.equals(C));				
		assert(!B.equals(C));				

		majority(A, new Candidate[] { A, A });		
		majority(A, new Candidate[] { A, A, A });
		no_majority(new Candidate[] { A, A, A, C, C, B, B });
		no_majority(new Candidate[] { A, A, A, C, C, B, B, C, C, C });
		majority(C, new Candidate[] { A, A, A, C, C, B, B, C, C, C, B, C, C	});		
		no_majority(new Candidate[] { A, A, A, B, B, B, C });		
	}
}