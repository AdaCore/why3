theory PGCD_PGCD_gcd_a_b_1
imports Why3
begin

why3_open "PGCD_PGCD_gcd_a_b_1.xml"

why3_vc gcd_a_b
proof -
  from assms have "common_div (a-b) b k" using is_gcd_def by simp
  then have 1: "common_div a b k" using common_div_a_b by simp
  (* show that any other common divisor of a and b divides k *)
  { fix p
    assume h: "common_div a b p"
    hence "\<exists>ka kb::int. (a = ka * p) \<and> (b = kb * p)" using common_div_def and divides_def by simp
    then obtain ka kb where "a = ka * p" and "b = kb * p" by auto
    hence "a - b = (ka - kb) * p" using int_distrib by simp
    hence "divides p (a-b)"  using divides_def by simp
    hence "common_div (a-b) b p" using h and common_div_def by simp
    hence "divides p k" using assms and is_gcd_def by simp
  }
  hence "\<forall>p::int. common_div a b p \<longrightarrow> divides p k" by simp
  thus "is_gcd a b k" using 1 and is_gcd_def by simp
qed

why3_end

end
