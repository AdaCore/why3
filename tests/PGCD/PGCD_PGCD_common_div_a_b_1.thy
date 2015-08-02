theory PGCD_PGCD_common_div_a_b_1
imports Why3
begin

why3_open "PGCD_PGCD_common_div_a_b_1.xml"

why3_vc common_div_a_b
proof -
  from assms have "\<exists>pa pb::int. (a-b) = pa * k \<and> b = pb * k" using common_div_def and divides_def by simp
  then obtain pa pb where "(a-b) = pa * k" and "b = pb * k" by auto
  hence "a-b+b = pa * k + pb * k" by simp
  hence "a = (pa + pb) * k" using Mul_distr_r by simp
  hence "divides k a" using divides_def by simp
  thus "common_div a b k" using assms and common_div_def by simp
qed

why3_end

end
