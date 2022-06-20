theory Exercise2
  imports Main
begin

lemma "
  (\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs)
\<or> (\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs + 1)
" (is "?EVEN \<or> ?ODD")
proof cases
  assume "2 dvd (length xs)"
  then obtain k
    where even_xs: "length xs = 2*k"
    by auto
  then obtain ys zs
    where ys_def: "ys = take k xs"
      and zs_def: "zs = drop k xs"
    by simp
  hence xs_part: "xs = ys @ zs" by simp
  have "length zs = k"
    using even_xs zs_def
    by simp
  hence ?EVEN using xs_part even_xs by auto
  thus ?thesis by simp
next
  assume "\<not> (2 dvd (length xs))"
  hence "\<exists>k. length xs = (2*k) + 1" by arith
  then obtain k
    where odd_xs: "length xs = (2*k) + 1"
    by auto
  then obtain ys zs
    where ys_def: "ys = take (k+1) xs"
      and zs_def: "zs = drop (k+1) xs"
    by simp
  hence xs_part: "xs = ys @ zs" by simp
  hence "length zs = k"
    using odd_xs zs_def
    by simp
  hence ?ODD using xs_part odd_xs by auto
  thus ?thesis by simp
qed

end
