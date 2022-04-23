theory MyList
imports Main
begin

datatype 'a list = Nil | Cons 'a "'a list"

fun app ::  "'a list => 'a list => 'a list" where
   "app Nil ys = ys"
 | "app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list => 'a list" where
   "rev Nil = Nil"
 | "rev (Cons x xs) = app (rev xs) (Cons x Nil)"

fun mycount :: "'a list \<Rightarrow> nat" where
   "mycount Nil = 0"
 | "mycount (Cons x xs) = Suc (mycount xs)"

fun myremove :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
   "myremove x Nil = Nil"
 | "myremove x (Cons y xs) =
    (if x=y
      then (myremove x xs)
      else (Cons y (myremove x xs)))"

fun mydedup :: "'a list \<Rightarrow> 'a list" where
   "mydedup Nil = Nil"
 | "mydedup (Cons x xs) = Cons x (myremove x (mydedup xs))"

fun myiindex :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
   "myiindex x Nil = 1"
 | "myiindex x (Cons y xs) =
    (if x=y
      then 0
      else (1 + (myiindex x xs)))"

fun myhas :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
   "myhas x Nil = False"
 | "myhas x (Cons y xs) =
    (if x=y
      then True
      else (myhas x xs))"

fun mycindex :: "'a \<Rightarrow> 'a list \<Rightarrow> int" where
   "mycindex x xs =
    (if (myhas x xs)
      then int (myiindex x xs)
      else -1::int)"

fun myindex :: "'a \<Rightarrow> 'a list \<Rightarrow> int option" where
  "myindex x xs =
    (if (myhas x xs)
      then Some (int (myiindex x xs))
      else None)"

value "rev (Cons True (Cons False Nil))"

(* a comment *)

lemma app_Nil2 [simp]: "app xs Nil = xs"
  apply (induction xs)
  apply (auto)
done

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  apply (induction xs)
  apply (auto)
done

lemma rev_app [simp]: "rev (app xs ys) = app (rev ys) (rev xs)"
  apply (induction xs)
  apply (auto)
done

theorem rev_rev [simp]: "rev (rev xs) = xs"
  apply (induction xs)
  apply (auto)
done

theorem app_count [simp]: "mycount (app xs ys) = (mycount xs) + (mycount ys)"
  apply (induction xs)
  apply (auto)
done

theorem rev_count [simp]: "mycount (rev xs) = mycount xs"
  apply (induction xs)
  apply (auto)
done

theorem remove_idempotence [simp]: "myremove x (myremove x xs) = myremove x xs"
  apply (induction xs)
  apply (auto)
done

lemma remove_count_limit [simp]: "mycount (myremove x xs) \<le> mycount xs"
  apply (induction xs)
  apply (auto)
done

lemma remove_count_required [simp]: "mycount (myremove x (Cons x xs)) < mycount (Cons x xs)"
  apply (induction xs)
  apply (auto)
done

lemma remove_distributivity [simp]: "myremove x (myremove y xs) = myremove y (myremove x xs)"
  apply (induction xs)
  apply (auto)
done

lemma dedup_remove_distributivity [simp]: "mydedup (myremove x xs) = myremove x (mydedup xs)"
  apply (induction xs)
  apply (auto)
done

theorem dedup_idempotence [simp]: "mydedup (mydedup xs) = mydedup xs"
  apply (induction xs)
  apply (auto)
done

theorem dedup_count_limit [simp]: "mycount (mydedup xs) \<le> mycount xs"
  apply (induction xs)
  apply (auto)
by (meson dual_order.trans remove_count_limit)

theorem dedup_count_nonzero [simp]: "(mycount xs > 0) = (mycount (mydedup xs) > 0)"
  apply (induction xs)
  apply (auto)
done

theorem iindex_post_remove [simp]: "myiindex x (myremove x xs) = (mycount (myremove x xs)) + 1"
  apply (induction xs)
  apply (auto)
done

theorem remove_other [simp]: "x \<noteq> y \<longrightarrow> myremove x (Cons y xs) = Cons y (myremove x xs)"
  apply (induction xs)
  apply (auto)
done

lemma iindex_remove_limit [simp]: "x \<noteq> y \<longrightarrow> myiindex x (myremove y xs) \<le> myiindex x xs"
  apply (induction xs)
  apply (auto)
done

lemma iindex_dedup_limit [simp]: "myiindex x (mydedup xs) \<le> myiindex x xs"
  apply (induction xs)
  apply (auto)
by (meson dual_order.trans iindex_remove_limit)

lemma remove_other_still_has [simp]: "x \<noteq> y \<longrightarrow> myhas x (myremove y xs) = myhas x xs"
  apply (induction xs)
  apply (auto)
done


theorem dedup_no_remove [simp]: "(myhas x (mydedup xs)) = (myhas x xs)"
  apply (induction xs)
  apply (auto)
done

theorem cindex_dedup_limit [simp]: "mycindex x (mydedup xs) \<le> mycindex x xs"
  apply (induction xs)
  apply (auto)
by (meson dual_order.trans iindex_dedup_limit iindex_remove_limit)


theorem index_dedup_limit [simp]: "the (myindex x (mydedup xs)) \<le> the (myindex x xs)"
  apply (induction xs)
  apply (auto)
by (meson dual_order.trans iindex_dedup_limit iindex_remove_limit)

end
