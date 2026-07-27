(* Used in Notation.v to test import of notations from files in sections *)

Notation "'Z'" := O (at level 9).
Abbreviation plus := plus.
Abbreviation succ := S.
Abbreviation mult := mult (only parsing).
Abbreviation less := le (only parsing).

(* Test bug 2168: ending section of some name was removing objects of the
   same name *)

Abbreviation add2 n:=(S n).
Section add2.
End add2.
