
import M4R.Algebra

open M4R

#eval (Finset.range 10).length

#eval ∑ x in (Finset.range 10), (3 : Int)
#eval ∏ x in (Finset.range 3), x + 1

#eval ∑ (Finset.range' 3 1)
#eval ∑ (fun x => x.fst * x.snd) in (Finset.antidiagonal 7)
