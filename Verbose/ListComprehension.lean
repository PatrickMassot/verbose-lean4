/-
This code by Kyle Miller has nothing to do with this project, but came up on
Zulip and I don't want to loose it

https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/List.20Functor/near/290456697
-/

declare_syntax_cat compClause
syntax "for " term " in " term : compClause
syntax "if " term : compClause
syntax "Δ" compClause : compClause

syntax "[" term " | " compClause,* "]" : term

macro_rules
  | `([$t:term |]) => `([$t])
  | `([$t:term | for $x in $xs]) => `(List.map (λ $x => $t) $xs)
  | `([$t:term | if $x]) => `(if $x then [$t] else [])
  | `([$t:term | $c, $cs,*]) => `(List.join [[$t | $cs,*] | $c])

def List.diag (xss : List (List α)) : List α :=
  match xss with
  | [] => []
  | []::_ => []
  | (x::_)::xss => x :: List.diag (List.map (· |>.tailD []) xss)
termination_by _ => xss.length

macro_rules
  | `([$t:term |]) => `([$t])
  | `([$t:term | for $x in $xs]) => `(List.map (λ $x => $t) $xs)
  | `([$t:term | if $x]) => `(if $x then [$t] else [])
  | `([$t:term | Δ $c, $cs,*]) => `(List.diag [[$t | $cs,*] | $c]) -- warning, inefficient
  | `([$t:term | $c, $cs,*]) => `(List.join [[$t | $cs,*] | $c])

#eval [x+1| for x in [1,2,3]]
-- [2, 3, 4]
#eval [4 | if 1 < 0]
-- []
#eval [4 | if 1 < 3]
-- [4]
#eval [(x, y) | for x in List.range 5, for y in List.range 5, if x + y <= 3]
-- [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (3, 0)]

def List.prod (xs : List α) (ys : List β) : List (α × β) :=
  [(x, y) | for x in xs, for y in ys]

#eval [x * y | for (x, y) in List.prod (List.range 3) (List.range 3)]
-- [0, 0, 0, 0, 1, 2, 0, 2, 4]

def List.zip' (xs : List α) (ys : List β) : List (α × β) :=
  [(x, y) | Δ for x in xs, for y in ys]
  -- Delta temporarily switches to using the diagonal monad instead of the usual list monad

#eval List.zip' [1,2,3] [4,5,6,7]
-- [(1, 4), (2, 5), (3, 6)]
