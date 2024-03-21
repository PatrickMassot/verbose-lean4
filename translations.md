# Translating to other languages

Verbose Lean currently has a French version and an English version. 
It is hopefully easy (but a bit tedious) to add more languages in separate libraries
(I do not wish to maintain versions in languages I don’t understand so I would
not merge pull requests proposing this).

You only need to copy the content of the `English` folder from this repository
and replace the English words.
In case of doubt about what needs to be done, you can look at differences
between the French and English folders.

In order to show the kind of work that is involved, here are some examples.
The easiest parts are functions like:
```lean
def describeHypShape (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "The assumption {hyp} has shape “{headDescr}”"

def describeHypStart (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "The assumption {hyp} starts with “{headDescr}”"


implement_endpoint (lang := en) helpExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term we get $nameS:ident such that ($ineqIdent : $ineqS) and ($hS : $pS))
  pushComment <| libres [nameS, ineqIdent, hS]
```
whose French version is
```lean
def describeHypShape (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "L'hypothèse {hyp} est de la forme « {headDescr} »"

def describeHypStart (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "L'hypothèse {hyp} commence par « {headDescr} »"

implement_endpoint (lang := fr) helpExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term on obtient $nameS:ident tel que ($ineqIdent : $ineqS) et ($hS : $pS))
  pushComment <| libres [nameS, ineqIdent, hS]

```
Sometimes the surrounding Lean code looks a bit more intimidating, but the same
principle applies: look for English words that seem to be user-facing, and
compare with the French version to make sure. 
For instance, in the English version of a file we see:
```lean
declare_syntax_cat maybeApplied
syntax term : maybeApplied
syntax term "applied to " term : maybeApplied
syntax term "applied to " term " using " term : maybeApplied
syntax term "applied to " term " using that " term : maybeApplied

def maybeAppliedToTerm : TSyntax `maybeApplied → MetaM (TSyntax `term)
| `(maybeApplied| $e:term) => pure e
| `(maybeApplied| $e:term applied to $x:term) => `($e $x)
| `(maybeApplied| $e:term applied to $x:term using $y) => `($e $x $y)
| `(maybeApplied| $e:term applied to $x:term using that $y) => 
    `($e $x (strongAssumption% $y))
| _ => pure default 

elab "We" " conclude by " e:maybeApplied : tactic => do
  concludeTac (← maybeAppliedToTerm e)
```
and the corresponding French code is:
```lean
declare_syntax_cat maybeAppliedFR
syntax term : maybeAppliedFR
syntax term "appliqué à " term : maybeAppliedFR
syntax term "appliqué à " term " en utilisant " term : maybeAppliedFR
syntax term "appliqué à " term " en utilisant que " term : maybeAppliedFR

def maybeAppliedFRToTerm : TSyntax `maybeAppliedFR → MetaM Term
| `(maybeAppliedFR| $e:term) => pure e
| `(maybeAppliedFR| $e:term appliqué à $x:term) => `($e $x)
| `(maybeAppliedFR| $e:term appliqué à $x:term en utilisant $y) => `($e $x $y)
| `(maybeAppliedFR| $e:term appliqué à $x:term en utilisant que $y) => 
    `($e $x (strongAssumption% $y))
| _ => pure default 

elab "On" " conclut par " e:maybeAppliedFR : tactic => do
  concludeTac (← maybeAppliedFRToTerm e)
```
A note about names: the reason why the syntax category name
`maybeApplied` is translated although it is not user facing is that it is more
convenient as a library developer to be able to import both languages at the
same time. 
If you create your own translation this is less crucial. But I still recommend
doing this because you never know whether you’ll want to create a multilingual
document some day.
