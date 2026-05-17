theory TRE_Syntax
  imports Interval
begin

datatype 'a tre =
    Empty
  | Epsilon
  | Atom 'a
  | Union "'a tre" "'a tre"
  | Intersection "'a tre" "'a tre"
  | Concat "'a tre" "'a tre"
  | KleeneStar "'a tre"
  | KleenePlus "'a tre"
  | Within "'a tre" interval

end
